# Research notes: input languages, incrementality, and theories

Working notes on where booleanium could go beyond a QDIMACS-in /
verdict-out 2QBF solver. The starting observation: incremental
determinization's core state *is* a set of definitions (the implication
sets are gate semantics), while CNF input forces the encoder to destroy
definitions that the solver then spends its runtime reconstructing.
Everything below is grounded in measurements from this repository (see
`PLAN.md` for the detailed numbers).

## Measured motivation

* The Plaisted–Greenbaum tax is real and quantified: `adder2.qdimacs`
  starts with 209 of 515 variables deterministic and degenerated into
  search until frontier CEGAR; the `stmt` family (38 QBFEVAL'17
  instances) was out of reach until the pure-literal rule. Both fixes
  are, at heart, heuristics that *reconstruct* gate definitions the
  encoding threw away — the pure-literal rule recovers one-sided gates,
  frontier CEGAR recovers the settled/unsettled boundary.
* Gate detection on the backend side failed twice by measurement
  (CryptoMiniSat XOR reasoning, on two encodings of the conflict check).
* The definition-level input prototype (`src/aiger.rs`, QAIGER circuits)
  makes the point directly: `beem.qaig` (18k gates) solves with **zero
  decisions and one conflict** — the circuit arrives fully deterministic
  and only the top-level question is left. All nine QAIGER instances of
  the CADET suite solve in ≤ 0.8s, matching CADET's verdicts, certified.

## RQ1 — Is definition-level input strictly better for ID?

The prototype ingests circuits by emitting two-sided Tseitin clauses, so
determinization *rediscovers* the gates in the initial propagation.
Open questions:

* **Direct pre-determinization — measured, verdict: convenience, not
  speed** (at current scales): on the largest definition-level suite
  instance (`beem.qaig`, 18k gates) the whole run is dominated by
  discovery — zero decisions, one conflict — and completes in ~0.15 s,
  i.e. ~8 µs/gate; a pre-determinization API could save at most that.
  Discovery *can* dominate pathologically (`AR-fixpoint` corpus
  instances spend >30 s before the first fixpoint), but those are
  PG-encoded CNF where no definitions exist to enter, so the API would
  not apply. Revisit only if definition-level instances 100x larger
  than the suite appear.
* **Paired-encoding experiment — run** (`bench_encodings`: the same
  circuit families rendered as (a) QCIR through the definition-level
  frontend, (b) two-sided Tseitin CNF, (c) Plaisted–Greenbaum CNF;
  measured: verdict, time, *initially determinized fraction*
  (`IncDet::initial_deterministic`), decisions, conflicts). The
  prediction (a) ≈ (b) ≪ (c) is **refuted in its general form**; the
  encodings separate *conditionally*:
  - *(a) ≈ (b) always* — the definition-level path is two-sided CNF by
    construction; identical determinization and search on every family
    (the format's value is convenience and losslessness, not a
    separate algorithm).
  - *Output-forced structure*: on trees whose output forces everything
    (parity-equality chains, mux trees), PG loses nothing — unit
    propagation down the forced output re-derives the dropped
    directions; all encodings determinize 100% initially with zero
    decisions, PG slightly leaner.
  - *Irrelevant cones*: on random circuits PG wins **~100x** — gates
    outside the output cone get no clauses and stay unconstrained,
    while (a)/(b) pay decisions and conflicts to determinize junk
    (initial 6–10/50 determinized, then search; PG: solved in
    microseconds).
  - *Choice-blocked structure* (comparison gates over existential
    choice variables under a disjunctive top): initial determinization
    stalls for **all** encodings — a gate whose arguments include an
    unconstrained existential cannot be recognized bottom-up — and PG
    is a mild constant worse (~1.3–1.5x decisions/time).
  The drastic definition-level wins recorded on the wild `stmt`/QAIGER
  instances (PLAN §1) therefore hinge on instance structure the naive
  generators do not produce: deep gates over *universal* inputs, used
  effectively one-sidedly, under tops that force nothing. The
  corpus-wide determinization-fraction metric is now queryable for the
  detection question below.
* **How much does gate *detection* on CNF actually recover? —
  surveyed** (all 384 QBFEVAL'17 2QBF instances, 10 s budget,
  fraction of existentials determinized at the first propagation
  fixpoint vs solve outcome):

  | initially determinized | n | solved |
  |---|---|---|
  | fixpoint not reached in 10 s | 10 | 0% |
  | 0–20% | 182 | 21% |
  | 20–50% | 90 | 40% |
  | 50–80% | 86 | 50% |
  | 80–99% | 15 | 60% |
  | ~100% | 1 | 100% |

  Solved instances recover a median 45% of their existentials up
  front; timeouts a median 6%. Only *one* instance in the corpus
  determinizes fully — on wild CNF encodings, propagation-based
  detection recovers a fraction of the structure, and that fraction
  is a strong monotone predictor of solvability. This settles the
  corpus-wide question against "QDIMACS is fine": the structure ID
  runs on is mostly *not* recoverable from the shipped encodings
  (consistent with the `stmt` observation and with the
  paired-encoding result that one-sidedness hurts exactly when
  neither top-down forcing nor irrelevance rescues it). Caveat on
  causality: instance size confounds — larger instances both
  determinize less and are harder — so the number argues for
  definition-level *inputs*, not for detection being the only
  bottleneck.
* **QCIR frontend — done for the prenex 2QBF slice** (`src/qcir.rs`,
  auto-detected by the CLI via the `#QCIR` header): `and`/`or`/`xor`/
  `ite` gates over cleansed or named identifiers become existential
  variables with two-sided Tseitin definitions — the same
  definition-level path as QAIGER, with richer gates. Prefixes that
  collapse to ∀∃ or a single block solve natively (with certification,
  strategy circuits under the surface names, and QRAT proofs); an ∃∀
  prefix is solved by negation with the verdict inverted (gate
  definitions are self-dual, only the output flips), mirroring the
  SMT-LIB frontend's synthesis mode. Non-prenex quantifier gates and
  deeper prefixes are rejected with clear errors. Validated by a
  differential proptest against direct circuit evaluation (game
  semantics on the circuit itself, independent of the Tseitin
  conversion) in both quantifier orders, 8k cases.

## RQ2 — The incremental interface (the QIPASIR gap)

SAT's success as a *library* (IPASIR: add-clause / assume / solve) is
what made bounded model checking and IC3 practical; QBF never got an
adopted equivalent. For booleanium the natural contract is:

    push / pop / add-clause / add-definition / solve(assumptions)
      -> verdict + Skolem functions valid for the current stack

**Status: the baseline exists** (`src/incremental.rs`): an assertion
stack of frames with `push`/`pop`/`add_clause`/`define_and`/`solve`/
`solve_with_assumptions`, piecewise Skolem model extraction
(`src/incdet/model.rs`, with a pointwise evaluator and SMT-LIB
emission), and *learnt-clause carrying* as the incrementality
mechanism: learnt clauses are resolvents of the matrix they were learnt
under, so they stay valid for every extension; each is tagged with the
stack depth it was learnt at and dropped when that depth pops.
Assumptions are a temporary frame, so assumption-derived clauses are
retracted automatically. Every solve currently rebuilds the core solver
from the stack (plus carried clauses) — correct by construction, and
validated by a differential proptest that runs random
push/pop/add/solve sessions against the brute-force oracle, certifies
every satisfiable answer, and evaluates the extracted model on every
universal point against the matrix. The open work below is about
*performance*, not the contract:

* Decision levels and the guarded conflict-check clauses are already a
  push/pop mechanism (level-tagged implications, per-level assumption
  guards, reboot-from-trail). Universal *assumptions* even exist already
  (case-split machinery assumes universal literals).
* **Root permanence is the landmine.** Large parts of the solver treat
  root-level state as forever: permanent clauses in the conflict check,
  `root_vars` in frontier CEGAR, learnt clauses as globally
  matrix-implied resolvents, recorded CEGAR cases and closed case
  splits as permanently excluded regions. Under pop, "the matrix"
  shrinks: learnt clauses and handled cases derived under popped
  constraints must be retracted. The clean design is to tag *every*
  derived artifact (learnt clause, handled case, exclusion) with the
  push depth it depends on — the same discipline the decision-level
  tagging already applies one level down.
* Research question: can recorded cases be *kept* across pops when
  their derivation did not touch popped clauses? (Dependency tracking
  per case — the CEGAR response solver knows which clauses supported a
  cube.) This is the difference between "restart per query" and a truly
  incremental games loop. *Answered — see the pop-retention entry
  below*: locked-ness of root implications turned out to be the right
  dependency granularity, and recorded cases need no tracking at all
  (they survive any clause deletion).
* **In-place monotone continuation — done** (see `PLAN.md` §1c for the
  full design and measurements): the live solver continues across
  add-only deltas, keeping root trail, learnt clauses, handled cases
  (re-verified against exactly the added clauses), activities, and the
  conflict check; parity unrolling goes quadratic → linear (75 ms →
  1 ms at 200 steps) and monotone-UNSAT re-solves are free. Two
  corrections to the plan sketched above, found during implementation:
  root assignments are *not* all forced — root **pure-constant**
  assignments are winnability-preserving choices, and survive an added
  clause containing their literal only if the root functions entail
  that clause with the unassigned variables treated adversarially; and
  handled cases need not be discarded wholesale — the same adversarial
  entailment check re-validates them per extension (budget-capped),
  which keeps CEGAR/case-split work alive across solves.
* **Temporary queries no longer cost continuation — done**: a query
  (`solve_with_assumptions`/`solve_with_clauses`, i.e.
  `check-sat-assuming` and the ∃∀ frontend's negation clause) runs on
  a throwaway solver built beside the continuation base and serves the
  model calls until the next solve; the base stays untouched, so
  interleaved probe queries keep the plain solves linear (probed
  parity unrolling: every step continues in place). Likewise, a pop
  of frames the base never solved (push/assert/pop scoping) no longer
  invalidates anything: the base tracks per-frame *integrated sizes*,
  frames are append-only, and the delta is derived at solve time.
* **Assumption-scoped solving in the core — done for existential
  literal assumptions** (`IncDet::resolve_with_assumptions`, tried
  first by `IncrementalSolver::solve_with_assumptions`): assumptions
  are assigned as *constants at fresh decision levels* — the
  existential analog of universal case assumptions — sticky across
  backtracks, communicated to the conflict check as level-guarded
  units. They carry no implication clauses, so conflict analysis keeps
  their negations in every resolvent: everything learnt or recorded
  during a query (learnt clauses, CEGAR cases, root assignments) is
  matrix-valid and *persists* after retraction. Retraction is lazy
  (backtracking at the next solve), so a satisfiable query state
  serves models and certificates directly. The pieces that made this
  sound: CEGAR rounds take the query literals as extra response-solver
  assumptions (so recorded cases respect them and region coverage
  stays trustworthy); assumption *violations* (a firing implication of
  the opposite polarity against the constant) resolve by CEGAR rounds
  only, since variable-centric clause learning would lose the
  assumption literal from the resolvent; the redundancy check keeps
  literals whose variable has no implication clauses; root-assigned
  assumption variables are answered directly (forced constants and
  functions are implied — a function-entailment counterexample is a
  winning universal move for the query, verified under the query
  units); and the fast path declines when recorded cases predate the
  query or a root pure *choice* blocks the verdict — the throwaway
  query solver remains the fallback, and a declined attempt marks the
  base for re-search since it may already have backtracked it.
* **Negative result — the ∃∀ check does *not* benefit from assumption
  queries.** The plan was to reify the growing disjunction
  `¬a₁ ∨ … ∨ ¬aₖ` as `¬AND(a₁…aₖ)` with hash-consed gates and assume
  the single gate literal. Measured on an incremental ∃∀ workload
  (8 constants, 60 asserts, check after each): the flat temporary
  clause solves the session in ~45 ms; the gate reification takes 4.4 s
  with full-width gates and 1.26 s with a binary chain — 25–90x
  slower — *even when the reified instance is solved through the old
  throwaway path*. The stale accumulated gates themselves make the
  internal instances harder: ID handles the flat disjunction as one
  wide clause (a single implication candidate once the roots
  determinize), while the gate chain turns the same constraint into a
  chain of decisions. The ∃∀ check therefore keeps the temporary
  disjunction clause (re-measured after the violation fix below: still
  ~23x slower reified); assumption queries remain the tool for
  *literal* probes.
* **Assumption violations are final, not conflicts.** A firing
  implication clause of `¬a` that was *root-registered* has permanent
  root functions as premises: at the firing point every strategy
  compatible with the root state yields `¬a`, and since pure rewrites
  never touch assumption variables, the pure-literal lemma lifts this
  pointwise fact to the strategy level — the query is unsatisfiable
  outright, with the firing assignment's universal part as the
  winning-move candidate (verified under the query units before
  exposure, so choice-tainted candidates are filtered while
  gate-determined ones — the synthesis case — pass). This replaced the
  earlier CEGAR-per-violation loop and its budget: no enumeration, no
  learning surgery needed. Violations via implications registered
  *above* the root (possible while the variable is transiently
  unassigned between a backtrack and its re-assumption) depend on
  revisable search state and abort to the throwaway fallback.
* **Universal assumptions — done**: a universal assumption literal
  restricts the universal player's domain — the "what if the
  environment plays u" probe of a games loop. On the fast path the
  literal is assumed like a case assumption but *not* registered as a
  case (nothing is recorded or excluded for the restriction itself);
  cases closed during such a query record the query cube as part of
  their own, the case-split domain search stays inside the
  restriction (so an empty remaining domain correctly means the
  *restricted* region is covered), and the final certificate region is
  scoped by the query cube. Restrictions are assumed *before* the
  existential assumptions and scope their entailment/violation checks
  — a verdict derived at a point outside the restriction would be
  about a game the query never plays; the fuzz caught exactly this as
  the "unsatisfiable stack answers any query" shortcut firing under a
  restriction (restricting *weakens* the obligation, so a globally
  lost game can be winnable on a sub-domain). The throwaway fallback
  substitutes the restriction into the instance (a unit clause would
  instead let the universal player falsify it), and contradictory
  restrictions denote an empty domain, vacuously satisfiable.
* **Recorded cases stay usable across queries — done**: the fast query
  path no longer requires an empty case list. A recorded region counts
  as covered for the query, so its recorded strategy must honor the
  assumed existential constants on the part of its region that
  intersects the domain restriction — checked with one SAT call per
  case (`case_compatible`, sharing the certify encodings), skipped
  entirely for restriction-only queries (recorded strategies satisfy
  the matrix, which is all a restriction asks) and for regions whose
  cube contradicts the restriction. The entry entailment checks
  exclude the handled cubes (inside them the compatible region
  strategies govern). The soundness bedrock is pointwise forcing:
  unique-consequence functions constrain *every* matrix model at a
  point, so a verified response can never contradict a root-forced
  function on its region — which is why the root-constant and
  violation verdicts stay final with cases retained. Fast-path hits in
  the differential fuzz went from 20 to 88 per 256 sessions (half of
  which run with continuation disabled).
* **Pop-retention of solved state — done** (`IncDet::retract_to_depth`;
  the dependency-tracking question above, resolved for the tractable
  slice): a pop of a clause-only frame keeps a *satisfiable* base
  when, after a backtrack to root, none of the popped originals and
  none of the live learnt clauses is *locked* (registered as a root
  implication) — locked-ness is exactly the dependency that matters,
  because an unlocked clause supports no root function. The popped
  originals and *all* learnt clauses (they may resolve against popped
  ones; per-clause resolution ancestry was not worth tracking) are
  deleted like a reduce-DB sweep and the conflict check is rebooted;
  recorded cases survive (their strategies satisfy a superset of the
  shrunk matrix), root pure-constant choices survive (purity is
  monotone under clause removal — deleting clauses only *frees*
  occurrences), and the satisfiable verdict survives outright. The
  bookkeeping blocker fell to per-clause depth tags: every original
  carries the stack depth it was loaded at, through both the build
  path (rebuilds now construct the core solver frame by frame instead
  of from a flat QCNF) and the extension path. One subtlety the unit
  test surfaced: a clause can be integrated *unlocked* because a root
  pure choice already satisfies it, so whether retention applies is a
  property of the solving trajectory, not of the instance alone.
  Measured on scoped re-solving (`parity-scoped` in
  `bench_incremental`: push a clause frame, solve, pop — 200 rounds
  on a 200-step chain): ~124 ms retained vs ~145 ms with the base
  dropped on every pop (the prior behavior) vs ~217 ms
  rebuild-per-solve. Modest on this easy family because carried
  learnt clauses already make its rebuilds cheap — but every round
  stays on the extension path (399 in-place extensions), keeping the
  cases and activities that matter on harder instances.

## RQ3 — SMT-LIB as the surface language

**Status: a Boolean-fragment frontend exists** (`src/smtlib.rs`,
auto-detected by the CLI): `declare-const`/`declare-fun` (nullary
Bool), `define-fun` as the definition-level input, assertions over
`and`/`or`/`not`/`=>`/`=`/`xor`/`ite` with hash-consed Tseitin gates,
`(assert (forall (...) (exists (...) body)))`, `push`/`pop`/
`check-sat`/`check-sat-assuming`, and `get-model` printing the
piecewise Skolem functions as `define-fun`s parameterized by the
universal variables. Free constants are solved in the innermost block
(truth-equivalent) when they do not occur under a forall; when they
do, the session is ∃∀ and solved by negation (see below). Remaining
notes:

* `define-fun` ↔ pre-determinized variable (RQ1's API, standardized);
  `push`/`pop`/`check-sat-assuming` ↔ RQ2; `get-model` returning
  `define-fun`s for the existentials ↔ the Skolem functions the
  certifier already extracts piecewise. The output side matters: a
  solver whose *answer* is a function is a synthesis tool, and SMT-LIB
  is the only widely-parsed syntax for that answer.
* Quantifier structure: 2QBF is `(forall (u...) (exists (e...) φ))`
  with φ quantifier-free. Users writing SMT-LIB don't Tseitin anything;
  the solver picks its own clausal form and keeps the definitions —
  the PG problem becomes structurally impossible rather than
  heuristically mitigated.
* Open question: how much of full Bool/BV ∀∃-SMT is reachable before
  theories (bit-blasting BV eagerly keeps everything Boolean but risks
  re-losing word-level structure — the same story one level up).
* The emitted models are validated indirectly (the pointwise evaluator
  they mirror is checked against the matrix exhaustively in the fuzz
  harness); running an external SMT solver over `get-model` output as a
  CI check would close the remaining gap, but no such solver is
  available in this environment.
* **The 3-block gap that matters for synthesis — closed for the
  determined case**: the natural bounded synthesis shape is
  ∃ parameters ∀ inputs ∃ gates(determined). Because the inner block
  is *defined* (two-sided gate encodings are self-dual), the shape is
  solved by negation without any core extension: the frontend solves
  `∀ parameters ∃ inputs, gates: ¬(∧ assertion roots)` and inverts the
  verdict; the synthesized parameters are the negation's UNSAT witness
  (the universal part of the final conflicting assignment, recorded at
  every unsatisfiability site in the core). Only genuine ∃∀∃ — a free,
  *underdetermined* inner block — remains out of scope and rejected.
  Open engineering item: the recorded witness candidate is heuristic
  (pure-literal assignments are winnability-preserving choices, not
  pointwise-forced values), so it is verified with one SAT call before
  exposure; if verification fails the answer is `sat` without a model.
  A complete extraction fallback (e.g. solving the dual instance or a
  CEGIS-style repair of the candidate) would close this; across 20k+
  random ∃∀ instances the differential harness has not yet observed a
  rejected candidate, so the gap is currently theoretical.

## RQ4 — Theories: lifting ID to ∃∀-SMT

What generalizes cleanly, judged against the current architecture:

* **CEGAR does** — it is already model-based (universal model →
  existential response → generalization) and is exactly the
  exists/forall loop of Dutertre's Yices `ef-solve`. Cube
  generalization over theory literals replaces support counting.
* **Case splits do** — assume a universal *predicate* instead of a
  literal; the domain solver becomes a theory solver.
* **The frontier does** — "settled by definitions" is theory-agnostic;
  the frontier is the boundary of the defined terms.
* **The clausal core does not** — watched literals, unique
  consequences, and implication-clause resolution are Boolean.
  Determinacy modulo a theory means "this constraint *defines* x given
  earlier variables" (x = t as a definition; more generally
  single-valuedness), which is a per-theory notion. Research direction:
  theory-aware unique consequences (equalities and functional
  congruences as definitions), or the layered architecture — ID on the
  Boolean skeleton, theory solver for the atoms — which converges
  toward quantified abstraction (QuAbS) from the other side.
* **Measured warning on per-query cost**: the conflict-check workload
  is thousands of small incremental queries; even CaDiCaL and
  CryptoMiniSat lose to varisat on it (~6k vs ~9k conflicts/min on
  adder2). An SMT backend pays this severalfold. Any theory lift needs
  batching or a lazy design, not a drop-in backend swap (the
  `SatSolver` trait makes the naive swap a one-day experiment — worth
  running once, expecting it to lose, to get the number).

## RQ5 — Positioning: a building block for two-player games

An incremental ∀∃ solver that returns functions is the inner loop of
bounded synthesis and safety-game solving: the game unrolling depth maps
to push levels, the winning-strategy extraction maps to `get-model` (or
`SkolemModel::to_aiger` / CLI `--strategy`, which emits the functions as
an AIGER strategy circuit — see `PLAN.md` §2), and the incrementality
between depths is where the interface (RQ2/RQ3) earns its keep — none
of which a one-shot QDIMACS call can express.

* Competition/baselines: Z3's quantifier engines, Yices `ef-solve`,
  SyGuS solvers. The niche for an ID-based engine is structure
  exploitation plus *certified* function output plus incrementality.
* **Benchmark built — done** (`aiger::Unroller`, `bench_games`): the
  AIGER path now parses *sequential* safety specifications (latch
  next-state and reset, the SYNTCOMP `controllable_` input convention,
  outputs as error signals) and unrolls them one time step per solve
  into the incremental API — fresh input and gate copies per step, the
  latch chain connecting to the previous step, and the error signals
  asserted false. The unrolling is monotone, so the per-depth queries
  ride the whole incremental stack. Validated by a differential
  proptest against an *independent* clairvoyant-simulation game oracle
  (random small sequential circuits, every depth's verdict compared
  and every satisfiable result certified), plus hand-built games. The
  benchmark families are SYNTCOMP-shaped generators: a
  bounded-response arbiter (realizable iff clients ≤ bound) and
  pursuit games on a ring/corridor.
* **The clairvoyant relaxation is real, not a technicality**: a ∀∃
  prefix fixes the universal input sequence in advance, so a bound-k
  satisfiable answer is a *necessary* condition for realizability
  (unsatisfiable refutes outright) but not sufficient. Measured
  concretely: the corridor pursuit with a staying obstacle is a
  classic cop-win game for a *reactive* cop, yet stays satisfiable at
  every probed depth — the future-seeing robot times swaps past the
  oblivious sweep. **The causality post-check closing this gap is
  built** (`Unroller::strategy_is_causal`): per controllable output of
  the emitted strategy circuit, one SAT call asks whether two copies
  of the circuit agreeing on all inputs up to that output's step can
  disagree on the output — semantic support, because the structural
  cone is too coarse (piecewise region selectors routinely mix steps
  even when the selected values agree, which a first cone-based
  attempt reported as false negatives). A causal strategy makes the
  bounded answer *sufficient*: it wins the real game for the unrolled
  depth. Demonstrated end to end (`bench_games`): the ring pursuit's
  found strategy is causal (mirroring — realizability certified up to
  the bound), the corridor's is not (swap-timing needs the future);
  a synthetic "predict the next input" spec is clairvoyantly
  satisfiable and correctly rejected. Remaining gap to full
  realizability: a causal bounded strategy certifies the bound only —
  unbounded synthesis still needs an inductive argument on top.
* **Which artifacts transfer across game depths — answered** (the RQ2
  dependency question, measured end to end): *learnt clauses* transfer
  (rebuilds are seeded with them; both modes benefit equally);
  *unsatisfiable verdicts* transfer via the monotone shortcut (the
  overloaded arbiter: ~1.3 ms in-place vs ~9.5 ms rebuilding each of
  16 depths); *handled cases do not transfer*: the fresh step
  variables have no function in any recorded case, so the adversarial
  per-case re-verification necessarily fails — the extension gate now
  detects this syntactically (a new clause constraining a variable
  declared by the same extension declines for free, instead of
  discovering the same in per-case SAT calls). In-place extensions
  therefore happen only until the first case is recorded (2 of 24
  depths on the rings), after which in-place and rebuild do the same
  learnt-seeded work and differ by search-trajectory variance
  (arbiter 2-2 at depth 16: ~613 ms vs ~325 ms against in-place;
  ring-4 at depth 12: ~1.46 s vs ~1.86 s in favor).
* **Definitional case extension — tried and rejected by measurement.**
  The idea: an unrolling step's clauses are definitions of the fresh
  variables, so recorded cases could be extended with the induced
  functions instead of declining. Implemented as *deferred
  re-verification*: run the extension search first, then graft the
  final state's snapshot functions for the fresh variables onto every
  retained region (materializing CEGAR responses into closed chains —
  their live root snapshot never carries decision-level functions) and
  re-check the deferred clauses per region; failure falls back to
  rebuild. The mechanism is sound (the check arbitrates the graft),
  and two real gaps surfaced on the way: fresh *inputs* are decisions,
  not root functions, and responses read only the root snapshot. But
  the graft rarely wins: the final region's new-step choice loses on
  old regions with different latch states (ring-6: 20 of 21 deferred
  checks fail — the failures are semantically genuine, each region
  needs its *own* new-step response, which is a per-region search,
  i.e. the very cost the idea was meant to avoid). Aggregate: one
  wasted search per depth, 2–4x slower than the syntactic decline
  (arbiter 2-2: 613 ms → 1.15 s; ring-4: 1.46 s → 6.2 s) for 1–2
  extra extensions. Reverted; the decline stays. What *would* work is
  bounding the per-region response search or lazily re-opening failed
  regions — both approach rebuild cost, and un-excluding a region
  invalidates every later region's piecewise claim, so re-opening
  needs re-verification cascades. Cases remain per-matrix artifacts.

## RQ6 — Quantifier alternations

The core is deliberately 2QBF (root permanence, pointwise forcing over
*one* universal frontier). Four algorithmic routes to ∃∀∃ and beyond,
judged against what this codebase already has:

* **Dependency-aware ID (the DQBF route).** Generalize determinacy to
  per-variable dependency sets: an existential of block `k` may only
  take implication premises over its preceding universals (and
  existentials with smaller dependency sets); determinacy means a
  unique value under every assignment of *its* dependencies. This is
  the conceptually clean extension — ID's implication sets are already
  definitions, and Pedant shows definition-based solving carries to
  DQBF — but it rewires every invariant this project spent its
  validation budget on: conflict analysis must respect the dependency
  lattice (the soundness pitfalls of long-distance Q-resolution live
  exactly here), the pointwise-forcing lemma that underpins root
  permanence, pure choices, assumption verdicts, and certificates is
  per-frontier, and the conflict check becomes a QBF query itself for
  inner blocks. High risk, whole-solver surgery. Not the smart first
  move.
* **Innermost-block expansion.** ∀-expand the innermost universal
  block into two copies per variable and recurse. Doubles the matrix
  per variable; only smart when that block is tiny. A degenerate
  special case of the next option; not worth separate machinery.
* **Recursive expansion with a persistent ID oracle (the smart
  move).** RAReQS-style CEGAR at the outermost existential block `X`:
  a plain SAT abstraction over `X` proposes candidates `X*`; the
  remaining ∀Y∃Z is *exactly* the 2QBF core — and the incremental
  API makes it a **persistent oracle**: declare `Y` universal and
  `Z ∪ X` existential once, then each candidate is one
  `solve_with_assumptions(X*)` — the workload the in-place assumption
  queries, case compatibility, and learnt-clause persistence were
  built for, and everything learnt is matrix-valid across candidates
  (assumption literals survive in every resolvent). On inner UNSAT
  the solver hands back a *verified* universal witness `Y*` — no
  UNSAT-core plumbing needed — and the refinement is the classic
  expansion: add `matrix[Y := Y*]` with fresh `Z`-copies to the
  abstraction (guaranteed to exclude `X*` precisely because the
  witness is verified); when the witness is unavailable (the recorded
  candidate failed verification), the weak refinement `¬X*` keeps the
  loop total. A ∀-outermost prefix gets the dual loop (enumerate
  refuting outer assignments, block answered ones); negating the
  matrix instead — the self-duality trick the ∃∀ frontends use — was
  tried and abandoned, see below. Deeper prefixes recurse, with strong
  refinements available at every level. What no existing
  expansion solver has: an inner oracle with persistent learning,
  certified inner strategies (composable toward alternation
  certificates: `X*` constants + the 2QBF Skolem functions), and
  verified witnesses driving the refinements.
* **Determinize-then-dispatch (hybrid).** Run the definition-level
  discovery across the whole prefix first — an inner existential
  whose implication premises all lie within its own dependency prefix
  is a *definition* regardless of alternation depth and can be
  treated as a gate (eliminated from the game). The residual
  undetermined variables then go through the expansion loop. This is
  the RQ1 story applied to alternations: on structured instances most
  inner existentials are gates, so the expansion loop only ever sees
  the genuinely strategic variables. Natural second step once the
  expansion loop exists.

**Status: implemented, validated, and measured** (`src/alternation.rs`,
CLI-dispatched for QDIMACS beyond two blocks). On the CADET suite it
lifts the score from 93 correct + 33 unsupported to **125 correct, 0
wrong** — 32 of the 33 alternation instances solve within 30 s, and
none of them by a narrow margin (both `pec_adder` pairs,
`adder2`-class, planning, blocks-world, 7-block circuit equivalence, a
22-block lights-out puzzle, the depth-6 arbiter). One survives: `biu`
(∃48 over 46–47-variable universal blocks — neither expansion nor
blocking-based refinement dents 2⁴⁸).

The pipeline, outermost first:

1. **Transform once, globally** — simplify and ∀-expand to a fixpoint
   *before* any candidate loop starts.
2. **Enumerate small innermost universal blocks** rather than
   reasoning about them, which removes an alternation outright.
3. **CEGAR at the outermost block** — ∃ blocks propose candidates over
   a SAT abstraction, ∀ blocks enumerate refuting candidates — with
   the recursion simplifying each restricted sub-instance.
4. **The 2QBF core as a persistent oracle** at three-block leaves: one
   `IncrementalSolver`, one `solve_with_assumptions` per candidate,
   learning carried across all of them.

Soundness rests on three arguments. *Expansion*: each copy's conjunct
mentions only that copy's variables, so a strategy for the expansion
projects back to the original by fixing the other copies' universals
arbitrarily — the cross-copy dependencies that merging per-level
copies allows are never needed. *Refinements*: a refuted candidate's
blocking clause is always sound, and an expansion point may be **any**
universal assignment, so the *unverified* recorded witness serves
(verification only ever mattered for exclusion). *Relaxation*: the
propositional copies existentially relax every inner variable, an
over-approximation, which is what makes strong refinements legal at
any recursion depth.

Five things measurement decided, several against the obvious design:

* **Measure before redesigning.** A feature-gated leaf-solve counter
  (`--features probe`) showed the hard instances reaching *zero* leaf
  solves in twenty seconds — so the persistent-oracle redesign that
  looked like the clear next step would have bought nothing. The real
  fault was that a *global* transformation was being reapplied per
  candidate.
* **Transform once, not per candidate.** With expansion inside the
  recursion, a restricted sub-instance looked profitable to expand
  again, so every candidate of every enclosing loop redid the matrix
  doubling. Hoisting it solved 22-block `lights3` (21.9 s) and the
  depth-4 arbiter (0.39 s).
* **Expand the innermost block only, and only when small.** Expanding
  an *outer* block also removes an alternation but multiplies every
  survivor by `2^|Y|` — the fuzz found instances that solve directly
  yet exhaust the budget once 3-variable blocks became 24-variable
  ones. And CEGAR beats expansion on large blocks because it
  enumerates only the *relevant* assignments: a 10-variable block made
  `p10-1.pddl` 17x slower expanded, so blocks are capped at eight.
* **A big expansion is only safe if it collapses the prefix.** At ≤2
  blocks the instance goes straight to the core (`BLOCKS4iii` hands it
  950k clauses happily, 30 s timeout → 1.9 s); otherwise it pays for
  per-level simplification and abstraction seeding on every candidate,
  so *speculative* expansions get a 50k clause budget instead of 2M.
* **Simplify every level.** `restrict` fixes a whole block and
  expansion copies matrices, both manufacturing units and pure
  literals in bulk that every level was rediscovering. A per-level
  pass (universal reduction, units, pure literals both directions, to
  a fixpoint, plus dropping variables that no longer occur) solved
  `biubug` (0.19 s → 7 ms after the occurrence check) and `ev-pr-4x4`,
  and made the differential fuzz 3x faster.

Two dead ends are worth recording. Negating the matrix for
∀-outermost prefixes cascades Tseitin gates through the recursion and
exhausts memory — the dual candidate loop keeps the matrix fixed
instead. And raising the round budget only converts give-ups into
timeouts; the survivors need better refinements, not more rounds.

Validation: four differential families (both dispatch paths, deep
prefixes, and all eight core option combinations) against the
brute-force oracle at 20–30k cases each. Beyond the reach of brute
force, the two dispatch paths validate *each other*: the expansion
dispatch and the pure-CEGAR loops share almost nothing but the leaf
oracle, so `--no-expansion` turns a real instance into a differential
check. Over 701 multi-block instances of the `reduction-finding`
corpus (hundreds of variables each), run through three configurations
— default, no-expansion, and no-CEGAR/no-case-splits — **591 reached a
verdict and all 591 agreed** (249 satisfiable, 342 unsatisfiable, zero
disagreements); the remaining 109 hit the 10 s timeout or the
recursion budget in at least one configuration. That is ~2100 real
solves' worth of agreement on the youngest code in the tree, against
the 33 instances the CADET suite contributes.

**Certificates beyond 2QBF — done**
(`Strategy`, `solve_certified`). A satisfiable alternation answer used
to come with nothing at all, which was the largest hole in the
project's own thesis (certified function output is the claimed niche).
The strategy is now *composed* out of the pipeline: simplification
contributes the literals it forced, an ∃-loop the constants of its
winning candidate, a ∀-loop one sub-strategy per enumerated cube
(exhaustive, because that loop only succeeds once every candidate of
the block is answered), and a leaf the core's certified Skolem model.
Verified exhaustively in the differential fuzz — every composed
strategy is evaluated at *every* universal assignment against the
*original* matrix — and produced for **97% of satisfiable results**
(25 000 of 25 809); the remainder are instances that needed a
∀-expansion, whose copies would have to be folded back into a
multiplexer over the expanded block.

The verification paid for itself immediately: the first version
recovered simplification's assignments by inspecting occurrence
patterns afterwards, which is wrong as soon as the fixpoint cascades
(a variable occurring in both polarities becomes pure only after
earlier assignments delete clauses). `simplify` now *reports* what it
forced. Note also that eliminating a *universal* pure literal needs no
strategy entry: a strategy valid at the eliminated value stays valid
at the other, since the clauses containing that literal are satisfied
by the literal itself.

**Composed strategies as circuits, checked by SAT.** A composed
strategy is now also a *circuit*: `Strategy::to_aiger` renders it in
the same ASCII AIGER format `SkolemModel::to_aiger` emits for a 2QBF
result, over the same shared AIG builder, so a caller sees one
artifact format regardless of prefix depth. `Fixed` and `Choose`
become constant wires, `Split` a priority multiplexer over its cube
conjunctions, and `Leaf` the 2QBF encoding verbatim
(`SkolemModel::build_into`, factored out of `to_aiger` so the two
cannot drift).

That circuit is what makes the certificate checkable at real scale.
`verify_strategy` encodes it into CNF alongside the matrix and asks
for a universal assignment falsifying some clause: unsatisfiable means
the strategy wins everywhere. One SAT call replaces `2^|Y|`
evaluations, which is the difference between checking the fuzz range
and checking an instance with a 47-variable universal block. Both the
universals and the existentials the strategy leaves undetermined stay
free, so the check reads "for *all* universal assignments *and all*
values of the undetermined variables" — the strong form, which is
sound because a variable is only left out when the solve found it
irrelevant. It is wired to `--certify` and `--strategy` for any prefix
depth.

The two checks now run side by side in the fuzz: the exhaustive
pointwise one, the SAT one, and — because the SAT check works on the
AIG rather than on the rendered text — a third that parses the emitted
AIGER back and simulates it. All three agreed across 300 000 cases per
family after one real bug: the multiplexer skipped a variable when
every branch agreed with the value *before* the split, which silently
dropped variables that only the branches define.

**Inverting ∀-expansion — the last gap, now closed.** Expansion was
the one dispatch that produced no strategy, and on real instances it
is the *common* dispatch, not the 3% corner the fuzz suggested (the
generated instances are small enough that the CEGAR loops usually
win). Inverting it is cheap once the bookkeeping exists:
`expand_universal_block` already builds, per assignment `σ` of the
enumerated block, a renaming of every variable bound after it, so it
now returns those renamings and `Strategy::Expanded` replays them —
the sub-strategy plays all copies at once, and the copy `σ` the actual
assignment of the block selects supplies the value. Nested expansions
nest as `Expanded` nodes, innermost applied first.

Soundness is the projection argument the expansion itself rests on: if
`S` wins the expansion, then `Z(u, b) := Z^b(u)` wins the original,
because the conjunct for `σ = b` is exactly `M[B := b]` over `Z^b`,
and `Z` may legally depend on `b` since it is bound after the block.
One trap worth recording: fresh copy variables were numbered above the
*current* instance's maximum, and simplification can drop the
original's highest variable, so a copy could collide with an original
variable that the composed strategy also assigns. Expansion now takes
a floor carried across the fixpoint.

With that, **every satisfiable fuzz result carries a strategy**
(174 084 of 174 084, up from 97%) and all **19 solved satisfiable
multi-block instances of the CADET suite certify** — by the internal
SAT check and independently by the external Python simulator sampling
the emitted AIGER. (An earlier count of 7 of 13 recorded here was read
off a sweep that had not finished; the pre-inversion coverage was
worse than 7/19, not better.) The suite itself is unchanged at 123
correct, 0 wrong at the time (125 after the memo below).

**Strong dual refinements — implemented, measured, rejected.** The
∀-loop blocks one *point* per round: it proposes a universal candidate,
recurses, and on a satisfiable answer adds the single blocking clause
`¬candidate`. The obvious upgrade is region learning — block the whole
cube the answer covers — and the certificate machinery makes it a
one-liner: the answered candidate comes with a winning sub-strategy, so
asking the falsification query "is some clause falsifiable under this
strategy, assuming the candidate?" with the candidate as *assumptions*
returns an unsatisfiable core, and the assumptions the refutation used
are exactly the literals the strategy needs. Everything else
generalizes away, soundly, for one SAT call per round.

It does not pay, for a reason the design did not anticipate: **the
∀-loop's cubes are too short to generalize.** On `lights3` (22 blocks,
the deepest suite instance) the 254 generalization queries had **0 of
254** cube literals to drop — every candidate cube was a *single*
literal, because by the time the recursion reaches a ∀-loop the
expansion dispatch has eaten the small universal blocks and
`normalized`/`restrict` hand each level one block at a time. On
`ev-pr-4x4` it dropped 3 of 21 literals across 7 queries and saved
exactly one round of 14. Rounds on `lights3`: 631 before, 631 after.

The cost, meanwhile, is quadratic in the very loop it was meant to
shorten: the query encodes the *composed sub-strategy*, whose size
grows with the rounds already taken (8.6M strategy nodes and 7.4M
clauses across those 254 queries, ~34k nodes each), which turned
`lights3` from 24 s into 49 s. Reverted. Region learning needs
strategies built to be universal-independent — a dual-CEGAR
abstraction in CAQE's sense — not point strategies generalized after
the fact.

One byproduct worth recording: across those 261 queries the
sub-strategy was confirmed valid every time, which is 261 independent
strategy verifications at *every* recursion level of two real
instances, not just at the top.

**Memoizing the recursion — the largest single win in RQ6.** The
candidate loops restrict one block at a time, so an *outer* loop
re-triggers its whole subtree per candidate, and different candidates
routinely restrict onto the same inner instance. A probe counting
distinct sub-solves made the scale obvious: on the 22-block
`lights3_021_0_009`, **363 of 377** recursive sub-solves repeat an
instance already answered. `solve_normalized` now looks its instance
up in a memo before dispatching.

Two design choices decide whether it pays.

*Key on the simplified, normalized instance.* That is where the
repeats become visible — distinct restrictions collapse onto the same
instance only after their units and pure literals are propagated away.
Keying on the incoming instance would find almost nothing.

*Store a fingerprint, not the instance.* The first version used the
canonical form itself as the key, which is exactly as large as the
instance: the memo blew a 4M-unit budget after **14 entries** and gave
back only half the speedup (13.5 s instead of 1.0 s). The key is now a
128-bit hash — clause literals sorted, clause hashes combined
commutatively so clause order is irrelevant, addition rather than XOR
so duplicated clauses stay distinguishable. Two distinct instances
collide with probability under `n²/2^129`, below 1e-25 for the largest
table this builds, which is many orders of magnitude under the rate at
which the hardware miscomputes the same answer. With 16-byte keys the
only thing that grows is the cached strategies, so the budget is on
those, and a recursion whose sub-solves do not repeat switches the
memo off after a warmup rather than paying a fingerprint per call.

Measured:

| | before | after |
|---|---|---|
| `lights3_021_0_009` (22 blocks) | 24.2 s, 143 MB | **1.0 s**, 122 MB |
| `arbiter-05 …depth-6` | >30 s timeout | **2.9 s** |
| `BLOCKS4iii.7` | 1.95 s | 1.99 s |
| CADET suite | 123 correct, 2 timeouts | **125 correct, 0 timeouts** |

Peak memory *falls* on `lights3` despite the table, because the memo
also avoids rebuilding the intermediate instances. The 701-instance
cross-validation is unchanged (591 decided, zero disagreements), and
so is every other suite instance — this is a pure win on the deep
prefixes and invisible elsewhere. `biu` is now the only CADET instance
the solver does not decide.

Next steps in order of leverage: `biu`, which needs something
genuinely new (∃48 over 46–47-variable ∀ blocks defeats expansion,
blocking, and now memoization — 4102 rounds in a single loop with *no*
repeated sub-solves); ∀-side persistent oracles (needs ∃∀ assumption
support in the core), which is also the prerequisite for doing dual
refinement properly; and the determinize-then-dispatch hybrid.

## Suggested experiment order

1. Paired-encoding experiment (RQ1) — settles the format thesis with
   numbers; generator + three encoders, no solver changes.
2. Pre-determinization API + QCIR frontend (RQ1/RQ3) — small, unlocks
   structured corpora.
3. Push/pop with depth-tagged artifacts (RQ2) — the enabling step for
   everything in RQ5; hardest invariant work, do it while the
   certification harness can still arbitrate every step.
4. SMT-LIB Boolean frontend over (2) and (3) (RQ3).
5. Naive SMT-backend swap measurement, then the layered design (RQ4).
6. SYNTCOMP-derived incremental benchmark (RQ5).
