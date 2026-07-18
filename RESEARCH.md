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

* **Direct pre-determinization**: an API that enters a defined variable
  as already-deterministic (implications attached, no determinacy
  checks) would skip the discovery pass. Measure discovery cost on
  large circuits first — if initial propagation is cheap relative to
  solving, the API is convenience, not speed.
* **Paired-encoding experiment**: the thesis needs instances that exist
  in both forms. Generate them: take circuit families (adders,
  comparators, sorting networks), emit (a) QAIGER, (b) two-sided CNF,
  (c) Plaisted–Greenbaum CNF, and compare solve times. Prediction from
  current data: (a) ≈ (b) ≪ (c) for ID, while CEGAR-style solvers care
  much less.
* **How much does gate *detection* on CNF actually recover?** Markus's
  position (QDIMACS is fine, detect the gates) is testable now: count,
  per QBFEVAL'17 instance, the fraction of existentials that initial
  propagation determinizes; correlate with solve success. The 38 `stmt`
  instances suggest the answer is "not enough under PG", but a corpus-
  wide number would settle it.
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
  oblivious sweep. A synthesis loop on top of this interface needs a
  causality post-check or per-step ∃∀ queries for the sufficient
  direction.
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
  ring-4 at depth 12: ~1.46 s vs ~1.86 s in favor). Open follow-up:
  *definitional case extension* — the clauses of an unrolling step are
  definitions of the fresh variables (gates, latch equalities), so
  each recorded case could be extended with the canonical functions
  those definitions induce, making cases transfer across depths;
  requires recognizing definitional clause groups, which the
  QCIR/QAIGER definition-level input path (RQ1) would get for free.

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
