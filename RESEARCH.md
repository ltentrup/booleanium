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
* **Preprocessing, and the tension it has with this thesis — open.**
  Bloqqer and HQSpre are not optional in practice; a large part of
  QDIMACS-level performance comes from them, and being fast on QDIMACS
  is a requirement here, not a nice-to-have. The tension is specific to
  this solver: the result above says ID runs on gate structure that
  one-sided CNF encoding destroyed, and classic CNF preprocessing —
  blocked-clause elimination above all — can destroy exactly that
  structure again. So "preprocess, then determinize" may be a large win
  on clausal instances and a *loss* on circuit-derived ones, and which
  it is on a given corpus is not obvious. HQSpre's gate detection and
  structural preprocessing are presumably the right shape for that
  reason.

  The experiment to run before importing anything: the RQ1
  paired-encoding generator already produces the same instance in
  definitional, two-sided-clausal and one-sided-clausal form, and the
  determinization-fraction metric is already instrumented. Preprocess
  each form, measure the fraction *after* preprocessing, and see
  whether preprocessing and determinization compete or compose.

  Second constraint, heavier than usual here: every satisfiable answer
  in this project is certified. Refutations through preprocessing are
  what QRAT was built for and the checker is in-tree, but satisfiable
  answers need *strategy reconstruction* through each preprocessing
  step. That is the part to scope carefully, and it is why importing a
  preprocessor wholesale is not a small change.

* **QCIR frontend — done for prenex circuits at any depth**
  (`src/qcir.rs`, auto-detected by the CLI via the `#QCIR` header):
  `and`/`or`/`xor`/`ite` gates over cleansed or named identifiers
  become existential variables with two-sided Tseitin definitions — the
  same definition-level path as QAIGER, with richer gates. A prefix
  ending universally is solved by its dual (gate definitions are
  self-dual, so flipping the quantifiers and negating the output
  suffices) at any depth, mirroring the SMT-LIB frontend's synthesis
  mode. Only non-prenex quantifier gates are rejected.

  The depth limit was lifted once RQ6 could handle depth: the frontend
  used to reject anything beyond two blocks, which left the solver's
  32-block capability reachable only through QDIMACS — the wrong way
  round, since QCIR is the format deep-prefix corpora actually ship in.
  Beyond two blocks the CLI dispatches to the alternation front-end,
  with composed strategies emitted as AIGER **under the surface
  names** and checked by `verify_strategy`, and `--no-expansion`
  available as the differential cross-check.

  Validated by two differential proptests against direct circuit
  evaluation, independent of the Tseitin conversion: the original
  two-block one in both quantifier orders, and a deep one (3–5 blocks,
  either outermost quantifier) against a *general* game oracle —
  alternating enumeration over the block structure, i.e. the definition
  of QBF truth applied to the circuit — at 30k cases.

## RQ2 — The incremental interface (the QIPASIR gap)

SAT's success as a *library* (IPASIR: add-clause / assume / solve) is
what made bounded model checking and IC3 practical; QBF never got an
adopted equivalent. For booleanium the natural contract is:

    push / pop / add-clause / add-definition / solve(assumptions)
      -> verdict + Skolem functions valid for the current stack

**Reproducibility.** The solver is deterministic run to run, which it
was not: a recorded winning move was collected out of a hash set, and
Rust seeds its hasher per process, so the *order* of the move's literals
differed between runs of the same binary on the same instance. Callers
that minimize the move greedily then dropped different literals and
returned different (equally valid) moves, and anything built on top —
a game's winning region above all — became irreproducible. Measured on
one pursuit game before the fix: 71, 78, and 101 refinement rounds
across three runs, with wall times from 0.49 s to 7.67 s, which is
enough variance to invent or hide any effect a benchmark might be
looking for. Sorting the move fixed it, and incidentally found a better
refinement path than the average unsorted one: the same game settled at
66 rounds and 0.34 s.

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
* **Arbitrary alternation depth — done for verdicts.** The frontend
  used to parse at most `(forall (...) (exists (...) body))`; it now
  takes an alternating chain of any depth. Two-block sessions keep the
  2QBF core untouched (so the ∀∃ and ∃∀ shapes above are unchanged);
  deeper ones switch to `Mode::Deep`, where the session keeps its own
  prefix — built *positionally*, block `i` of any assertion joining
  block `i` of the session, which generalizes the two-block rule that
  all `forall` binders are universal and all `exists` binders inner —
  with free constants outermost and the gates innermost, and each check
  goes to the alternation front-end. That makes all three frontends
  consistent: QDIMACS, QCIR, and SMT-LIB now accept the depth the
  solver can handle.

  Validated by a differential proptest over 3–4 block prefixes against
  a recursive game oracle evaluating the same CNF body directly on the
  surface formula, 30k cases, plus hand-written four-block sessions
  either side of the boundary (an inner existential that can track the
  last universal, and the same body with it bound too early).

  **`get-model` for deep sessions — done** (`Strategy::to_smtlib`), by
  the route the previous note predicted: the composed strategy already
  builds an AIG for `to_aiger`, and an AIG prints as `define-fun`s
  almost directly — one internal definition per gate, one public
  definition per determined variable. Both formats therefore come out of
  the *same* structure and cannot disagree about what the strategy is.

  This also removes the caveat recorded further down about SMT-LIB
  models being validated only indirectly, at least for this emitter: the
  alternation fuzz now renders every composed strategy as SMT-LIB,
  *reads it back* with a small interpreter for the grammar the emitter
  uses (`and`, `not`, constants, parameters, calls to earlier
  definitions), and compares against `Strategy::evaluate` at every
  universal assignment — 200k cases, alongside the existing AIGER
  parse-and-simulate check and the SAT check. Three independent readings
  of the same strategy now have to agree.
* **Does eager bit-blasting re-lose word-level structure? — measured,
  and the framing was wrong** (`bench_encodings`, families
  `bv-add-inverse-n` and `bv-ult-choice-n`: an `n`-bit addition and an
  `n`-bit unsigned comparison, bit-blasted into gate definitions the way
  a BV frontend would, then rendered through the same three encodings as
  RQ1).

  | family | encoding | initially determinized | decisions | time |
  |---|---|---|---|---|
  | `bv-add-inverse-8` | qcir | **61/61** | 0 | 0.19 ms |
  | `bv-add-inverse-8` | two-sided | **61/61** | 0 | 0.23 ms |
  | `bv-add-inverse-8` | PG | 57/61 | 0 | 0.16 ms |
  | `bv-ult-choice-8` | qcir | 2/40 | 243 | 5.5 ms |
  | `bv-ult-choice-8` | two-sided | 2/40 | 286 | 8.1 ms |
  | `bv-ult-choice-8` | PG | 1/40 | **81** | **2.3 ms** |

  `∀a,b ∃y. a + y = b` bit-blasts to a ripple-carry chain and
  determinizes **completely, with zero decisions and zero conflicts** —
  and note that this requires *inverting* the adder, since the gates
  define the sum bits from `a` and `y`, not `y` from `a` and `b`.
  Nothing word-level is lost. The comparison under a disjunctive top
  determinizes 2 of 40 and degenerates into search, and PG is
  **2.4x faster** there with a third of the decisions.

  So the worry as posed — that BV structure survives at the word level
  but not after bit-blasting — is not what the numbers show. The
  predictor is the axis RQ1 already isolated: whether the top *forces*
  the output. An output-forced word operation bit-blasts into something
  ID reads straight through; a comparison under a choice-blocking top is
  the `choice-of-relation` family again, wearing bit-vector clothes.
  That is a useful negative for a BV frontend: it says the value of
  word-level input would not come from preserving arithmetic structure,
  which bit-blasting preserves fine, but from whatever else word-level
  reasoning buys (e.g. not enumerating a 2^n comparison), which is a
  theory-solver question and belongs to RQ4.
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
  **The extraction gap is closed**
  (`IncrementalSolver::universal_witness_complete`). The recorded
  witness candidate is heuristic — pure-literal assignments are
  winnability-preserving *choices*, not pointwise-forced values — so it
  is verified with one SAT call before exposure, and used to be
  discarded on failure, leaving `sat` without a model. The fallback is
  **self-reduction**: the stack is unsatisfiable, so *some* move wins;
  fix one universal variable at a time and ask whether the restriction
  is still unsatisfiable. If it is, that value stays; if not, the
  opposite value must win, because a winning region cannot vanish
  under a two-way split. Each step is one restricted solve on a
  throwaway core, so the continuation base is untouched, and the
  result is complete by construction — then minimized over whichever
  variables the caller says it can use (RQ5's region refinement wants
  the state variables dropped and the inputs kept).

  The instance being reduced is the one the *query* answered, not the
  bare stack: the solver remembers what each throwaway query added
  (temporary clauses, universal-domain restriction) and rebuilds
  against that, which is what makes the method usable from the
  synthesis path, where the assertion roots are negated into one
  temporary clause.

  Validated by extending the incremental differential harness: every
  unsatisfiable solve now also extracts a move and *replays* it — the
  instance restricted to the move must stay unsatisfiable under
  brute force — which is 12 575 winning moves checked over 30 000
  random push/pop/assert/query sessions, independent of the
  self-reduction that produced them.

  **A soundness bug the harness caught later, worth recording**, because
  it is a distinction that is easy to lose: the self-reduction narrows
  towards a winning move by asking "is the stack, restricted to this
  cube, still unsatisfiable?", and that question says only that *some*
  point of the cube wins. It is the right question for narrowing and the
  wrong one for *generalizing*: a caller that acts on the whole cube — a
  game excluding a region — needs *every* point of it to win. The
  minimization used the narrowing test and so could hand back a cube
  containing winning states. It now uses the strong one, the same plain
  SAT check `unsat_witness_minimized` applies: no completion of the
  universals admits any response.

  It stayed hidden until the determinism fix below changed which
  literals the greedy step dropped, which is the honest reason it was
  found — the harness had been running over it for two commits. The gap was theoretical for the
  SMT-LIB frontend but not elsewhere: RQ5's game refinement hit it
  immediately and had to carry a hand-rolled single-state backstop,
  which this replaces.

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
* **Determinacy does, and lifts *better* than it runs here** — this
  bullet used to say the opposite ("the clausal core does not"), on the
  grounds that watched literals, unique consequences and
  implication-clause resolution are Boolean. They are, but they are the
  *implementation*. The notion is "this constraint *defines* x given
  the earlier variables", and modulo a theory that is usually available
  syntactically — solving an equality in LIA, an invertibility
  condition in BV, congruence closure in EUF — where in CNF it has to
  be found by a SAT query per determinization. See "Where the two
  tracks meet" below for the counterexample that forced the correction,
  and for what genuinely does not lift (decisions become term
  proposals; proofs have no counterpart).
* **Measured warning on per-query cost**: the conflict-check workload
  is thousands of small incremental queries; even CaDiCaL and
  CryptoMiniSat lose to varisat on it (~6k vs ~9k conflicts/min on
  adder2). An SMT backend pays this severalfold. Any theory lift needs
  batching or a lazy design, not a drop-in backend swap (the
  `SatSolver` trait makes the naive swap a one-day experiment — worth
  running once, expecting it to lose, to get the number).

### Where the two tracks meet

The goal is games over *theories*; the entry ticket is being fast on
QDIMACS. Those look like competing demands and mostly are. They were
recorded here as sharing exactly one investment — clausal abstraction,
named as both the QDIMACS answer and the theory-liftable architecture —
and that was **wrong in the direction that matters**. The two tracks
share less than claimed, and the piece that lifts is the opposite one.

**The counterexample that settles it.** Take `∀x ∃y. x = y + 1` over
any theory with arithmetic. Clausal abstraction's interface between
quantifier blocks is a set of *clause-satisfaction indicators*: one
b-literal per clause, saying whether that clause is already satisfied
from the outside. Two properties make that work in QBF — the clause
set is finite and fixed, so the interface is a finite Boolean
vocabulary; and the only thing an outer assignment can do to the inner
player is satisfy some clauses, which is a *complete* summary, because
a clause is satisfied or it is not.

The second property is what breaks modulo a theory. Here there is one
clause holding one atom that mentions both blocks. It is satisfied by
no assignment to `x` alone and by no assignment to `y` alone, so its
b-literal reads the same for every `x` and carries no information at
all. Everything that matters about `x` is the *value* it hands to `y`,
and the abstraction has no vocabulary for values. Recovering
completeness means splitting the atom into a family of atoms over
values or intervals — reintroducing the domain — and then the
abstraction's defining property, a fixed finite clause set, is gone.

**ID's interface is the Skolem function itself**, which is a term in
the theory's language. `y := x - 1` is a well-formed object in LIA, in
BV, in EUF, and the two obligations ID places on it are theory
queries, not Boolean ones:

* *determinacy* — is `y` uniquely forced? `∃y₁ y₂. C(x, y₁) ∧ C(x, y₂)
  ∧ y₁ ≠ y₂` is unsatisfiable;
* *conflict-freedom* — are the accumulated definitions jointly
  consistent under every `x`?

And there is an inversion worth stating plainly, because it reverses
the bullet list above. In CNF, determinacy has to be **discovered by
search** — precisely the SAT-backed machinery this project spends
about one call per search step on. In a theory it is usually
**syntax**: solving `x = y + 1` for `y` is Gaussian elimination in
LIA, an invertibility condition in BV, congruence closure in EUF. The
expensive half of ID gets *cheaper* when it is lifted, not more
expensive. The old claim confused the implementation (watched
literals, implication-clause resolution) with the notion (unique
consequence = definitional determinacy). The implementation is
Boolean; the notion is not, and the notion is the algorithm.

**The Boolean measurement already agreed, and was read backwards.**
The bit-blasted form of the same shape — `bv-add-inverse-n`,
`∀a,b ∃y. a + y = b` — determinizes completely, and it scales:

| width | universal domain | initially determinized | decisions | conflicts | time |
|---|---|---|---|---|---|
| 4 | 2⁸ | 29/29 | 0 | 0 | 0.16 ms |
| 8 | 2¹⁶ | 61/61 | 0 | 0 | 0.19 ms |
| 16 | 2³² | 125/125 | 0 | 0 | 0.36 ms |
| 32 | 2⁶⁴ | 253/253 | 0 | 0 | 0.67 ms |
| 64 | 2¹²⁸ | **509/509** | **0** | **0** | **1.45 ms** |

Linear in the width, nothing enumerated, over a universal domain of
2¹²⁸ — and this requires *inverting* the adder, since the gates define
the sum from `a` and `y`, not `y` from `a` and `b`. It does **not**
show that clausal abstraction fails on the bit-blasted instance:
bit-blasting hands it a circuit full of inner Tseitin variables and
plenty of clauses to learn about, and how fast it is there is an open
empirical question this repo has not answered. What it shows is the
thing that matters for the lift — ID's advantage on definitional
structure is *not an artifact of word-level input*. It survives being
compiled down to CNF, so it is a property of the algorithm rather than
of the frontend, and that is what makes it worth carrying up into a
theory.

**So the corrected position.** Two investments, not one:

* **Clausal abstraction is the QDIMACS play**, and only that. It is
  still the right answer there, for the reason it always was — it
  contains both search and expansion in one calculus, which is why
  CAQE decided instances neither DepQBF nor RAReQS could. Nothing here
  argues against it as the way to be fast on the benchmark that buys
  attention.
* **ID is the theory-liftable trunk.** Its central object is a
  definition, which is exactly what a theory can represent and often
  what it can read off syntactically, and the game machinery already
  built on top of it — CEGAR, case splits, the frontier — was already
  judged to lift.

What still does not lift, stated so this is not a second over-claim in
the other direction:

* **Decisions.** When nothing is forced — `∀x ∃y. y > x` — ID has to
  *choose*, and over a theory a choice is not a coin flip between two
  polarities but a proposed **term**. That is the genuinely hard part,
  and it is syntax-guided synthesis / model-based projection territory
  rather than anything the current code hints at.
* **Proofs.** Learned clauses become theory lemmas; the QRAT emission
  has no obvious counterpart.
* **The per-call cost warning stands**, with its premise corrected. An
  SMT query is far more expensive than a varisat query, and it is paid
  about once per search step. But over a theory most of those calls are
  replaced by *syntactic* definition extraction — so what changes is
  not only the cost per call but the number of them, which is the one
  lever the Boolean measurements found to be shut.

**Which theory: bit-vectors, revising an earlier answer.** EUF is the
right answer to "what is determinacy modulo a theory" — `x = t` is
literally a definition and congruence closure is the analogue of
unique consequence. It is the wrong answer to "which theory makes
*games* pay". The bit-blasting measurement above already narrowed
that: arithmetic structure survives bit-blasting fine (the inverted
adder determinizes 61/61 with zero decisions), and what word-level
reasoning buys is *not enumerating* — the comparison family
degenerates into search at 2/40 determinized.

In a fixpoint, the place you enumerate is **the region**. A Boolean
safety game's winning region is a set of cubes that grows one cube per
round; `arbiter-4-4` needs 55. A bit-vector game's region is naturally
an interval or a word-level constraint, and the bit-blasted form of it
can be exponentially larger. That is the same "specialised algorithm
beats the generic solver" failure mode as everywhere else, located
precisely: not in the search, in the representation of the region.

Bit-vectors also keep the method intact, which EUF and LIA do not:

* games over BV are **decidable** (finite domain), so this is an
  algorithm rather than a semi-algorithm with an abstraction on top;
* the differential oracle is **free and exact** — bit-blast the game
  and run the existing Boolean path. Every result in this project
  rests on an oracle sharing no code with the thing under test, and
  here the project already contains one;
* the industrial case (word-level controller synthesis) is the one
  people actually have.

**The experiment that prices the prize — run, and it inverts the
hypothesis** (`bench_games region`, families `region-arbiter-k-b`).
The same arbiter game with each client's age held two ways: as the
existing unary shift register, and as a **binary counter**
(`binary_arbiter`) — the state encoding a bit-vector frontend would
produce. Three prices per row: the cubes the refinement loop actually
discovered, a near-minimal cube cover of the *true* losing region
computed without the solver (explicit backward fixpoint, greedy prime
implicants, greedy set cover), and what a word-level description would
be.

Holding `k = 2` and growing the deadline `b` — the axis a word-level
region is supposed to win on, since the unary state space grows with
`b` and the binary one with `log b`:

| `b` | unary latches / cubes / width | binary latches / cubes / width | ideal |
|---|---|---|---|
| 2 | 4 / 3 / 2.3 | 4 / 4 / 3.2 | 3 |
| 4 | 8 / 3 / 2.3 | 6 / 5 / 4.8 | 3 |
| 8 | 16 / 3 / 2.3 | 8 / 6 / 6.3 | 3 |
| 12 | 24 / 3 / 2.3 | 8 / 6 / 6.3 | 3 |
| 16 | 32 / 3 / 2.3 | 10 / 7 / 7.9 | 3 |

Three things, and the first kills the hypothesis as posed.

**There is no region blowup to rescue.** The true losing region needs
**3 cubes at every width, in both encodings**. The premise — that a
bit-blasted word-level region is exponentially larger as a cube set
than as an interval — is simply false here. Thresholds have short DNFs.

**The unary encoding is already optimal, and free.** It finds exactly
the 3-cube cover at every deadline, in 5 rounds, with mean cube width
2.3, while its state space grows to 2^32. The loop is completely
insensitive to the size of the state space. That is a *tooling* result
in the sharpest sense: the same game, written the way a hardware
designer would naturally encode control state, costs the generic
solver nothing.

**The binary encoding degrades with word width, and never reaches the
optimum.** Cubes 4 → 7 and mean width 3.2 → 7.9 as `b` goes 2 → 16 —
roughly one extra cube per additional bit — against an ideal of 3
throughout. At `k = 3, b = 3` the same split shows on the other axis:
unary finds 10 of an ideal 10, binary finds 15.

So the loop's generalization tracks **the state encoding, not the
state-space size**, and one-hot beats binary at it.

**What that does to the theory case.** It replaces a wrong argument
with a better one. The prize is not that the region needs fewer
constraints word-level — it needs three either way. The prize is that
*the loop cannot find the good region on binary-encoded data, and
unary is not available at real widths.* You can encode a deadline of
16 in unary with 32 latches; you cannot do that to a 32-bit counter,
and the binary trend measured above is what you are left with. A
word-level region would recover what unary hands the Boolean solver
for free at small widths.

That is a narrower claim than "theories make games tractable" and a
much better supported one. It also names the experiment that would
falsify it: a family whose region is intrinsically complex rather than
a threshold. This one's region is 3 cubes, which is exactly why it
isolates generalization so cleanly — and exactly why it cannot speak
to the other axis.

**Scheduling.** Preprocessing is the highest QDIMACS-per-hour item and
is largely independent of the architecture, so it can run in parallel
without prejudicing the theory design. The two-solver control below
and the region experiment above are both cheap and both feed the
architecture decision — the control says whether determinization earns
its keep on the game workload at all, which is exactly the input the
"ID as component, not trunk" question needs.

## RQ5 — Positioning: a building block for two-player games

An incremental ∀∃ solver that returns functions is the inner loop of
bounded synthesis and safety-game solving: the game unrolling depth maps
to push levels, the winning-strategy extraction maps to `get-model` (or
`SkolemModel::to_aiger` / CLI `--strategy`, which emits the functions as
an AIGER strategy circuit — see `PLAN.md` §2), and the incrementality
between depths is where the interface (RQ2/RQ3) earns its keep — none
of which a one-shot QDIMACS call can express.

### What this actually has to beat, and does not yet measure against

The standing complaint about QBF solvers is that a specialised
algorithm beats them on any problem someone cares enough to
specialise. The counter-thesis this project is really testing is that
this is a **tooling** result rather than a complexity one: given the
right abstraction, a developer should be able to write the fixpoint
against a quantified solver and land at or below the cost of the
hand-rolled alternative — and the hand-rolled alternative for a safety
game is not an unrolling. It is **two competing SAT solvers**: one
proposing a state and an uncontrollable move, one checking whether a
controllable answer exists, generalising in both directions. That loop
is what practitioners write, and it is what the abstraction has to
match.

Two consequences, and the second is a hole in the evaluation.

**The interface has to be circuit-level, not clausal.** The transition
relation is a circuit, it never changes, and the developer should hand
it over once as gates. What varies between rounds is only the region.
Today `solve_safety` builds its whole query through `add_clause`, and
`IncrementalSolver::define_and` is sugar that expands to the same
two-sided clauses — so the loop is hand-Tseitining a structure the
solver could have owned. The region in particular is a *linear chain*
of membership definitions, one link per round: 55 cubes means
propagating through a 55-deep disjunction, where a specialised tool
keeps the region canonical and shared. Nothing removes a cube that a
later, more general one subsumes, either.

**The control — run, and it loses badly** (`bench_games control`).
Everything measured before it compared this solver against *itself*:
unrolling versus region refinement (107x for refinement), in-place
versus rebuild (parity), one option set versus another. The control is
the same fixpoint driven by two competing SAT solvers over the same
circuit — a candidate solver proposing a state and an uncontrollable
move, a responder checking for a controllable answer, refinement by
instantiation, generalisation by the responder's unsatisfiable core.
It shares nothing with the solver: its own AIGER parser, its own CNF
encoding, varisat used directly. The verdicts are asserted equal on
every row.

| family | latches | booleanium | time | two solvers | time |
|---|---|---|---|---|---|
| `arbiter-2-2` | 4 | 5 r / 3 c | 1.8 ms | 4 r / 3 c | **0.17 ms** |
| `arbiter-2-8` | 16 | 5 r / 3 c | 4.3 ms | 4 r / 3 c | **0.21 ms** |
| `arbiter-3-2` | 6 | 10 r / 8 c | 8.4 ms | 10 r / 10 c | **0.56 ms** |
| `arbiter-3-3` | 9 | 12 r / 10 c | 50 ms | 11 r / 10 c | **0.72 ms** |
| `ring-4` | 8 | 17 r / 15 c | 19 ms | 5 r / 4 c | **0.39 ms** |
| `corridor-4-stay` | 8 | 34 r / 32 c | 524 ms | 22 r / 21 c | **2.7 ms** |
| `ring-6` | 12 | 66 r / 64 c | 238 ms | 7 r / 6 c | **0.67 ms** |

**11x to 356x, in favour of two SAT solvers.** That is the answer to
the positioning question, and it is not the one the rest of RQ5 was
heading towards. The 107x that region refinement won over the
unrolling was real, but it was a race against another of this
solver's own encodings.

The gap decomposes into two independent factors, and both are
actionable.

**Cube quality.** Priced against the near-minimal cover of the true
losing region (`bench_games region`, same method as above):

| family | ideal | two solvers | booleanium |
|---|---|---|---|
| `arbiter-3-3` | 10 | 10 | 10 |
| `ring-4` | 4 | **4** | 15 |
| `corridor-4-stay` | 20 | **21** | 32 |
| `ring-6` | 6 | **6** | 64 |

The control's generalisation is *optimal* on the pursuit games — it
finds the 4-cube and 6-cube covers exactly — while this solver finds
15 and 64. On the arbiter family both are optimal, which is why the
earlier region experiment, run only on arbiters, saw nothing wrong.

The mechanism is the difference. The control takes the responder's
**unsatisfiable core**: one SAT call, and the core is by construction
the subset the refutation needed. This solver takes a *complete*
self-reduced universal move and then drops literals greedily, each
drop paid for with a `move_is_unanswerable` check — and greedy
descent from a full assignment lands in a poor local minimum. The
antitonicity argument recorded above says a second pass cannot help;
it says nothing about the starting point, and the starting point
looked like the problem.

**Seeding from the core was the obvious fix, and it was measured and
rejected — twice.** `unsat_witness_minimized`'s verification solve
already computes a core and throws it away. Using it to pre-drop every
removable literal the refutation did not need, then running the greedy
pass over what survives, took `ring-6` from **238 ms to 15 s** (66
rounds and 64 cubes became 73 and 71). Keeping the shorter of the two
cubes — greedy from the complete move, greedy from the core — pays for
the extra pass and buys nothing: 477 ms on `ring-6`, every other family
a few percent slower. Both reverted.

**Why it does not transfer is worth more than the attempt.** The
control's core comes from a *different query*: "from this state, under
this uncontrollable move, can the controller avoid the error and stay
in the region?", with only state and input literals assumed. That
formula is small, and its core is exactly the state bits the refutation
needed. This solver's verification solve is over the whole loaded
instance — matrix, region chain, the round's constraint, the caller's
query assumptions — with the *complete* universal witness assumed, and
a core of that carries no comparable signal.

So the cube-quality half of the gap is not an extraction problem, it is
an **interface** problem: generalising like the control requires being
asked the control's question, which means being told what the region
*is* rather than receiving it as undifferentiated clauses. That is the
circuit-level interface above, now with a second independent
measurement pointing at it.

### The interface, built — and the port that does not pay yet

The solver accepts terms now (`Node`, `and`/`or`/`xor`/`ite`,
`assert_node`, `named`), Tseitin-encodes them itself, and keeps the
variables that takes to itself (`is_auxiliary`). A caller that hands
over a circuit no longer puts its gate variables in the same namespace
as the variables it quantifies over. On top of that sits the
generalisation primitive the measurement above asked for:
`unanswerable_core(depth, universal, question)` — "is this universal
move answerable, and if not, which of its literals did the refutation
need", asked against *a term the caller names* rather than against
everything the solver holds.

Porting `solve_safety` onto it deletes the hand-rolled encoding and
the special-cased responder outright. It also, measured on one
machine against the pre-port code, **costs time**:

| family | hand-rolled | on terms | on terms, signals named |
|---|---|---|---|
| `arbiter-3-2` | 11 r / 9 c / 17.7 ms | 12 r / 10 c / 33 ms | **8 r / 1 c / 8.9 ms** |
| `arbiter-3-3` | 12 r / 10 c / 32.4 ms | 12 r / 10 c / 225 ms | 12 r / 10 c / 208 ms |
| `ring-4` | 6 r / 4 c / 8.7 ms | 6 r / 4 c / 21 ms | 6 r / 4 c / 19 ms |
| `ring-6` | 8 r / 6 c / 18.0 ms | 8 r / 6 c / 23 ms | 8 r / 6 c / 21 ms |
| `corridor-4-stay` | 23 r / 21 c / 115 ms | 22 r / 20 c / 302 ms | 23 r / 21 c / 194 ms |

The middle column is the naive port; the right one adds `named` on the
successor bits and the region terms, which the hand-rolled version had
as variables. That recovers a lot — `arbiter-3-2` finds a **one-cube**
region where every other configuration needs nine or ten — and the
finding behind it is worth keeping:

**For incremental determinization, naming an intermediate signal is not
overhead, it is the substrate.** A term interface that folds and shares
aggressively, as an SMT frontend should, dissolves exactly the named
definitions the solver determinizes, propagates through, and extracts
Skolem functions for. `named` is therefore not a wart on the API but
part of it, and the open question is which signals deserve it — the
hand-rolled encoding answered that by accident, and the port has to
answer it on purpose.

That first attempt did not pay — `arbiter-3-3` 6x slower, two more
families 2x — and was not landed. **Two causes, both found, and the
port then landed.**

**Cause one: k-ary terms.** A `k`-ary conjunction
folded into binary gates costs `k - 1` existentials, and the port
builds one per cube per round, twice — over the state and over the
successor — where the hand-rolled `link` built exactly one variable
each. On a nine-latch game with cubes around six literals wide that is
roughly ten new variables a round against two, every one of them
something the solver has to determinize and propagate through.
`and_all`/`or_all` now allocate a single variable with `k + 1` clauses,
which is what a hand-written encoding would have done, with the wide
term structurally shared like the binary ones. Pinned by a test that
counts the variables, since the property is invisible from the outside
and easy to lose.

This is the same lesson as `named` from the other side: a term
interface is free to be clever about *sharing*, and must not be clever
about *dissolving*. Both mistakes hand incremental determinization a
worse instance than the caller wrote.

**Cause two: the successor bits.** They were variables in the
hand-rolled encoding and terms in the first port, which is the `named`
finding again — the region speaks about them every round, and a signal
without a variable is one the solver cannot determinize, propagate
through, or record a function for. Keeping them declared costs two
clauses each and buys back most of what the port had lost.

**With both, the port is net faster and it is landed.** Same machine,
against the hand-rolled encoding it replaces:

| family | hand-rolled | on terms |
|---|---|---|
| `arbiter-3-2` | 11 r / 9 c / 16.5 ms | 12 r / 10 c / 21.2 ms |
| `arbiter-3-3` | 12 r / 10 c / 30.4 ms | 12 r / 10 c / 38.0 ms |
| `ring-4` | 6 r / 4 c / 8.6 ms | 6 r / 4 c / **7.9 ms** |
| `ring-6` | 8 r / 6 c / 17.7 ms | 8 r / 6 c / 18.5 ms |
| `corridor-4-stay` | 23 r / 21 c / 115.5 ms | 22 r / 20 c / **68.4 ms** |
| total | 188.7 ms | **154.0 ms** |

`corridor-4-stay`, the family that dominates the set, is 1.7x faster
and finds the **ideal** 20-cube region where the hand-rolled version
found 21. The two arbiters cost ~25%, within the trajectory swing this
loop shows whenever variable numbering moves — the same instance has
been seen at one cube and at ten across these ports.

What the port removes is the point: `solve_safety` no longer allocates
a gate variable, writes a Tseitin clause, or carries its own mirror of
the circuit for generalisation. It builds terms, names the signals it
wants to talk about, and asks `unanswerable_core` about the question it
just built. 128 lines of encoding became 69.

**And the same port applied to the *unrolling* is a regression, which
is the useful control.** `Unroller::step` hand-rolls the same Tseitin
encoding, and moving it onto terms changes nothing else — there is no
duplicated mirror to delete and no query to improve. Measured on the
bounded-safety families:

| | hand-rolled | on terms | on terms, error named |
|---|---|---|---|
| `arbiter-2-2` depth 16, in place | 785 ms | 580 ms | 939 ms |
| `arbiter-2-2` depth 16, rebuild | 414 ms | 558 ms | 668 ms |
| `arbiter-2-2` probed 12, in place | 319 ms | 318 ms | 311 ms |
| `arbiter-2-2` probed 12, rebuild | 266 ms | 353 ms | 306 ms |
| in-place monotone extensions | 1 | **0** | 1 |

The middle column loses the in-place extension outright: asserting
`!error` on a term flattens into a disjunction over the gate's inputs,
where the hand-rolled version asserted a *unit* on a named output.
Naming the error signal restores the extension and costs 25% instead.
Neither is a win, so the unrolling keeps its own encoding.

The contrast with `solve_safety` is the finding. Replacing a
hand-rolled Tseitin encoding with the term interface is **not free** —
it costs 0–25% here — and it pays only where it also removes duplicated
work or enables a better question. `solve_safety` gained because the
port deleted a second copy of the circuit and let the generalisation
name its query; the unrolling has neither, and pays the encoding cost
with nothing to set against it. A term interface is the right *shape*
for a frontend; it is not automatically the right implementation of one.

**The SMT-LIB frontend needs no port at all, and reviewing it found a
bug in the new interface.** `smtlib::and_gate` already hash-conses on a
structural key, folds constants and complementary pairs, and emits one
variable per `k`-ary conjunction through `define_and` — everything the
term interface offers, written by hand two research questions ago. But
it keeps its gate cache **per frame** and looks it up across the live
stack, where the term interface kept two flat maps and cleared them
wholesale on any `pop`. So every pop threw away all sharing and made
the caller re-encode terms it had already written — on a loop that
pushes and pops once a round, which is every caller this interface has.

The cache is per frame now, keyed uniformly by the sorted inputs so
binary and wide gates share one table, and a pop retires exactly the
gates its own frame owned. The constant moved to the base frame, since
gates encoded against it must not outlive it. Pinned by a test that
builds a term, pushes, builds another, pops, and checks the first is
still shared.

Worth recording as a pattern rather than an incident: the new interface
was written from scratch against the *idea* of what a term API should
do, while the code it was meant to replace had already solved the same
problem correctly. Reading the older implementation first would have
been faster than measuring the newer one twice.

**Per-round cost.** `arbiter-3-3` runs 12 rounds against the control's
11 and finds the same 10 cubes, and still takes 70x longer. So even
with cube quality equalised there is an order of magnitude in the
round itself — consistent with the conflict-check profile below, where
81% of the complete checks prove there is no conflict.

**What this says about determinization.** Booleanium's CEGAR
conflict resolution *is* the two-solver loop, with determinization
layered on top. On this workload the layer is not paying for itself.
That is a narrow claim — safety-game rounds are shallow ∀∃ queries
over a circuit, which is the case CEGAR alone handles well, and it
says nothing about the instances where determinization wins outright
(`adder2`, the `stmt` family). But it is exactly the workload the
theory ambition runs through, and it argues for ID as a component
that earns its place per-instance rather than as the trunk.

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
  satisfiable and correctly rejected. A causal bounded strategy
  certifies the bound only; the unbounded question is answered by the
  winning-region refinement below, which needs no inductive argument
  on top because the fixpoint *is* the argument.
* **The winning-region refinement — the shape the incremental
  interface was actually built for** (`aiger::solve_safety`). Both
  encodings above unroll the game to a *depth*, so they answer a
  bounded question and pay for it in prefix length or strategy size.
  The classical alternative does not unroll at all: start with the
  winning region `W` as every state, ask "from every state of `W`,
  whatever the environment plays, can the controller avoid the error
  and stay in `W`?", and on failure take the counterexample state out
  of `W` and ask again, until `W = CPre(W)`. The controller wins iff
  the initial state survived.

  Everything about that loop suits this solver. The query is
  `∀ state, uncontrollable. ∃ controllable` — **2QBF whatever the
  game's depth**, so the whole RQ6 machinery is not even needed. The
  counterexample is the core's own *verified universal witness*, which
  arrives already minimized, so a whole cube of states leaves `W` per
  round for free. And every refinement is an *addition* — fresh
  membership variables, fresh clauses, the previous round's constraint
  retired by a unit on its activation literal — so nothing is ever
  rewritten and the in-place monotone continuation applies to the
  entire run. The answer is *unbounded* realizability with a winning
  region, not a bounded approximation with a depth-limited strategy.

  The loop runs in two phases, the classical order: first ask only
  "can the controller avoid the error *now*", whose fixpoint is the
  set of **safe states** `CPre(⊤)`, then start the backward induction
  from there rather than from the whole state space. The phase-one
  query never mentions the successor, so it is the smaller formula.

  The witness minimization is **aimed at the state variables**
  (`IncDet::unsat_witness_minimized`). Which literals a winning move
  keeps is not aesthetics for a caller that uses only part of the
  assignment: the region refinement projects the move onto the states
  and throws the environment's input away, so every state literal
  dropped *doubles* the set of states excluded that round, while
  dropping an input literal buys nothing — and costs, because a more
  specific environment move defeats more states. Marking the state
  variables removable and the inputs not aims the greedy minimization
  at exactly the generalization the caller can use, at one SAT call
  per candidate.

  Each round's constraint lives in a **pushed frame** and is popped
  once answered, rather than being retired by an activation literal.
  The difference is what happens to what was learnt under it: with a
  guard, every clause learnt while the round's constraint was active
  stayed in the database for the rest of the run, referring to a
  literal that could never fire again. Popping drops exactly those and
  keeps what was learnt about the circuit and the region.

  | game | verdict | rounds (safe) | cubes | in-place | rebuild |
  |---|---|---|---|---|---|
  | `arbiter-2-2` | realizable | 5 (3) | 3 | 2.0 ms | 1.7 ms |
  | `arbiter-3-2` | unrealizable | 10 (4) | 8 | 7.7 ms | 7.7 ms |
  | `ring-4` | realizable | 17 (16) | 15 | 49.3 ms | 35.0 ms |
  | `corridor-4-stay` | realizable | 35 (17) | 33 | 185 ms | 163 ms |

  That is the whole benchmark from **126.1 s to 1.18 s, 107x** (and to
  0.45 s with the frames below), and it
  is not a constant factor on the same search — the rounds collapse
  because the cubes are genuinely more general: `ring-4`'s losing
  region needs **15 cubes instead of 112**, and its 113 safe-state
  rounds become 16. Where the previous section said the loop was
  "spending nearly the entire computation rediscovering a syntactic
  state predicate one cube at a time", it now discovers it in cubes
  large enough that a symbolic seed would save comparatively little.

  Against the unrolling the positioning is stark: `arbiter-2-2` is
  decided **unboundedly in 1.9 ms with a three-cube winning region**,
  where the reactive unrolling spent 1.3 s to certify depth 11 alone —
  with a twelve-million-node strategy — and 101 s for depth 12.

  Stratifying into the two phases was worth doing but not for the
  reason expected. It does *not* cut rounds — one per game, the phase
  switch — because starting from `⊤` already makes the successor
  conjunct vacuous, so the original loop was computing the safe states
  first anyway, and its effect on time was large and two-sided. What
  it bought was *visibility*: it showed that 113 of `ring-4`'s 114
  rounds were safe-state rounds, which is what identified the witness
  as the thing to fix. Aimed minimization then cut those 113 rounds to
  16. The phase split is kept because it is the honest structure and
  it keeps that number measurable, not because it is worth a factor.

  **Where the in-place mode was losing.** Before the frames, rebuild
  beat in-place by 2–3x, which is backwards for the one access pattern
  the interface was designed for. Two guesses were wrong and the probe
  said so: the fallback path fires almost never (0 rounds on three of
  the four games), and witness minimization costs ~1.5 ms against
  185 ms of solving. Timing the phases separately put essentially all
  of the gap in `solve` itself — and the gap grew with the round
  count, which pointed at the clause database rather than at any
  particular check. It was the activation literals. Moving the round's
  constraint into a pushed frame took `ring-4` in-place from 188 ms to
  49 ms (3.8x) and the whole benchmark from 1.07 s to 0.45 s, and it
  also *improved the search*: `arbiter-3-2` now needs 10 rounds and 8
  cubes where it needed 12 and 10, because the solver is no longer
  reasoning around dead clauses.

  What is left is parity, not a win: rebuild is still 0–40% ahead, and
  the in-place path performs **zero monotone extensions** in this loop,
  because every round changes the base frame. So the continuation is
  not yet earning its keep here — but it is no longer pathological,
  and the remaining gap is bookkeeping rather than a leak. Making the
  region links extendable in place, so the base can grow without
  invalidating the frame, is the next thing to try. That is consistent with what RQ2
  already measured — in-place extensions stop once the first case is
  recorded, after which both modes do the same learnt-seeded work and
  differ by trajectory variance — but here the loop is exactly the
  access pattern the interface was designed for, so "the right shape
  does not yet pay" is a live finding rather than a footnote. The
  first thing to look at is the fallback path: when a refutation
  arrives without a verifiable witness, the loop proves a single state
  losing with universal-assumption queries, and those run on throwaway
  solvers.

  Validated by a differential proptest over 20 000 random sequential
  circuits: not just the verdict but the *whole winning region* is
  compared against an explicit backward fixpoint over the state space,
  which shares no code with the solver.

  **What the generalization bug cost, on a real game.** The proptest
  found the soundness bug in cube generalization (a minimized move was
  accepted on the strength of "the QBF restriction is still
  unsatisfiable", which says *some* point of the cube wins, not every
  point — the fix is a plain SAT query over the matrix). The benchmark
  shows what it was worth. `arbiter-4-4` — four requesters, each lost
  after four consecutive steps of asking without a grant, grants that
  may not overlap — used to come back **unrealizable in 21 ms with a
  single cube**. It is realizable: round-robin answers every requester
  every fourth step, so the wait is exactly three, and the game sits
  precisely on the boundary `n = b`. The over-general cube swallowed
  the states that make the schedule work. It now returns realizable
  after 57 rounds and 55 cubes, confirmed against the explicit
  fixpoint over all 2^16 states
  (`aiger::test::safety_arbiter_4_4_is_realizable`, ignored by default
  — the fixpoint sweep and the solve both run for minutes).

  **Re-measured after the generalisation work: 63 rounds, 61 cubes,
  465 s** (the 753 s was on a different container, so read the
  improvement loosely). The two-solver control decides the same game in
  **22 ms**, with 55 rounds and 54 cubes.

  That is a **20 000x** gap, the largest anywhere in this project, and
  the cube counts say it is not the region: 61 against 54 is close, and
  the generalisation work that fixed `ring-6` did what it could here
  too. Every bit of the gap is per-round solve cost. `arbiter-4-4` is
  therefore the instance to hold up against any future work on the
  core — it is the one where this solver's central mechanism is most
  visibly not earning its place.

  The instructive part is the cost profile: **21 ms wrong, 753 s
  right.** The bug was not making the solver look good on easy games,
  it was making it skip the game. Every other family kept its verdict
  and its round count, so nothing else in the benchmark was resting on
  it — but nothing in the benchmark would have caught it either, which
  is why the random-circuit proptest is where soundness is actually
  decided.

  **Where those 753 seconds go, and where they do not.** The instance
  is now the benchmark's one genuinely expensive game, so it is worth
  taking apart. Per-round tracing
  (`RUST_LOG=booleanium=debug`) says the refinement loop is not the
  cost: witness extraction is ~0.8 ms a round, **0.1% of the run**, and
  a typical round's solve is 10–130 ms. The run is dominated by a
  handful of rounds that hand the 2QBF core a hard query — one round of
  57 spends **59.9 s** inside `solve`, with 26 499 decisions, 8 023
  conflicts and 42 472 global conflict checks. Those are exactly the
  rounds that fall back to self-reduction: the refutation arrives
  without a recorded universal move, because it came from deep clause
  learning rather than from a conflict check.

  The cubes are not the problem either, and this one is provable rather
  than measured: the greedy minimization is already at a local minimum
  after one pass, because `move_is_unanswerable` is antitone in cube
  size — a literal that could not be dropped from a larger cube can
  never be dropped from a smaller one, so a second pass cannot find
  anything. The growth from 1–6 literals in the safe phase to 15–18
  under induction is a property of the region, not of the minimizer.

  **The core's own extensions were then A/B-ed on it**
  (`BENCH_RESTARTS`, `BENCH_NO_CASE_SPLITS`, `BENCH_NO_CEGAR` on
  `bench_games`), which is worth doing because the refinement loop
  drives the core very differently from the 2QBF corpora the defaults
  were fitted on, and because that hard round reports 0 restarts and 54
  case-split assumptions of which **0 were ever closed**:

  | configuration | in-place | rebuild | rounds | cubes | fallback |
  |---|---|---|---|---|---|
  | default | 753 s | 761 s | 57 | 55 | 8 |
  | `restarts` | 685 s | 609 s | 57 | 55 | 8 |
  | `no case splits` | **5 550 s** | — | 56 | 54 | 3 |
  | `no cegar` | 914 s | 829 s | 58 | 56 | 17 |

  (All five runs shared four cores, so the absolute numbers are
  uniformly inflated; the ratios are the content.)

  **The defaults win, and two of the three answers are informative.**
  Case splits are worth **7x** here despite closing none of their
  cases — the "0 closed" statistic measures completed cases, not
  useful ones, and reading it as churn would have been exactly wrong.
  CEGAR is worth ~20% and, more tellingly, halves the fallback rounds
  from 17 to 8: it is CEGAR that produces the conflicting assignments
  the loop reads as winning moves, so without it the loop has to
  reconstruct them by self-reduction. Restarts change nothing at all —
  not just the wall time but the *trajectory*: identical rounds,
  cubes, and fallbacks, which says the schedule never alters what the
  search finds on these queries.

  So the 753 s is not a tuning failure and not a loop-shape failure.
  It is the core's search on the induction queries, and improving it
  is a 2QBF problem, not a game problem.

  **Which part of the core.** Timing the two check paths separately
  (`SkolemStats::det_check_time`, `global_check_time`) answers that
  directly. The hard round, twice, on an otherwise idle machine:

  | phase | time | share | calls | per call |
  |---|---|---|---|---|
  | complete conflict check | **37.8 s** | **72%** | 42 472 | 890 µs |
  | determinacy check | 9.9 s | 19% | 660 196 | 15 µs |
  | propagation, analysis, CEGAR | 4.8 s | 9% | | |

  (The other run: 50.8 s total, 36.1 s and 10.0 s — the split is
  stable.)

  The budgeted micro-DPLL that replaced a SAT solver in the determinacy
  check is doing its job: 660 196 calls for 10 s, 15 µs each. The
  complete conflict check is where the round lives, and the shape of
  its cost is the interesting part — 42 472 calls yield only 8 023
  conflicts, so **81% of the expensive calls prove that there is no
  conflict**. The cheap syntactic filter in front of it
  (`may_be_conflicted`) admits 42 472 of 52 788 candidates: it rejects
  only 20%.

  That makes the target concrete for the first time. Not "the core is
  slow on this game" but *the negative complete checks*, and there are
  two ways at them — a stronger filter in front of the solver, or a
  cheaper call behind it. One candidate for the second is already
  ruled out: the level guards passed as assumptions average **10.3 per
  call** (437 988 over 42 472), so assumption handling is not where
  the 890 µs goes.

  **The same shape on a different family, and a correction.** The
  finding above came from one hard round of `arbiter-4-4`. Summed over
  every round of `corridor-4-stay` — a different game, measured after
  the generalisation and the term interface changed how the loop drives
  the core — the complete check is **46% of core solve time** over
  1 257 calls, of which 1 073 (**85%**) find no conflict. (An earlier
  draft of this paragraph reported 62% over 6 552 calls; that came from
  an aggregation that double-counted the nested statistics dumps of the
  throwaway query solvers. The figures here reproduce across runs.)

  **But splitting that time by outcome changes what to do about it**,
  and it is worth the paragraph because the obvious reading of "85% of
  the calls prove nothing is there" is wrong:

  | | calls | time | per call |
  |---|---|---|---|
  | finds no conflict | 1 073 (85%) | 19.0 ms (**47%**) | 17.7 µs |
  | finds one | 184 (15%) | 21.9 ms (**53%**) | 118.9 µs |

  The negative checks are many and *cheap*; the positive ones are few
  and **6.7x more expensive each**. A perfect filter — one that skipped
  every check destined to find nothing, for free — would save 19 ms of
  an 88 ms core solve, about **20%**. The remaining time is in the
  checks that do the work, which no filter can remove because finding
  the conflict *is* the work.

  **And the obvious way to remove calls was tried and is already
  done.** A variable whose implication clauses are a two-sided
  definition — `x <-> a & b` and its dual — *cannot* be conflicted: the
  forced-true condition is `a & b`, the forced-false one `!a | !b`, and
  they are mutually exclusive by construction. So the check is only
  needed where determinacy was *derived*, never where it was
  *declared*, and on circuit-derived instances most existentials are
  declared. That looked like most of the calls gone.

  It is worth nothing, because `may_be_conflicted` already does it. On
  `corridor-4-stay`:

  | | count | share of candidates |
  |---|---|---|
  | conflict-check candidates | 6 195 | |
  | of those, two-sided definitions | 4 542 | **73%** |
  | reaching the SAT check | 1 257 | 20% |
  | of those, definitions | **0** | **0%** |

  The cheap syntactic filter rejects every single definition, for the
  same structural reason that makes them conflict-free: the two sides
  always clash on a literal, so no compatible pair exists to test. What
  survives the filter is exactly the derived, genuinely uncertain
  variables. The filter is not weak — 80% rejection looked unambitious
  and is in fact near-complete on the population it can decide
  syntactically.

  **Do conflicts cluster? Yes, but not enough to answer with.** The
  next idea was to find conflicts by evaluation instead of search,
  since the expensive half of the check is exactly model-finding. The
  cheapest version of that uses previous conflicting assignments as the
  samples, on the guess that conflicts cluster. Measured — remembering
  the last 16 and asking whether any of them already makes both
  polarities of the candidate fire:

  | family | conflicts | witness right | wrong | recall | precision |
  |---|---|---|---|---|---|
  | `corridor-4-stay` | 184 | 122 | 475 | **66%** | 20% |
  | `ring-6` | 58 | 44 | 360 | **76%** | 11% |
  | `arbiter-3-3` | 182 | 91 | 477 | **50%** | 16% |

  **The clustering is real**: a remembered assignment witnesses half to
  three quarters of all conflicts. But the precision is 11–20%, four to
  nine false claims per true one, and the reason is instructive — the
  test asks only whether both polarities *fire* under the assignment,
  not whether the assignment is still *consistent* with everything the
  solver has determined since it was recorded. Making it sound means
  checking consistency against the current Skolem functions, which is
  the propagation the SAT call was going to do anyway.

  So the remembered assignment is a **hint, not an answer**. The next
  question was what a hint is worth, and the answer corrects the
  optimistic reading above: **it is worth nothing, and the 50–76%
  recall was measuring the wrong thing.**

  There is a way to use a hint soundly that needs no backend support at
  all. Pinning the remembered universals as *assumptions* only
  restricts the query, so a model found under them is a real conflict,
  and an unsatisfiable answer costs one cheap solve before the full one
  runs — a sound version of "simulate before you solve", executed
  inside the solver where consistency comes for free. Implemented
  (`Options::conflict_hints`, `try_conflict_hints`) and measured:

  | family | hints tried | hit | pinning |
  |---|---|---|---|
  | `corridor-4-stay` | 1 107 | 30 (**3%**) | whole assignment |
  | `ring-6` | 639 | 0 (**0%**) | whole assignment |
  | `arbiter-3-3` | 2 370 | 56 (**2%**) | whole assignment |
  | `corridor-4-stay` | 589 | 70 (**12%**) | local universals only |
  | `ring-6` | 309 | 1 (**0%**) | local universals only |
  | `arbiter-3-3` | 804 | 52 (**6%**) | local universals only |

  Trying all sixteen remembered assignments instead of the newest drops
  the rate further (120 hits in 35 688 tries on the corridor): the
  extra candidates are older and staler, not better. Restricting the
  pin to the universals the checked variable's own implications mention
  — a much weaker restriction, which should have been the generous
  version — reaches 12% at best.

  **Why the syntactic probe was so much more optimistic**: it asked
  only whether both polarities *fire* under the remembered assignment,
  and firing is the easy half. The hard half is that the assignment
  must still be consistent with everything the solver has determined
  since — and the reason it usually is not is structural, not
  incidental. The assignment was remembered *because* it conflicted,
  and a conflict is immediately followed by analysis that learns a
  clause, or by a CEGAR round that records a handled case excluding
  exactly that universal cube. The search's response to a conflict is
  to make that assignment impossible. Re-trying it asks the solver to
  reproduce the one thing it has just ruled out, which is why the sound
  rate is 0–12% where the unsound one was 50–76%.

  End to end it is a **regression**, three runs each, hints on vs off:

  | family | off | on |
  |---|---|---|
  | `corridor-4-stay` | 65.2 / 70.2 / 63.9 ms | 187.2 / 106.2 / 162.0 ms |
  | `ring-6` | 17.5 / 19.5 / 21.7 ms | 19.2 / 19.6 / 19.1 ms |
  | `arbiter-3-3` | 39.5 / 36.9 / 36.9 ms | 39.8 / 28.9 / 51.7 ms |

  Two costs, and the second is the interesting one. The obvious cost is
  the extra unsatisfiable solve on the ~90% of checks the hint misses.
  The subtle one is that a *hit* is not free either: the model found
  under a pinned assignment is more constrained than the one free
  search would have found, so it generalizes to a worse cube, and the
  corridor's 2.5x slowdown is mostly this. A biased conflict is a worse
  conflict.

  So the whole "conflicts cluster" line is closed, and closed on its
  own merits rather than parked on a backend limitation: phase-seeding
  would be a weaker version of the same hint, and the hint is wrong
  almost always and harmful when right. Kept behind
  `Options::conflict_hints` (default off, nothing recorded unless it is
  set) so the measurement can be repeated.

  **Is the query local? Not where it costs.** The other cheap idea was
  to make each check *smaller* rather than to ask for fewer of them:
  the check solver carries the whole determinized formula, but a
  conflict on `v` can only depend on the implication clauses reachable
  from `v` — its own, closed under the variables they mention. If that
  cone were a small part of the formula, a scoped query would be a
  constant factor on both directions at once. Measured (behind
  `probe`, `check_cone`, one sample per complete check):

  | family | checks | cone clauses | cone vars |
  |---|---|---|---|
  | `arbiter-2-2` | 109 | 26/40 (65%) | 14/17 (84%) |
  | `arbiter-2-8` | 180 | 23/57 (40%) | 13/24 (55%) |
  | `arbiter-2-16` | 199 | 17/77 (**22%**) | 11/37 (29%) |
  | `ring-6` | 644 | 122/181 (68%) | 52/59 (88%) |
  | `corridor-4-stay` | 1 257 | 234/306 (76%) | 81/95 (85%) |
  | `arbiter-3-3` | 1 222 | 61/107 (58%) | 28/39 (73%) |
  | `arbiter-4-4` | 247 876 | 762/905 (**84%**) | 136/152 (90%) |

  The locality is real and it *scales the right way* on the family
  built to grow: holding the arbiter at two clients and stretching the
  deadline from 2 to 16 leaves the cone flat in absolute size (26 → 17
  clauses) while the formula doubles, so the share falls from 65% to
  22%. That is the signature you want.

  It is on the wrong axis. The share is highest exactly where the check
  is expensive — 84% on `arbiter-4-4`, the family that costs two
  minutes and 248 000 complete checks, and 76% and 68% on the corridor
  and the ring. The instances where the cone is small are the ones that
  solve in 9 ms. Scoping would trim a sixth of the clause database on
  the instances that need help, and to *realize* the trim the check
  solver would have to be rebuilt per query, which is the
  non-incremental path that was already measured slower. So: not
  implemented. The measurement stays behind `probe`, because the
  trend is worth re-testing on a family with genuinely independent
  subsystems — the games here are all one connected fixpoint, which is
  precisely why everything is in everyone's cone.

  **Can the checks be batched? There is no batch.** The last idea in
  the family was the real CDCL analogy: stop checking each
  determinization before committing it, commit optimistically, and ask
  once per epoch whether *any* determinized variable is conflicted —
  one query with a selector per variable, the model naming the guilty
  one, the repair being the backtrack conflict analysis already does.
  The appeal is that it collapses the negative direction, 85% of calls
  and 47% of the time at 17.7 µs each, most of which is per-call
  overhead rather than search: a thousand cheap queries become one.

  It needs a batch to exist. The soundest epoch boundary is the
  propagation wave (checking before anything is concluded), the
  coarsest defensible one is the decision. Measured at both:

  | family | waves | complete checks | per wave | per decision | waves ending on a conflict |
  |---|---|---|---|---|---|
  | `corridor-4-stay` | 679 | 1 257 | 1.9 | 2.4 | 23% |
  | `ring-6` | 155 | 644 | 4.2 | 6.5 | 34% |
  | `arbiter-3-3` | 1 182 | 1 222 | 1.0 | 1.1 | 9% |
  | `arbiter-2-16` | 333 | 199 | 0.6 | 0.7 | 7% |
  | `arbiter-4-4` | 188 119 | 247 876 | 1.3 | 1.4 | 5% |

  **About one complete check per decision.** On `arbiter-3-3` and
  `arbiter-2-16` the batch would hold a single query, and on
  `arbiter-4-4` — 248 000 checks, the family that costs a minute and a
  half and the one this was meant to rescue — it holds 1.4. The best
  case is the ring at 6.5, where 34% of waves end on a conflict, which
  forces the batch to be re-run after the repair. There is nothing to
  amortize.

  That is the real answer to "the conflict check is too expensive", and
  it is not an answer about the check. Incremental determinization
  spends **one SAT call per search step** — the check is the algorithm's
  unit of work, not an overhead sitting on top of it. CDCL's per-step
  obligation is unit propagation, which is linear and searchless;
  ID's is "this Skolem function is well defined", which is a
  satisfiability question by its nature. The three experiments closed
  here say the same thing from three directions: the query cannot be
  made local (the cone is 56–84% where it matters), it cannot be
  guessed (hints hit 0–12%, and hitting is itself harmful), and it
  cannot be batched (one per decision). What is left is either a
  cheaper backend per call, or an algorithm whose per-step obligation is
  weaker — which is exactly what clausal abstraction is, and it is
  the QDIMACS answer recorded above. ID's beauty and its price are the
  same property.

  **A cheaper backend per call, taken seriously: BDDs.** That was the
  half of the conclusion left hanging, and it is the one with a real
  precedent — BDD-based solvers dominated SYNTCOMP's safety track for
  years while SAT-based ones were not competitive, which is the same
  problem shape this project's RQ5 track is losing at. The idea is not
  "call a BDD library instead of varisat" but to change what a Skolem
  function *is*: carry each one as a BDD over the universal variables,
  built by composition as determinization proceeds. Then

  * the conflict check is `fire_pos ∧ fire_neg ≠ ⊥`, a **pointer
    comparison** after a handful of applies;
  * the conflicting *set* comes out whole rather than one assignment at
    a time — and cube quality is worth a great deal here, since
    generalising `ring-6`'s counterexamples from 64 cubes to the ideal
    6 was one of the larger wins in the RQ5 track. A BDD hands you the
    ideal cube by prime-implicant extraction, for free;
  * determinacy, constant detection and certification collapse into
    the same representation — the strategy *is* the BDD, so the AIG
    compilation and its relevance-keyed memo stop being needed.

  So the whole question is representation size, and nothing else. That
  is measurable, so it was measured (`src/bdd.rs`, a minimal ROBDD
  package written for this: unique table, memoised apply, node budget,
  no reordering). Skolem functions of the RQ1/RQ3 families, largest
  single function, in prefix order and in the order interleaving the
  two halves of the universal block:

  | family | prefix order | interleaved | ID's own cost |
  |---|---|---|---|
  | `parity-eq-64` | 129 | 129 | 0.38 ms |
  | `mux-tree-5` | 65 | 75 | 0.28 ms |
  | `choice-16` | 5 | 5 | 23 ms |
  | `random-6-10-40-*` | 6–13 | 6–11 | 0.6–1.9 ms |
  | `bv-ult-choice-8` | 10 | 10 | 4.6 ms |
  | `bv-add-inverse-8` | 513 | 26 | 0.15 ms |
  | `bv-add-inverse-16` | **>1 000 000** | 50 | 0.35 ms |
  | `bv-add-inverse-64` | **>1 000 000** | **194** | 1.07 ms |

  **On twenty-two of twenty-four families the BDDs are trivially
  small** — under 130 nodes, most under 20 — and on those the conflict
  check really would be free. The exception is two-operand arithmetic,
  where the prefix order gives the textbook exponential (33, 513,
  >10⁶ at 4, 8, 16 bits) and the interleaved order gives the textbook
  linear (3n + 2, so 194 nodes at 64 bits). The same function, the same
  package: **a factor of over five thousand, decided by a permutation
  of the inputs.**

  And it is the family where ID is at its best — `bv-add-inverse` is
  the definitional shape from the theory-lifting argument, solved at
  every width with zero decisions and zero conflicts in about a
  millisecond, *order-obliviously*. ID has no variable-order problem to
  have. A BDD-backed ID would acquire one, on exactly the instances it
  currently handles perfectly.

  The region tells the same story from the other side, and more kindly
  (`bench_games`, `region` mode, now reporting BDD nodes in the
  natural latch order and the best of 300 random orders next to the
  cube counts):

  | family | cubes built | ideal cover | BDD natural | BDD best order |
  |---|---|---|---|---|
  | `arbiter-4-4` unary | 75 | 53 | **59** | 59 |
  | `arbiter-4-4` binary | 53 | 25 | 70 | 70 |
  | `corridor-4-stay` | 20 | 20 | 35 | 23 |
  | `ring-6` | 6 | 6 | **128** | **14** |
  | `ring-4` | 4 | 4 | 32 | 10 |
  | `arbiter-3-3` unary | 10 | 10 | 20 | 14 |

  On `arbiter-4-4` — the family that costs 88 s and 248 000 conflict
  checks — the region BDD is 59 nodes against an ideal cube cover of 53
  and the 75 cubes the refinement loop actually builds, and it is
  completely insensitive to the order (59 either way). That is the
  SYNTCOMP result reproduced in miniature: where the region is the
  bottleneck, the BDD is as good as the best cube set anyone could
  find, and it is reached in one step instead of 77 refinement rounds.
  On the ring the natural order is 21x worse than the cube set and a
  better order recovers most of it (128 → 14), which is the same
  lesson: **the numbers are order numbers, not BDD numbers.**

  **Verdict: not a replacement, a budgeted alternative.** Every
  argument for BDDs here survives, and the single argument against is
  concentrated and identified — the method acquires a sensitivity the
  current one does not have, and the worst case is exponential memory
  rather than slowness, which is the failure mode you cannot recover
  from mid-solve. The shape that follows is the one that already
  worked once in this project, for the determinacy check: run the cheap
  complete method **under a budget**, fall back to the general one when
  the budget trips. `Bdd::with_limit` and `Bdd::exceeded` exist for
  exactly that signal, and the ordering result says a serious version
  needs sifting, which is the real cost of the idea and should be
  costed as such rather than assumed away.

  A first reading of the above went to "so the strongest form is BDDs
  for the *region*, in the game layer". That is a deflection: safety
  games are a test vehicle here, not the application, and the question
  asked was about the conflict check inside ID. It also rested on the
  wrong population — the numbers above are *final* Skolem models of
  *satisfiable synthetic* instances, and the conflict check runs
  mid-search, on partial states, mostly on instances that end
  unsatisfiable. So the measurement was redone on the population that
  actually matters.

  **The right measurement: sample the live conflict-check state.**
  `ConflictCheck::trail_bdd` (behind `probe`, enabled with
  `BOOLEANIUM_PROBE_BDD`) builds the Skolem functions of the current
  trail as BDDs over the universals, exactly the way a BDD-backed
  solver would — walk the trail in dependency order, compose each
  variable's firing condition from the BDDs of the variables its
  implication clauses mention — under a one-million-node budget.
  Sampled at powers of two of the complete-check count, on the CADET
  suite and QBFEVAL'17:

  | corpus | instances with data | every sample fit | blew the budget | median peak | max peak |
  |---|---|---|---|---|---|
  | CADET | 72 | 70 | 2 | **7 nodes** | 169 053 |
  | QBFEVAL'17 | 5 | 2 | **3** | — | 46 400 |

  **On the CADET suite the answer is yes, emphatically**: 61 of 70
  instances peak under 100 nodes and the median is *seven*. On those,
  the conflict check really would collapse to a pointer comparison, and
  the CEGAR cube would come out ideal for free.

  **And it fails exactly where it would matter.** The instances that
  blow the budget or come close are the ones this project has spent its
  time on: `adder2` — the instance frontier CEGAR was built for — needs
  **169 053 nodes**, four orders of magnitude above the median;
  `bug10rr` and `bug10rrr` — the instances that exposed the frontier
  certificate soundness bug — exceed a million; on QBFEVAL, `add20y`
  and two `cache-coherence` instances exceed a million. `add20y`
  *solves in under five seconds* and still blows up, so this is not
  "hard instances are hard": it is structural, and the structure is
  arithmetic.

  That is the anti-correlation that decides it. **The BDD is cheap
  where the check is already cheap, and it explodes on exactly the
  structure ID handles best.** `bv-add-inverse` is the same point in
  the clean case: ID determinizes it at every width with zero decisions
  and zero conflicts, order-obliviously, while its Skolem functions are
  >10⁶ BDD nodes in the prefix order and 194 interleaved.

  And the ordering escape does not survive contact with the corpus. For
  `bv-add-inverse` the good order was hand-built from knowing which
  bits are operands. `add20y.qdimacs` is a CNF file — there is no
  operand structure to read, so a real implementation has to *find* the
  order, which means sifting a 10⁵–10⁶ node BDD during search, and the
  cost of that has to be set against a SAT call that costs 17.7 µs when
  it finds nothing and 118.9 µs when it does.

  **Answer to the question as asked**: BDDs cannot replace the SAT
  conflict check in ID. As a *budgeted accelerator* they remain
  defensible and the CADET median of seven nodes is a real argument for
  trying — maintain the BDDs while they stay under a few thousand
  nodes, hand the check back to SAT permanently once they do not, which
  is the shape that already worked for the determinacy check.
  `Bdd::with_limit`/`Bdd::exceeded` are that signal. But the honest
  expectation is set by the anti-correlation: the instances that would
  keep the budget are the ones that are already fast, so the ceiling on
  the win is low and the engineering (incremental maintenance across
  backtracking, plus reordering) is not.

  The region result stands on its own and is recorded above, but it
  belongs to the RQ5 track and answers a different question.

  So the item is not "build a stronger filter", which was the reading
  the call counts invited. It is either making the *positive* check
  cheaper, or asking for fewer of them — and the second is a question
  about the search, not about the check.

  The appealing symmetry — do to the conflict check what the budgeted
  micro-DPLL did to the determinacy check — does not transfer as
  cleanly as it looks. A determinacy check is *local*, over the
  implication clauses of one variable, which is why a budget decides
  almost all of them; a conflict check is *global*, over the matrix,
  the determined Skolem functions and every handled case, so a
  budgeted searcher for it is a SAT solver again. The filter side is
  the one with room: it currently reasons only about clashing literals
  within pairs of implication clauses, and never propagates.

* **The alternating encoding closes the same gap at the source**
  (`Unroller::alternating`, now that the solver handles deep
  prefixes): unroll with *one quantifier alternation per step*,
  `∀I₀ ∃C₀ ∀I₁ ∃C₁ …`, putting the gate, latch, and controllable
  variables of step `t` in the existential block of that step.
  Causality then holds by construction — it is a property of the
  prefix, not something to audit afterwards — so a satisfiable answer
  *is* realizability for the depth. The price is `2·depth` blocks
  instead of two, which is exactly the capability RQ6 built. The two
  encodings provably differ: on a "announce the next input" spec the
  flat prefix is satisfiable at every depth while the reactive one is
  refuted from depth 2, and the solver matches an independent
  reactive-game oracle at each depth.

  Worth recording, because it explains the causality results above:
  across **20 000 random specs / 39 979 depth verdicts** the two
  encodings *never once* disagreed. Clairvoyance is real but rare —
  random sequential circuits essentially never reward seeing the
  future — which is why the post-check kept answering "causal" on
  everything except the hand-built swap-timing games. The honest
  encoding is cheap to prefer now, but the flat one was not
  misleading in practice.
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
* **An expansion is only worth doing if it collapses the prefix.** At
  ≤2 blocks the instance goes straight to the core (`BLOCKS4iii` hands
  it 950k clauses happily, 30 s timeout → 1.9 s); otherwise it pays
  for per-level simplification and abstraction seeding on every
  candidate. *Speculative* expansions first got a smaller budget and
  were later dropped outright — see the deep-prefix measurement
  below.
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
the strategy wins everywhere. A SAT call replaces `2^|Y|`
evaluations, which is the difference between checking the fuzz range
and checking an instance with a 47-variable universal block. Both the
universals and the existentials the strategy leaves undetermined stay
free, so the check reads "for *all* universal assignments *and all*
values of the undetermined variables" — the strong form, which is
sound because a variable is only left out when the solve found it
irrelevant. It is wired to `--certify` and `--strategy` for any prefix
depth.

**One query per clause, not one query for all of them.** The natural
encoding of "some clause is falsified" is a selector per clause and a
disjunction over the selectors. It is also the worst one: the solver
gets a single enormous query with 2 023 ways to succeed and no handle
on any of them. Asking one clause at a time instead — the same solver,
the same circuit, the falsifying literals passed as *assumptions* —
keeps everything expensive shared and everything learnt, and each
query is small and focused. On `lights3_021_0_009` (43 blocks, a
98 256-gate strategy, 2 023 clauses) verification went from 123 s to
33 s; the instance had been failing the strategy suite's 60 s budget
and now passes it. The solve itself takes 0.26 s, which is the real
statement here: on deep prefixes it is *checking* the answer, not
finding it, that costs.

Substituting the circuit wires directly into the matrix instead of
tying them to matrix variables by equivalences — two fewer clauses per
determined variable, one less propagation step — was tried on top and
was **worse**: 44 s against 33 s. The equivalences are not overhead;
they give the solver a decision variable per determined existential
and keep the matrix clauses short, and it uses both.

The next step, if verification needs to get faster still, is to
decompose along the strategy's own structure rather than along the
matrix: check each `Split` case against its cube separately, so each
query sees one branch's circuit instead of all of them. That needs the
earlier cubes' negations to be part of each case's query — case `k`
only applies where no earlier cube holds — which assumptions cannot
express, so it wants a solver per case and is a larger change than the
one measured here.

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

How much it generalizes is decided entirely by **the width of the
universal block**, and the two ends of that range were both measured.

| instance | block width | cube literals dropped |
|---|---|---|
| `lights3_021_0_009` | 1 | **0 of 254** |
| `ev-pr-4x4` | ~3 | 3 of 21 |
| `biu` | 46–47 | **828 188 of 955 933 (87%)** |

At width 1 there is nothing to drop — by the time the recursion
reaches a ∀-loop, the expansion dispatch has eaten the small universal
blocks and `normalized`/`restrict` hand each level one block at a
time — and the query is pure overhead: `lights3` went from 24 s to
49 s, its rounds unchanged at 631, because the query encodes the
*composed sub-strategy*, whose size grows with the rounds already
taken (8.6M strategy nodes across 254 queries). That cost is quadratic
in the loop the technique is meant to shorten.

Gating on block width fixes the overhead — narrow blocks skip the
query, and `lights3` stays at 1.0 s — and on `biu`, the one suite
instance with wide ∀ blocks, the mechanism works exactly as designed:
cubes of ~30 literals shrink to ~4. It still does not crack the
instance. Blocking 87%-shorter cubes out of 2⁴⁷ turned "gives up after
4096 rounds in 2.2 s" into "still running after 120 s", same verdict.
Reverted a second time.

So the honest statement is not "the cubes are too short" — that is
only the `lights3` half. It is: *region learning from a point strategy
works, in proportion to block width, and no instance available to this
project is both wide enough to benefit and close enough to solvable
for the benefit to matter.* Reviving it needs a corpus with wide ∀
blocks at recursion depth ≥ 4; the whole 701-instance
`reduction-finding` corpus is at most three blocks with an outermost
∃, so its ∀-loops never run at all. The version that would pay
regardless is strategies built to be universal-independent — a
dual-CEGAR abstraction in CAQE's sense — rather than point strategies
generalized after the fact.

One byproduct worth recording: across every one of those queries the
sub-strategy was confirmed valid, which is thousands of independent
strategy verifications at *every* recursion level of real instances,
not just at the top.

**On `biu`.** It is the only CADET-suite instance booleanium does not
decide, and it is worth stating plainly that **CADET does not decide
it either** (it gives up in 0.25 s; the suite's expected verdict comes
from elsewhere). ∃48 ∀47 ∃52 ∀47 ∃49 ∀46 ∃498 defeats expansion (the
blocks are 6x the expansion cap), memoization (4 sub-solves, no
repeats), and region learning (above). It is not a tuning target for
this architecture, which puts the suite effectively at **125 of 125
decidable**.

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

**Speculative ∀-expansion — removed, and it was the wall.** The
scaling table above was the first thing the instrument paid for.
Profiling the satisfiable arbiter at its cliff showed the run was not
in the candidate loops at all: it was a *single* leaf solve over
46 643 clauses, grown out of an instance with 245. The expansion
dispatch had eaten the whole prefix.

The fixpoint expands the innermost ∀ block whenever the result fits a
budget, and on a deep prefix it does that once per remaining ∀ block,
each multiplying the trailing material. Every individual step passed
its 50k budget; the *product* was never bounded. The distinction the
code already drew — a *collapsing* expansion hands its result to the
2QBF core, a *speculative* one hands it back to the loops, which pay
per clause many times over — turns out to be the whole story, and the
speculative case has no business being taken at all:

| | before | after |
|---|---|---|
| reactive `arbiter-2-2`, depth 8 | 22.0 s | **31 ms** |
| reactive `ring-4`, depth 12 | 2.1 s | **38 ms** |
| reactive `corridor-4-stay`, depth 7 | 6.5 s | **0.22 s** |
| `lights3_021_0_009` | 0.85 s | **0.12 s** |
| `BLOCKS4iii.7` (collapsing) | 1.55 s | 1.59 s |
| `arbiter-05 …depth-6` | 2.27 s | 2.31 s |

Collapsing expansions are untouched, so nothing that relied on them
moves. The CADET suite is unchanged at 125 correct, all 19 satisfiable
multi-block instances still certify, the 701-instance cross-validation
decides 592 (one more than before) with zero disagreements, and the
fuzz passes 300k cases per family. Worth noting what this says about
tuning: the speculative budget was a *measured* parameter, fitted on
the CADET suite, and it was fitted to a corpus that tops out at seven
blocks. It took a family with 32 blocks to show that the whole branch
was a loss.

**A depth-scaling instrument** (`bench_games scale`). The suite is
decided apart from `biu`, and every corpus in reach is 2QBF or 3QBF,
so the remaining alternation work had nothing to be judged on. The
reactive unrolling supplies it: a family generator with depth as a
dial and verdicts known independently from the game oracle. Solving
each depth and verifying each strategy — as it stood when the
instrument was built, before the sharing work below:

| family | verdict | blocks | solve | strategy | verify |
|---|---|---|---|---|---|
| `arbiter-3-2` | unsat | **32** | 9.5 ms | — | — |
| `ring-4` | sat | **32** | 198 ms | 2 425 176 | (skipped) |
| `ring-4` | sat | 22 | 31 ms | 76 005 | 4.8 s |
| `corridor-4-stay` | sat | 18 | 815 ms | 7 423 078 | (skipped) |
| `arbiter-2-2` | sat | 22 | 1.3 s | 12 093 332 | (skipped) |
| `arbiter-2-2` | sat | 14 | 12 ms | 89 040 | 10.2 s |

**Depth alone is not the difficulty.** The unsatisfiable arbiter is
essentially *flat* — 5.2 ms at 6 blocks, 9.5 ms at 32 — because a
refutation is found near the front of the prefix and never has to
enumerate what is behind it. The satisfiable families reach 32 blocks
too, in a fifth of a second.

**What grew was the composed strategy, not the search.** Its size
roughly *tripled per alternation* — `arbiter-2-2` went 31, 187, 666,
2249, 7662, 26 095, 89 040, … , 41 289 049 nodes across depths 1–12,
while the solve stayed in milliseconds until the sheer size of the
object being built took over. The reason was structural: composition
deep-cloned the sub-strategy into every case of every `Split` and
every copy of every `Expanded`, so a strategy a DAG would represent in
linear space was materialized as a tree. The unsatisfiable family,
which builds no strategy at all, stayed flat — which is exactly the
control that diagnosis needed.

### Sharing, in two places, and only one of them obvious

**The strategy itself.** Making the recursive fields `Rc` and letting
the sub-solve memo hand back a shared pointer instead of a deep copy
turns the tree back into the DAG it always was. It is a one-line
change per constructor, and the numbers move by orders of magnitude:

| depth | tree nodes | DAG nodes |
|---|---|---|
| 3 | 666 | 322 |
| 5 | 7 662 | 513 |
| 7 | 89 040 | 645 |
| 12 | 41 289 049 | **975** |

Growth goes from geometric to *linear* — 66 nodes per alternation,
which is one `Split` over the block plus the leaf it wraps. `size()`
counts distinct nodes now (identity-memoized), because what the memo
budget has to bound is memory, and memory is the DAG.

**The circuit — where the blowup actually went.** That should have
made certification cheap and did not: at depth 7 the strategy is 645
nodes and its circuit is **42 950 gates**, and at depth 12, from 975
nodes, **19 984 296**. Compiling a DAG node by node flattens it right
back into the tree, because `build_into` threads an accumulator of
values through the walk and a node reached along two paths is asked
for its circuit twice, under different accumulators.

The first attempt keyed a memo on `(node, the whole value map)` and
got **0 hits in 6 690 calls** over 645 nodes — every node revisited
about ten times, never with the same map. The map is the wrong key:
what differs between the paths into a shared node is the constants an
outer `Choose` committed to, and those are variables the node's
subtree never mentions. Keying on the values of the variables the
subtree *does* mention — its cubes, its assignments, its expansion
copies, its leaves' outputs, everything it could read or write —
collapses it:

| depth | gates before | gates after | certificate check |
|---|---|---|---|
| 5 | 3 604 | 588 | 46 ms → 7.5 ms |
| 7 | 42 950 | 1 318 | 12.8 s → 41 ms |
| 8 | 146 928 | 1 800 | (skipped) → 93 ms |
| 12 | 19 984 296 | **4 508** | (skipped) → 3.95 s |

On a real instance, `lights3_021_0_009` (43 blocks): 313 239 strategy
nodes and 98 256 gates become 742 nodes and **315 gates**, and its
certificate check goes from 33 s to **0.98 ms**. The instance that was
failing the strategy suite's 60 s budget now certifies in under a
second end to end.

The lesson is the one the failed first attempt taught: sharing in the
data structure buys nothing on its own if every consumer walks it as a
tree. The consumers have to be told what a node actually depends on.

What remains is genuinely the SAT check. Gates now grow quadratically
with depth while verification time still grows ~2x per alternation on
`arbiter-2-2` — that is query hardness, not encoding size, and it is
the honest wall. But it moves the reachable depth a long way. The
instrument now certifies **every satisfiable depth it generates** —
40 of 40, none skipped, none invalid — where the size guard used to
fire from depth 8 on `arbiter-2-2` and depth 12 on `ring-4`:

| family | verdict | blocks | solve | strategy | circuit | verify |
|---|---|---|---|---|---|---|
| `arbiter-3-2` | unsat | **32** | 13 ms | — | — | — |
| `arbiter-2-2` | sat | 24 | 22 ms | 975 | 4 508 | 4.0 s |
| `ring-4` | sat | **32** | 88 ms | 1 602 | 10 730 | 153 s |
| `corridor-4-stay` | sat | 20 | 684 ms | 13 960 | 73 015 | 1 900 s |

`ring-4` at its full 32 blocks costs the 153 s it used to spend on 22.
`corridor-4-stay` — the widest family, and the one that used to build
a 7.4-million-node strategy at depth 18 — certifies its last generated
depth, where before the guard fired at depth 12.

Earlier drafts of this section reported the certification points as
*solver* cliffs; they are not — solving those same instances takes
tens of milliseconds. The measurement that separated them was simply
running the CLI with and without `--certify`.

### Directions from the solver-landscape review

**Clausal abstraction, as the thing that *unifies* search and
expansion.** Q-resolution and ∀Exp+Res are incomparable, and this
solver happens to own one engine of each: ID's clause learning and the
alternation front-end's expansion. The weak conclusion is to race
them; the strong one, and the one CAQE actually demonstrated, is that
clausal abstraction is QDPLL-shaped and expansion is compatible
*inside* it, which is why CAQE decided instances that neither DepQBF
nor RAReQS could. That reframes the front-end's future: not patching
the ∀-loop, but replacing the ∃-loop, the ∀-loop and the
expansion-budget dispatch with one per-block abstraction, where the
universal side gets universal-independent refinements by construction
— exactly what region learning failed to fake after the fact, twice
(above). It also dissolves `MAX_EXPANDED_BLOCK` rather than tuning it,
and it makes `biu` (∃48 ∀47 ∃52 ∀47 ∃49 ∀46 ∃498) a fair test again
instead of an instance that defeats expansion by construction. This is
a rewrite of `alternation.rs`, not a patch.

**Dependency schemes — worth a survey, with a prior against.** The
informed prior is that a dependency scheme mostly finds slack on
Tseitin variables, which would make it uninteresting here. Two things
cut the other way and are worth settling with the corpus rather than
with priors:

* The Tseitin variables are exactly the ones this solver *fails* to
  recover on hard instances. The RQ1 survey measured a median 45% of
  existentials determinized up front on solved instances and **6% on
  timeouts**. A dependency scheme finds independence by clause
  connectivity and does not need the definition to be two-sided, so
  the two mechanisms are complementary precisely on the population
  that currently loses.
* In 2QBF the trivial scheme reduces *nothing*. `preprocess_clause`
  drops universals bound after every existential of the clause, and in
  ∀X ∃Y that condition never fires. Universal reduction does no work
  at all in the core today, on any instance. A scheme is the only
  thing that would make it do any — and shorter learnt clauses feed
  straight into the measured problem that 81% of the complete conflict
  checks prove there is no conflict.

The cheap decisive version, before any scheme goes near the core:
compute the *standard* (connectivity) scheme over the 384-instance
corpus and cross it with the determinization fraction already
instrumented. Slack inside the already-determinized set means the
prior was right and this is one paragraph; slack concentrated in the
0–20% band (182 instances, 21% solved) means it sits exactly where the
solver loses. Note the soundness caveat: determinacy here means "a
unique value under *every* universal assignment", and relativising
that to a dependency set changes the semantics of the central notion —
Q(D)-Res soundness does not transfer to a Skolem-function setting for
free.

**Long-distance resolution — deliberately not in the core.** In ∀X ∃Y
every universal is left of every existential pivot, so LD merging
never applies; its power is in the alternating case, which is where
this solver has no clausal calculus at all. That is an argument for
giving the deep path a real calculus (IR-calc/IRM-calc unify both
systems and are strictly stronger), not for patching 2QBF.

**Full-solver QRAT.** Proofs today require CEGAR and case splits off,
because the clausal rules cannot express their derivations. But a
CEGAR case *is* an expansion step, and QRAT p-simulates ∀Exp+Res, so
an encoding via extension variables naming the case cubes should
exist. That turns a documented limitation into a result.

**Strategy extraction as a hardness classifier.** Strategy extraction
into a circuit class plus a lower bound for that class yields
proof-size lower bounds. This solver *is* a strategy extractor, into
AIGs, and now instruments both strategy nodes and circuit gates — so
the machinery to split instances into "search-hard" and
"strategy-hard" already exists. Where the Skolem function is
inherently large, no amount of conflict-check tuning helps, and that
is worth knowing before spending more on the conflict check.

Next steps in order of leverage: the two-solver baseline for RQ5
(above), which is the missing control for the whole positioning; the
dependency-scheme survey, which is cheap and could reorder the rest;
∀-side persistent oracles (needs ∃∀ assumption support in the core),
which is also the prerequisite for doing dual refinement properly; and
the determinize-then-dispatch hybrid.

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
