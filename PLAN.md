# Plan: finishing the incremental determinization solver

This document records the state of the solver, the changes made to finish the
core algorithm, and a roadmap for the remaining work. The algorithm is based
on [Incremental Determinization](https://link.springer.com/chapter/10.1007/978-3-319-40970-2_23)
(Rabe & Seshia, SAT 2016): instead of assigning truth values, the solver
assigns *Skolem functions* to existential variables. A variable is
*deterministic* when the clauses seen so far force a unique value for it under
every universal assignment; conflicts arise when a variable is forced to both
values, and are resolved by CDCL-style clause learning over the implication
graph.

## State of the core algorithm

The 2QBF core loop — determinacy checks, watch-based function propagation,
local/global conflict checks, conflict analysis with clause minimization,
VSIDS — is validated by differential testing against a brute-force oracle
(`QCNF::brute_force`). Several hundred thousand random instances across
propagation-heavy, decision-heavy, and conflict-heavy shapes pass, for every
combination of solver options and for ∀∃, ∃∀, and purely existential
prefixes. See `src/incdet/test.rs` (`fuzz` module); run with e.g.
`PROPTEST_CASES=50000 cargo test --release incdet::test::fuzz`.

## Finished in this pass

* **Constant propagation** (`Options::constant_propagation`, previously the
  dead `ENABLE_CONSTANT_PROPAGATION` flag): the queue was pushed to but never
  drained, so enabling it lost propagations and produced wrong results.
  Now `propagate` drains constants first (`propagate_constant`); constants
  are used to strengthen the determinacy check and both conflict checks
  (unit clauses), to skip globally satisfied clauses during function
  propagation, and new constants are derived at the root level when all
  remaining literals of an implication clause are constant false.
  Contradicting constants are reported as a conflict with an empty universal
  assignment, which conflict analysis correctly turns into UNSAT.
* **Incremental conflict check** (`Options::incremental_conflict_check`,
  previously the disabled `INCREMENTAL_CONFLICT_CHECK` flag): validated by
  differential fuzzing and enabled by default. It reuses one incremental SAT
  solver with per-decision-level assumption literals instead of rebuilding a
  solver for every global check.
* **Propagation across backtracking**: `backtrack_to` used to clear the whole
  propagation queue, silently dropping pending determinacy checks (variables
  were later handled by decisions, which is sound but weaker). Unassigned
  variables that still have implication clauses are now re-queued, as is the
  conflict variable after learning.
* **Conflict-clause minimization** is memoized (`is_literal_redundant`),
  avoiding exponential re-exploration of shared implication sub-graphs.
* **Implication graph** entries no longer duplicate a reason clause per
  universal literal; an entry is one `(clause, decision level)` pair.
* The feature `const`s were replaced by a public `incdet::Options` so
  configurations can be fuzzed and benchmarked against each other
  (`bench_conflict_check_configs`, `fuzz_path_coverage` test helpers).

## Roadmap

### 0. CAV'18 extensions ("Understanding and Extending Incremental
Determinization for 2QBF", Rabe, Tentrup, Rasmussen, Seshia)

* **CEGAR conflict resolution — done** (`Options::cegar`, default on):
  when a conflict check returns a conflicting universal assignment α, a
  second SAT solver over the original matrix checks whether the
  existential player has any response to α. If not, the formula is
  unsatisfiable immediately (this solves the former `bug8.qdimacs`
  timeout in milliseconds). If yes, the response is generalized to a cube
  (support-based minimization) recorded as a handled case and excluded
  from future conflict checks; an empty cube means immediate
  satisfiability. Recording a case *replaces* clause learning only at the
  root level; otherwise the conflict additionally goes through clause
  learning — pure case-carving diverged on an unsatisfiable instance with
  178 universal variables (`stmt27rrr.qdimacs`), while the combination
  keeps both the pruning and the refutation progress. An effectiveness
  gate (exponential moving average of cube sizes) stops CEGAR rounds when
  cubes degenerate. Effect on the hard random benchmark instances:
  10–300x faster (e.g. `random-12-90-330-4` 88s → 0.3s); the certified
  fuzz harness validates recorded cases in every satisfiable result.
* **Frontier CEGAR — done** (the piece that solves `adder2.qdimacs`,
  studied from CADET's `cegar.c`, which solves it with 120 conflicts in
  0.1s — with case splits *off*): cubes over the universal inputs cannot
  generalize across carry chains, so CEGAR used to degenerate on adder
  circuits and the gate shut it down. Following CADET, everything is
  rephrased in terms of the deterministic *frontier*: a clause is
  *settled* if it is an implication clause of a root-level assigned
  variable (the root functions satisfy it everywhere); the *frontier*
  consists of the universal variables and root-level existential
  variables occurring in unsettled clauses (35 variables on `adder2`
  against 96 universal inputs). When the universal cube of a round
  degenerates (above the effectiveness fraction), the response is
  re-solved with the conflicting assignment's frontier values pinned and
  generalized to a cube *over frontier literals* — a cube over derived
  signals covers exponentially many inputs at once. Responses then only
  need to cover the non-frontier variables; the root-level functions are
  recorded implicitly, and certification verifies each recorded case as
  a region (root functions plus response constants, SAT-checked) instead
  of the earlier syntactic support check. Frontier cubes are excluded
  from the conflict checks like any handled case (the check solver knows
  the function definitions); the case-split domain solver only receives
  all-universal cubes, which is conservative. The universal-cube path is
  attempted first and kept when it generalizes, so the hard random
  instances keep their old behavior (bench-neutral), while `adder2` goes
  from a 30s+ timeout to 0.2s — the full supported CADET suite now
  passes with **84 of 84 correct, no timeouts**.

  Certifying the *real* suite instances (the runner now passes
  `--certify`; the fuzz harness alone had missed this for 280k cases)
  exposed one soundness bug in the frontier-case certificates: the
  response used to cover the variables outside the *interface*, but a
  variable that is root-level assigned with all its clauses settled is
  outside the interface too, and overriding its load-bearing function
  with a response constant broke its settled clauses elsewhere in the
  region (`bug10rr.qdimacs`). The response now covers exactly the
  variables that were not root-level assigned when the response solver
  was built. Two follow-up experiments were rejected by measurement:
  carving *multiple* cases per conflict before learning (CADET does up
  to 50 rounds per learnt clause) made the suite an order of magnitude
  slower — without interleaved learning, near-identical cubes flood the
  conflict check with exclusion clauses; and flipping the decision
  polarity to CADET's default-true convention timed `bug10rr` out
  entirely. The CEGAR response query now sorts its assumptions: the
  backend's search is sensitive to assumption order, and feeding it an
  unordered set made whole-suite runs a lottery (the same binary
  fluctuated between 0.7s and 99s on the random benchmarks; runs are
  deterministic now).
* **Interleaved case splits — done** (`Options::case_splits`, default on
  with a stall threshold of 5000 conflicts, CLI `--case-split-threshold`;
  replaces the v1 restart-from-scratch recursion): once the search
  stalls, a universal literal is *assumed* — assigned as a constant at a
  fresh decision level — which restricts all determinacy and conflict
  checks to the halved domain while keeping the full solver state (learnt
  clauses are matrix-implied resolvents and stay valid across cases).
  When every existential variable is assigned inside a case, the case is
  closed: the Skolem functions are snapshotted for certification, the
  assumption cube is excluded from all future conflict checks, and the
  solver backtracks below the assumptions. A small domain solver over the
  universal variables holds the negation of every handled cube (CEGAR
  cubes included); its models pick the next assumption polarity, and its
  unsatisfiability proves the whole domain is covered. Certification
  works piecewise: region `k` of the handled-case list is valid on its
  cube minus the cubes handled before it, and the final solver state
  covers the rest.

  The subtle part is conflict analysis: case assumptions give universal
  literals decision levels, so a learnt clause whose deepest existential
  literal lies *below* the deepest case-assumption literal would — with
  the standard "second-highest level" rule — backtrack without
  unassigning that existential, and the clause would be registered as an
  implication for an already-assigned variable, silently corrupting its
  function (found via a certified fuzz counterexample). The backtrack
  level of such clauses is therefore computed from the existential
  literals only, going strictly below the deepest one. Learnt clauses
  consisting purely of universal literals refute the instance outright
  (they are matrix-implied, so the universal player wins by picking the
  cube).

  Such backtracks land below the case assumptions, so assumptions are
  *sticky*: they stay committed until their case closes and are
  re-assumed once propagation settles (abandoning a case would be
  pointless anyway — the universal player chooses the case, so every
  case must be won; a genuinely lost case surfaces as a global
  refutation through the all-universal-clause rule or a root conflict).
  Re-assuming also re-queues only the determinacy checks that can
  actually change: the check is local to a variable's implication
  clauses, so only variables whose implications mention the assumed
  variable are affected.

### 1. Algorithm: beyond 2QBF

`_solve` currently rejects prefixes with more than two blocks. Options, in
increasing order of ambition:

* **Quantifier-block recursion / expansion** for small inner blocks, reducing
  a k-block instance to 2QBF sub-problems (CEGAR over the outermost blocks,
  as in RAReQS). Cheap to build on the existing core.
* **Dependency-aware determinization** (CADET does this only for 2QBF as
  well): determinacy and conflict checks must respect that an existential
  variable may only depend on universals of outer scopes. The current checks
  quantify over *all* universals; for general prefixes the checks need
  dependency sets per variable and the learned clauses need universal
  reduction with respect to scopes (the `_add_clause` reduction already
  handles part of this).

### 1b. Input languages

* **QAIGER (circuit) input — done** (`src/aiger.rs`, auto-detected by
  the `aag` header): 2QBF instances given as combinational AIGER
  circuits, following CADET's convention (inputs named with the prefix
  `"2 "` are controllable/existential, other inputs and latches are
  universal, gates become existential variables with two-sided Tseitin
  definitions, the output is asserted). This is the definition-level
  input path: nothing is lost to one-sided CNF encodings, and the
  effect is drastic — `beem.qaig` (18k gates) solves with zero
  decisions and one conflict, and all nine QAIGER instances of the
  CADET suite solve in ≤ 0.8s, certified, raising the suite to **93 of
  93 supported instances correct**. Validated additionally by a
  differential proptest over random circuits against the brute-force
  oracle. A **QCIR frontend** (`src/qcir.rs`, prenex circuits at *any*
  depth with `and`/`or`/`xor`/`ite` gates, named or cleansed
  identifiers, universally-ending prefixes by negation, deep ones
  dispatched to the alternation front-end with strategies emitted under
  the surface names) extends the same definition-level path to the QBF
  community's structured-instance format — see `RESEARCH.md` (RQ1)
  for design and validation. The **paired-encoding experiment**
  (`bench_encodings`: the same families as QCIR, two-sided CNF, and
  Plaisted–Greenbaum CNF) measured what the format is worth — the
  answer is conditional, not the predicted uniform win; results and
  analysis in `RESEARCH.md` (RQ1). Two bit-vector families
  (`bv-add-inverse`, `bv-ult-choice`) extend it to the bit-blasting
  question: the addition determinizes *completely* with zero decisions
  and zero conflicts at every width from 4 to 64 bits (509/509 in
  1.4 ms over a 2¹²⁸ universal domain), even though `y` must be
  recovered by *inverting* the adder, while an
  8-bit comparison under a disjunctive top determinizes 2/40 and PG
  beats the definition-level encoding 2.4x — so what predicts the
  outcome is output-forcing, not word-level-ness (`RESEARCH.md`, RQ3). The larger questions this opens — an
  incremental (QIPASIR-style or SMT-LIB) interface, theories, and
  positioning as a building block for two-player games — are collected
  in **`RESEARCH.md`**.

### 1c. Incremental API and SMT-LIB frontend

* **Incremental solving API — done** (`src/incremental.rs`): an
  assertion stack of frames (`push`/`pop`/`add_clause`/`define_and`/
  `solve`/`solve_with_assumptions`) over the ∀∃ core, with
  *learnt-clause carrying* — learnt clauses are resolvents of the
  matrix they were learnt under, tagged with their stack depth and
  dropped when that depth pops (deduplicated: the live solver reports
  its whole learnt set per harvest). Piecewise Skolem models are
  extracted from satisfiable results (`src/incdet/model.rs`): a
  pointwise evaluator and an SMT-LIB `define-fun` emitter over the
  region structure of the certificate. Validated by a differential
  proptest running random push/pop/add/solve sessions against the
  brute-force oracle, certifying every satisfiable answer, and
  evaluating the model on every universal point against the matrix
  (including with aggressive case-split thresholds so closed-case
  regions are exercised, and with continuation both on and off).
* **In-place monotone continuation — done, default on**
  (`IncDet::extend_and_resolve`, `IncrementalSolver::set_continuation`):
  between solves whose delta is monotone (only declarations and clause
  additions — any pop or redeclaration falls back to rebuild), the live
  solver is continued in place: the root-level trail, learnt clauses,
  handled cases, variable activities, and the incremental conflict
  check are all kept; the CEGAR response solver and the case-split
  domain solver are invalidated and rebuilt lazily; new clauses are
  integrated at the root mirroring the load/propagation paths (two
  watches, an implication registration, or — with every existential
  literal permanently root-assigned — a root-function entailment check
  whose counterexample is an UNSAT witness). Soundness of retention:
  root functions and constants are *implied* by their implication
  clauses and survive any matrix extension; the two exceptions are
  checked per extension and cause a rebuild when violated — root-level
  **pure-constant choices** survive only if every added clause
  containing their literal is entailed by the root functions
  (unassigned variables adversarial), and every **handled case** must
  satisfy the added clauses on its region (same adversarial check,
  budget-capped at 64 cases — beyond that a rebuild is cheaper than
  the SAT calls). `original_clause_count` became an explicit clause
  list on this occasion (extension originals arrive after learnt
  clauses, breaking the prefix-index assumption). Measured on
  `bench_incremental`: BMC-style parity unrolling (new variables +
  clauses per step, solve each step) drops from 75–90 ms to ~1 ms at
  200 steps (quadratic → linear); monotone-UNSAT re-solves are free
  (verdict shortcut); random clause-refinement chunks are a wash —
  the retained pure choices and CEGAR cases genuinely die there, the
  gates reject in microseconds, and remaining deltas are search-
  trajectory variance. Not carried over a rebuild: nothing — learnt
  clauses are harvested on success *and* failure (a rejected extension
  integrates nothing, so the live solver's resolvents stay valid).
* **Queries and scoped pops preserve the continuation — done**:
  temporary queries (`solve_with_assumptions`/`solve_with_clauses` —
  `check-sat-assuming`, the ∃∀ negation clause) run on a *throwaway
  solver* beside the continuation base and serve the model calls until
  the next solve, instead of baking their clauses into the live
  solver; and the base records per-frame *integrated sizes* (frames
  are append-only apart from whole-frame pops), so the delta of the
  next solve is derived on demand and a pop of frames the base never
  solved — the push/assert/pop scoping pattern — costs nothing. Only
  popping an integrated frame or redeclaring a variable still forces a
  rebuild (inherent to root permanence). The differential session fuzz
  gained assumption-query actions, checked against the oracle with
  certification and model evaluation under the assumptions.
* **In-place assumption queries — done**
  (`IncDet::resolve_with_assumptions`, tried first by
  `solve_with_assumptions`): existential assumption literals are
  assigned as *constants at fresh decision levels* — the existential
  analog of universal case assumptions — sticky across backtracks and
  passed to the conflict check as level-guarded units. Assumptions
  carry no implication clauses, so conflict analysis keeps their
  negations in every resolvent, making everything learnt or recorded
  during a query matrix-valid and persistent. Query-critical pieces:
  CEGAR rounds add the query literals to the response-solver
  assumptions (recorded cases then respect them, so region coverage
  and the piecewise certificate stay valid); assumption *violations*
  (an opposite-polarity implication firing against the constant)
  resolve exclusively by CEGAR rounds, since variable-centric analysis
  would drop the assumption literal from the learnt clause; the
  redundancy check no longer treats reason-less literals as removable;
  root-assigned assumption variables are answered directly (constants
  and root functions are forced, so a function-entailment
  counterexample refutes the query and doubles as its universal
  witness, verified under the query units). The fast path declines —
  falling back to the throwaway query solver — when recorded cases
  predate the query, a root pure *choice* blocks the verdict, or the
  search cannot attribute a state; a declined attempt marks the base
  for re-search since it may already have backtracked it (the fuzz
  caught exactly that as an invalid certificate). Retraction is lazy:
  a satisfiable query state serves models and certificates until the
  next solve backtracks it. Measured on probed parity unrolling: the
  probe answers drop from a rebuild each to one small entailment SAT
  call each (~98 ms → ~55 ms at 200 steps, on top of the plain solves
  already being in-place).
* **Universal assumptions, case retention across queries, and
  pop-retention of solved state — done**: domain-restriction queries
  ("what if the environment plays u") run on the in-place fast path;
  recorded cases stay usable across assumption queries via a
  per-case compatibility check; and popping a clause-only frame keeps
  a satisfiable base when the popped originals and live learnt
  clauses are unlocked (`IncDet::retract_to_depth`, per-clause depth
  tags on originals through both the build and extension paths).
  Measured on scoped re-solving (`parity-scoped`, 200 rounds on a
  200-step chain): ~124 ms retained vs ~145 ms dropping the base per
  pop vs ~217 ms rebuild-per-solve. Full designs, soundness
  arguments, and measurements in `RESEARCH.md` (RQ2).
* **Safety-game unrolling benchmark — done** (`aiger::Unroller`,
  `bench_games`): the AIGER path parses sequential SYNTCOMP-style
  safety specifications (latches, `controllable_` inputs, error
  outputs) and unrolls them one time step per solve into the
  incremental API; benchmark families are a bounded-response arbiter
  and ring/corridor pursuit games, validated by a differential
  proptest against an independent game-simulation oracle. End-to-end
  findings — which derived artifacts transfer across game depths,
  the clairvoyance caveat of per-depth ∀∃ queries, and the syntactic
  extension decline it motivated — in `RESEARCH.md` (RQ5).
* **SMT-LIB frontend — done, Boolean fragment** (`src/smtlib.rs`,
  auto-detected by the CLI): declarations, `define-fun` definitions
  (the definition-level input path), assertions over the usual Boolean
  operators with hash-consed Tseitin gates, alternating
  `forall`/`exists` chains of *any* depth (past two blocks the session
  keeps its own prefix, the checks go to the alternation front-end, and
  `get-model` prints the composed strategy via `Strategy::to_smtlib`), `push`/`pop`/`check-sat`/`check-sat-assuming`, and
  `get-model` printing the Skolem functions as `define-fun`s
  parameterized by the universal variables. See `RESEARCH.md` for the
  in-place incrementality upgrade path.
* **∃∀ synthesis mode — done** (the SYNTCOMP-critical shape ∃ strategy
  bits ∀ inputs ∃ gates-determined-by-both): free constants under
  `forall` binders switch the frontend to solving the *negation* —
  gate definitions are self-dual, so only the assertion roots flip
  (`∀ constants ∃ binders, gates: ¬(∧ roots)`) — with the verdict
  inverted. The synthesized constant values are the negation's **UNSAT
  witness**: the core records the universal part of the conflicting
  assignment at every unsatisfiability site (`IncDet::unsat_witness`,
  `IncrementalSolver::universal_witness`). Because pure-literal
  assignments are winnability-preserving *choices* rather than
  pointwise-forced values, the recorded candidate is heuristic and is
  **verified with one SAT call** before being exposed; an unverifiable
  candidate yields `sat` without a model (`get-model` errors) rather
  than a wrong model. The quantifier structure of a session is fixed
  by its first quantified assertion (or first check, defaulting to
  ∀∃); assertion roots stay *pending* until then — in ∃∀ mode they
  form a disjunction that weakens with every new assertion, so each
  check solves it as a temporary clause
  (`IncrementalSolver::solve_with_clauses`) that carried learnt
  clauses can never resolve against. Validated by a 20k-case
  differential proptest against an enumeration oracle that also checks
  every printed model against the matrix on all universal points, plus
  the core fuzz asserting witness validity on all UNSAT 2QBF cases.

### 1d. Quantifier alternations

* **Expansion prototype — done** (`src/alternation.rs`, CLI-dispatched
  for QDIMACS with more than two blocks): recursive CEGAR over the
  outermost block with the incremental 2QBF core as a *persistent
  oracle* at depth three — candidates arrive as assumption queries,
  learnt clauses persist across candidates, and refutations return
  verified universal witnesses that drive classic expansion
  refinements. ∀-outermost blocks use a dual candidate loop (matrix
  negation cascaded Tseitin gates through the recursion and blew
  memory — a measured dead end), deeper prefixes recurse with weak
  refinements, and a resource budget degrades to unknown. Differential
  proptests (20k cases, 1–6 blocks) against the brute-force oracle;
  A ∀-expansion dispatch enumerates small innermost universal blocks
  instead of searching them (capped at eight variables: beyond that
  CEGAR's relevant-assignment enumeration wins, measured at 17x on
  `p10-1.pddl`), and a per-level QBF simplification pass (universal
  reduction, units, pure literals) propagates what the restrictions
  and expansions manufacture, once per level. Expansion itself is
  hoisted to a single top-level fixpoint — reapplying it inside the
  recursion made deep prefixes redo the matrix doubling per candidate,
  which a leaf-solve probe caught as *zero* leaf solves in twenty
  seconds — and expansion is taken *only* when it collapses the prefix
  onto the 2QBF core, never speculatively (measured: on a 16-block
  reactive game the fixpoint grew 245 clauses into 46 602 and took
  22 s, against 31 ms for the loops alone). Finally, the recursion is
  *memoized* on a 128-bit fingerprint of each simplified sub-instance,
  because the candidate loops re-trigger whole subtrees (363 of 377
  sub-solves repeat on the 22-block `lights3`, which went from 24.2 s
  to 1.0 s; the depth-6 arbiter from a timeout to 2.9 s). CADET suite:
  93 + 32 = **125 correct, 0 wrong, 0 timeouts**, `biu` the only
  instance left undecided — and CADET does not decide `biu` either,
  so the suite is effectively complete. Beyond it, the *reactive*
  game unrolling (`Unroller::alternating`, one alternation per time
  step) supplies deep prefixes with independently known verdicts:
  **32 quantifier blocks** solved in `bench_games scale` (unsat in
  9.5 ms, sat in 198 ms), certified to 22 blocks. That family retired
  *speculative* ∀-expansion — expanding a block whose result goes back
  to the loops rather than to the core — which cost 22 s where the
  loops alone take 31 ms, and it located the next bottleneck: the
  composed strategy triples in size per alternation because
  composition deep-clones sub-strategies instead of sharing them.
  Beyond the suite, the dispatch paths cross-validate each other
  (`--no-expansion`) on 701 multi-block `reduction-finding` instances:
  591 decided, **all agreeing**, zero disagreements. Satisfiable
  answers now carry a **composed winning strategy**
  (`alternation::solve_certified`) built from the pipeline's own
  pieces — simplification's forced literals, an ∃-loop's winning
  constants, a ∀-loop's per-cube sub-strategies, and the core's
  certified Skolem models at the leaves — rendered as an AIGER
  strategy circuit (`Strategy::to_aiger`) through the same builder the
  2QBF emitter uses, verified by a SAT check
  (`alternation::verify_strategy`, one query per matrix clause against
  one solver that keeps the circuit and everything it learns — 3.7x
  faster than the single query over all of them) as well as
  exhaustively in the
  fuzz, and available for *every* satisfiable result now that
  ∀-expansion is inverted too (`Strategy::Expanded` replays the
  renaming of the copy the actual assignment of the enumerated block
  selects). Design rationale and the algorithm survey
  (dependency-aware ID, expansion, hybrids) in `RESEARCH.md` (RQ6).

* **Safety games without unrolling — done** (`aiger::solve_safety`):
  the winning region starts as every state and is shrunk by
  counterexample until `W = CPre(W)`, over a query that stays ∀∃ at
  any game depth. Every refinement is a pure addition, so the loop
  rides the in-place continuation; the counterexample is the core's
  verified universal witness, so a whole cube leaves the region per
  round. Answers *unbounded* realizability with a winning region —
  `arbiter-2-2` in 1.9 ms and 5 rounds, where the reactive unrolling
  needs 1.3 s for depth 11 alone. Runs in the classical two phases
  (safe states, then backward induction), and minimizes the
  counterexample *toward the state variables*
  (`IncDet::unsat_witness_minimized`) since the environment's move is
  projected away — worth 107x on the game benchmark, with `ring-4`'s
  losing region dropping from 112 cubes to 15. Each round's constraint
  lives in a pushed frame rather than under an activation literal, so
  the clauses learnt under it are dropped when it is retired instead
  of outliving it (a further 2.4x, and it removed the in-place
  regression that made rebuilding faster). Validated against an
  explicit backward fixpoint on 20k random circuits, region and all.
  See `RESEARCH.md` (RQ5).

* **Complete winning-move extraction — done**
  (`IncrementalSolver::universal_witness_complete`): when the recorded
  heuristic move fails verification, the move is re-derived by
  self-reduction over the universal variables (one restricted
  throwaway solve each), then minimized over the variables the caller
  can use. Closes the RQ3 synthesis gap (`sat` without a model) and
  replaces the hand-rolled backstop the game refinement needed.
  Validated by replaying 12 575 extracted moves against brute force in
  the incremental differential harness.

### 2. Certificates

* **Skolem function verification — done**
  (`IncDet::verify_skolem_functions`, CLI `--certify`): every assigned
  variable has the uniform function "assigned polarity iff one of its
  implication clauses fires", the trail provides a topological order, and
  a SAT check refutes the existence of a universal assignment falsifying
  the matrix under these functions. The differential fuzz harness verifies
  the functions of every satisfiable result, and all satisfiable instances
  of the CADET suite certify.
* **Skolem function output — done** (`SkolemModel::to_aiger`, CLI
  `--strategy <path>`): the piecewise Skolem functions are emitted as a
  *strategy circuit* in ASCII AIGER — universal variables as inputs,
  every defined existential as an output — mirroring the region
  structure of the model (first handled region whose cube holds wins,
  the final chain covers the rest) with a constant-folding AIG builder.
  Validated by a proptest simulating the emitted circuit on every
  universal point against the pointwise model evaluation (which the
  differential harness checks against the matrix), with aggressive
  case splitting so region selection is exercised, and externally by a
  Python simulator sampling the CADET suite's satisfiable instances:
  42/42 parseable instances check out (the remaining two are QAIGER
  inputs the external checker does not parse; verified by hand). The
  external sweep found a real emitter gap: a CEGAR *response* can
  cover a variable the final solver state leaves unassigned, and both
  emitters dropped such region-only variables — `to_smtlib`'s
  `get-model` had the same latent bug. Both now emit the union of
  defined variables (unconstrained outside the defining regions,
  emitted as constant false there).
* **QRAT refutation proofs — done** (`Options::proof`, CLI
  `--proof <path>`, checker binary `qrat_check`): unsatisfiable results
  emit a standard-format QRAT proof, checked by the in-tree checker
  (`qrat::check_refutation`) on every UNSAT instance of the
  differential fuzz (7 families × 20k cases) and on the CADET suite
  (47 of the supported UNSAT instances valid, one timeout). Proof mode
  disables CEGAR and case splits — their cube exclusions are justified
  game-theoretically by recorded strategies, which clausal rules cannot
  express — and everything else is checkable: learnt clauses are linear
  resolution-chain conclusions (RUP by construction, preserved by
  clause minimization); forced root constants are RUP units; *pure*
  constants are QRAT unit additions (every clause containing the
  opposite literal is satisfied by an earlier constant unit, making
  each outer resolvent an asymmetric tautology) — and a non-root pure
  constant discarded by backtracking emits a *deletion* line, so a
  later opposite constant stays justifiable (the fuzz caught exactly
  this as contradictory unit lines); reduce-DB deletions emit deletion
  lines; the two pointwise UNSAT sites (root conflict, analysis with
  only root existentials) are completed to a clause without existential
  literals by resolving along the trail with the implications that fire
  under the conflicting assignment, which universal reduction then
  empties. The checker implements RUP with scope-aware universal
  reduction and the unit-QRAT rule (tautologies dropped as inert, the
  same normalization the solver's preprocessing applies). The old
  half-finished `qrat` parser stub was removed, superseded by the
  emitter and checker.
* **Certificates beyond 2QBF — done**
  (`alternation::Strategy`, `solve_certified`, `verify_strategy`, CLI
  `--certify` / `--strategy` on any prefix depth): a satisfiable
  answer to a prefix with more than two blocks carries a winning
  strategy composed out of the pipeline, rendered in the same AIGER
  format as a 2QBF result and checked by SAT — the
  exhaustive pointwise check the fuzz uses cannot survive a
  47-variable universal block. All 19 solved satisfiable multi-block
  instances of the CADET suite certify, by the internal check and
  independently by the external AIGER simulator. See `RESEARCH.md`
  (RQ6).
* **Where the safety refinement's time goes — measured**
  (per-round tracing in `aiger::solve_safety`, `det_check_time` and
  `global_check_time` in the core statistics, core options A/B-able
  from the environment in `bench_games`): on `game-arbiter-4-4`, the
  benchmark's one expensive game, witness extraction is 0.1% of the
  run and one round of 57 spends 52 s inside the core, 72% of it in
  the complete conflict check — 42 472 calls at ~890 µs, of which 81%
  prove there is *no* conflict. The defaults beat every alternative
  tried (case splits are worth 7x despite closing no cases; CEGAR
  halves the fallback rounds; restarts change nothing at all). See
  `RESEARCH.md` (RQ5).

* **Structure sharing in composed strategies — done**
  (`alternation::Strategy` over `Rc`, `Strategy::gates`): the
  recursion's memo hands back a shared node instead of a deep copy, so
  the strategy is the DAG it always was — `arbiter-2-2` at 24 blocks
  goes from 41 289 049 nodes to 975, geometric growth to linear. The
  circuit compiled from it is shared too, keyed on the variables a
  node's subtree actually mentions rather than on the whole value
  accumulator (which finds no sharing at all): 19 984 296 gates to
  4 508 at the same depth, and `lights3_021_0_009` certifies in 0.98 ms
  where it took 33 s. See `RESEARCH.md` (RQ6).

### 3. Performance

Done in the performance pass (see `src/bin/bench.rs`; run with
`cargo run --release --bin bench`):

* **Determinacy checks** no longer build a SAT solver: the formulas are tiny
  and local, so a budgeted DPLL (`incdet::determinacy`) decides almost all
  checks directly, falling back to a solver only when the budget runs out.
  A shared incremental solver with guard literals was tried first and was
  8x *slower* than the per-check solver on propagation-heavy instances —
  the checks are too local for a global solver to pay off.
* **Conflict checks**: the SAT-based local pre-check was replaced by a
  syntactic pairwise-compatibility check (ignoring global constraints,
  "both polarities can fire" holds iff some pair of implication clauses of
  opposite polarity has no clashing literals). The incremental global check
  reuses activation literals and fire arbiters cached per (clause, implied
  literal) instead of re-encoding every implication clause with fresh
  variables on every check, and variable mappings are kept stable across
  backtracking (the checked variable is scrubbed from the returned model
  since it carries no meaningful value).
* The special decision handling in the conflict check turned out to be
  semantically redundant (a fired implication of the decided polarity
  contradicts "no implication of the decision fires"), so the check is the
  same for decisions and propagations and the encoding was removed.
* **Model extraction** is linear now (was quadratic), and implication counts
  are cached.

Effect (A/B against the pre-optimization solver, 18 random instances,
150s timeout): solved instances 15/18 → 17/18, and the instances solved by
both got ~20x faster in aggregate (282s → 14s); `parity-1000` went from
46ms to ~4ms. Note that conflict-heavy instances show large search
variance — the learned clauses depend on which model the conflict check
happens to return — so only aggregate comparisons over many instances are
meaningful. The remaining time on conflict-heavy instances is dominated by
the incremental global conflict checks, of which only ~13% find an actual
conflict.

Three further ideas were implemented, benchmarked, and rejected as
defaults — recorded here so they are not retried naively:

* **CaDiCaL as conflict-check backend** (feature `cadical`, kept as an
  optional backend): correct under certified fuzzing, but slower in
  aggregate on the hard random instances (147s → 210s+ with one new
  timeout; individual instances swing both ways) and no improvement on
  the two suite timeouts. The conflict-check workload is many small
  assumption-solves on a growing formula, where varisat's low per-call
  overhead beats CaDiCaL's stronger-but-heavier core, mirroring the
  earlier CryptoMiniSat result. Worth retrying together with the
  conflict-check solver reboot, where per-solve formula sizes change.

* **No-conflict verdict caching**: "no conflict" verdicts are monotone
  along a branch (constraints only grow), so they can be cached and
  invalidated by per-variable implication epochs plus level incarnation
  ids. Sound (fuzz-verified), but the hit rate was only ~4% — propagation
  waves touch most variables' implication sets — and skipping solver calls
  perturbs the incremental solver state enough that the search got slower
  on balance.
* **BDDs for the conflict check — measured, not adopted** (`src/bdd.rs`,
  a minimal ROBDD package with a node budget). Carrying Skolem
  functions as BDDs over the universals makes the check a pointer
  comparison and hands back the whole conflicting set instead of one
  assignment, so the only question is representation size. On 22 of 24
  RQ1/RQ3 families the BDDs are under 130 nodes and the check would be
  free; on two-operand arithmetic the prefix order is the textbook
  exponential (>10^6 nodes at 16 bits) and the interleaved order the
  textbook linear (194 at 64 bits) — a factor over 5 000 decided by a
  permutation, on exactly the family ID solves order-obliviously with
  zero decisions. The region numbers are friendlier (`arbiter-4-4`: 59
  BDD nodes against an ideal 53-cube cover and the 75 cubes the loop
  builds). Measured again on the population that actually matters —
  the *live* conflict-check state during real solves, sampled by
  `ConflictCheck::trail_bdd` under a one-million-node budget, on the
  CADET suite and QBFEVAL'17: 70 of 72 CADET states fit with a **median
  peak of 7 nodes**, but `adder2` needs 169 053 and `bug10rr(r)` and
  three of five QBFEVAL instances exceed a million. The BDD is cheap
  where the check is already cheap and explodes on arithmetic, which is
  the structure ID handles best. Verdict in `RESEARCH.md`: not a
  replacement; defensible only as a budgeted accelerator, with a low
  ceiling.
* **Conflict hints** (`Options::conflict_hints`, kept but off by
  default): re-try the universal values a recent conflict came back
  with, pinned as assumptions, before searching freely — sound in one
  direction, since assumptions only restrict the query. The hint is
  right 0–12% of the time, because conflict analysis and CEGAR have
  just made that very assignment impossible, and a hit is *also* a
  loss: the model found under a pin is more constrained, so it
  generalizes to a worse cube. 2.5x slower on `corridor-4-stay`,
  neutral elsewhere. Covered by the differential option sweep so the
  path cannot rot into an unsound one.
* **Luby restarts** (`Options::restarts`, kept but off by default): on the
  random suite restarts lost about 2x in aggregate at both base intervals
  100 and 500. Unlike in a SAT solver, a restart discards the level-tagged
  implication structure, and rebuilding it costs SAT-based determinacy and
  conflict checks rather than cheap unit propagation. Worth re-evaluating
  on QBFEVAL instances together with phase saving.

Remaining performance work:

* **Sharper conflict gating — closed**: the syntactic pair check was
  suspected of being weak; it is not. It rejects 80% of candidates and
  *every* two-sided definition among them, which is the whole
  conflict-free population it can decide syntactically. What survives
  is the genuinely uncertain remainder, and the profile says the
  surviving positives are where the time is. Three follow-ups —
  localizing the query to a cone, guessing it from remembered
  conflicts, and batching it per epoch — are all measured and rejected;
  see `RESEARCH.md`. The residual finding is that ID spends about one
  complete check per decision, so the check is the algorithm's unit of
  work rather than an overhead on it.
* **Cone-of-influence reduction — measured and rejected**: only clauses
  of variables in the transitive premise cone of the checked variable
  are relevant, but the cone is 56–84% of the determinized formula on
  every family where the check is expensive (84% on `arbiter-4-4`, 76%
  on `corridor-4-stay`). It does shrink with formula size where the
  formula grows without the game changing — 65% → 22% across
  `arbiter-2-2` … `arbiter-2-16` — but those instances solve in
  milliseconds. See `RESEARCH.md`; the probe is `check_cone`, behind
  the `probe` feature.
* **Watch bookkeeping**: `propagate_function` scans watch lists to find and
  move watched literals; storing the two watched literals per clause would
  make this O(1). Not measurable on current benchmarks, worth revisiting
  with clause databases that have longer clauses.
* **Clause database management — done**
  (`Options::clause_deletion`, default on): every 2000 learnt clauses the
  less active half of those not currently registered as implications
  (tracked by lock reference counts in the allocator) is deleted. Clause
  activities are bumped for every reason clause used during conflict
  analysis with a geometric per-conflict decay (MiniSat-style); activity
  ties are broken towards deleting longer clauses, which subsumes the
  earlier length-based policy for never-used clauses. Bench-neutral
  (within the run-to-run noise), and long-running instances keep a
  bounded clause database. The residual progressive slowdown on the
  suite timeouts lives in the *incremental conflict-check solver*, which
  cannot shed retired clauses; this is addressed by a periodic **solver
  reboot** that rebuilds the incremental solver by replaying the trail
  definitions (and handled-case exclusions) every 512 global checks.
* **Eager clause retirement removed — 2.4x on the benchmark suite**:
  stack sampling on `adder2` showed two thirds of the time inside the
  incremental conflict check, dominated by the backend's unit
  simplification. Every check used to retire its per-check clauses with
  a fresh unit clause, and every backtrack retired the dropped level
  guards the same way — each unit making varisat re-simplify its whole
  clause database. Both are now left inert behind their (never assumed
  again) guards until the reboot sheds them, and single-implication
  polarities skip the per-check clause entirely by passing the fire
  arbiter as an assumption. Benchmark aggregate 1.2s → 0.5s; after this
  the conflict check is genuinely solving-bound (the samples sit in the
  backend's CDCL loop, no simplification overhead left).
* **Benchmarking on real instances**: the solver is validated against the
  CADET integration-test suite (117 QDIMACS instances with known results):
  **84 correct, 0 wrong, 0 panics, 0 timeouts** at 30s since frontier
  CEGAR (see above), 33 unsupported (more than one quantifier
  alternation). Case assumptions are kept **sticky**: conflicts whose
  learnt clause bottoms out at root-assigned existentials must backtrack
  to the root (see the case-split section), which used to prune the
  assumption before a second one could stack; assumptions are now
  committed until their case closes and re-assumed once propagation
  settles after such a backtrack. Getting this suite to run also required
  QDIMACS free-variable support and header tolerance. QBFEVAL 2QBF tracks
  would give a competitive comparison against CADET/DepQBF. A direct
  per-instance timing comparison against a locally built CADET over the
  suite stood at 4.2s vs 1.3s aggregate, with `bug10rr.qdimacs` as the
  outlier (722ms vs 21ms: CADET finished with 147 decisions and a single
  conflict where booleanium needed 441 CEGAR cases; initial propagation
  is identical, so the gap was decision *phase*). Unconditionally firing
  implications found by the determinacy check are now propagated as
  *constants* rather than generic functions, so they cascade (satisfy
  and shorten clauses) in every downstream check.
* **Response-guided decision phase — done, 1.6x on the suite aggregate**
  (2.6s vs the 4.2s above; bug10rr 722ms → 30ms, on par with CADET, and
  `test_sat.qdimacs` now beats CADET 5ms vs 615ms): decisions follow the
  most recently recorded CEGAR response where it assigns the variable —
  the response is a winning existential move for the current search
  region, so deciding consistently with it avoids re-conflicting there —
  and default the variable to *true* otherwise (the trail literal is the
  negation of the intended default, since a decided literal holds only
  when one of its implications fires). The heuristic space here is
  non-linear: the previous structural rule (assign the side with fewer
  implication literals), constant default-true alone, response phase
  with the structural rule as fallback, and implication-count-gated
  variants were each measured and are all worse in aggregate — the last
  two each blew a different instance up by 10-60x — while this
  combination dominates everywhere except `adder2` (127ms → 559ms,
  accepted against the aggregate win). CADET's Jeroslow-Wang phase
  (active only after 3 restarts) was inspected but not adopted; its
  pre-restart constant default-true is what solves most of its suite.
* **QBFEVAL'17 2QBF track evaluation** (385 competition instances, up to
  2.5M clauses; corpus mirrored in the `arey0pushpa/synthetic_qbf_formulas`
  GitHub repository — qbflib.org is offline and the JKU mirror is outside
  this environment's network policy): at a 10s timeout on 4 cores,
  booleanium solves 134 of 384, a locally built CADET 207. **Zero verdict
  disagreements** on the 119+ instances both solve, and zero abnormal
  exits — real-instance differential evidence on top of the fuzzing.
  Eleven instances are solved by booleanium but not CADET. The gap is
  concentrated in families: `stmt` (38 CADET-only before the pure-literal
  rule below), `sortnetsort` (9), `rankfunc` (8), and the `*-fixpoint`
  families.
* **Pure-literal rule — done** (motivated by the `stmt` family: CADET
  solves `stmt27_93_98` in 44ms with 280 pure variables cascading into
  1679 constant propagations and an interface of *three* variables): a
  literal is pure if every original clause containing it is either
  registered as one of its own implication clauses or satisfied by a
  constant; the variable can then take the minimal function "literal iff
  one of its implications fires" without loss (clauses of the pure
  literal are satisfied by construction, every other clause profits from
  the opposite literal holding maximally, and any winning strategy can be
  rewritten accordingly). With no implications at all this is the classic
  pure-literal rule and yields a *constant*, which cascades. Purity is
  re-checked event-driven (implication registered, clause satisfied by a
  constant, assignments unwound) via static occurrence lists, and pure
  assignments take precedence over decisions. The certified fuzz harness
  caught one soundness bug during development — backtracking fed unwound
  *universal* case assumptions into the pure queue, and the rule assigned
  a universal as a constant. Results: `stmt27_93_98` timeout → 1.5s,
  `stmt53_296_346` timeout → 4s, five `sortnetsort` instances unlocked
  (previously all CADET-only); net +4 on the QBFEVAL'17 track at 10s
  (130 → 134) with a few marginal instances shuffling across the timeout
  cliff in both directions, and no change on the CADET suite (84 of 84
  certified) or the random benchmarks. Remaining refinement: CADET's
  *enhanced* purity (disregarding clauses that are blocked by the
  literal), which its stats suggest is what carries the remaining `stmt`
  stragglers.
* **The (former) timeout instances, and what actually fixed them**: stack
  sampling first
  suggested XOR-hard conflict checks, so the optional CryptoMiniSat
  backend was made buildable (git binding plus C++14 flags in
  `.cargo/config.toml`), wired in as the conflict-check solver behind the
  `cryptominisat` feature, and root-level definitions are now added as
  raw unguarded clauses so the backend can detect structure (both
  fuzz-validated; no regression for the default varisat backend). Neither
  helped, and a re-test after the eager-retirement removal (when the
  check became solving-bound and the query pattern moved to assumptions)
  confirmed the negative: CryptoMiniSat reaches ~6k conflicts per minute
  on `adder2` against varisat's ~9k — the workload is many small
  incremental queries, where per-solve overhead outweighs XOR reasoning.
  Progress logging shows `adder2` grinding
  with only 209 of 515 variables initially deterministic — consistent
  with a one-sided (Plaisted–Greenbaum-style) clause encoding, where
  gate variables have implications in only one polarity and incremental
  determinization degenerates into plain search. A **one-sided function
  rule** (decide the polarity with the non-empty implication set, giving
  the natural gate function) was implemented and rejected by measurement:
  it did not speed up the circuit instances and slowed the random suite by
  an order of magnitude. Progress logging further shows a **progressive
  slowdown** as learnt clauses accumulate in the implication sets that
  every determinacy check processes (the gap between 1024-conflict
  milestones grows 4s → 13s within 30s of solving), which made
  **learnt-clause deletion** look like the highest-leverage fix (since
  done, see above). In the end none of the per-conflict work was the
  answer for `adder2`: what CADET does differently is not searching
  faster but searching *exponentially less*, via frontier CEGAR (see the
  algorithm section) — a comparison run of CADET needs 120 conflicts
  where the grind needed tens of thousands. The moral for future
  bottlenecks: compare the *number* of conflicts against CADET before
  optimizing their cost.
* **Conflict-check model reuse — deprioritized by profile**:
  `Conflict::assignment` is a `HashSet<Lit>` rebuilt per conflict. Stack
  sampling after the eager-retirement removal shows the time in the
  backend's CDCL loop, not in model extraction or hashing, so this
  refactor would not be measurable; revisit only if a profile ever shows
  it.

* **Re-validated after the interface work** (the term API, the
  `solve_safety` port onto it, the frame-scoped gate cache): the CADET
  alternation suite is unchanged at **125 correct with the same single
  give-up** (`biu`), and **all 19** satisfiable multi-block instances
  still certify. The 2QBF core benchmark returns the expected verdicts
  throughout. Worth stating explicitly because the changes reached into
  `incremental.rs`, which every frontend sits on, and nothing in the
  safety-game work should have been able to move those numbers — the
  point of running them is that "should not" is not a measurement.

### 3b. Open directions (see `RESEARCH.md` for the reasoning)

Recorded from the solver-landscape review, roughly in leverage order:

* **The control for RQ5 — run, and the solver loses 11x to 356x**
  (`bench_games control`): the same fixpoint driven by two competing
  SAT solvers over the same circuit, sharing no code with the solver.
  Two independent causes, both actionable. Cube quality: the control's
  unsat-core generalisation is *optimal* on the pursuit games (4 and 6
  cubes against near-minimal covers of 4 and 6) where greedy dropping
  from a complete move finds 15 and 64. Seeding the minimization from
  the solver's own unsat core was tried and **rejected by measurement**
  (`ring-6` 238 ms to 15 s); the control's core comes from a tight
  query over the region, not from the whole loaded stack, so the fix is
  the circuit-level interface rather than the extraction. And per-round
  cost: `arbiter-3-3` matches the control's rounds and cubes and is
  still 70x slower.
* **A circuit-level construction interface** for that fixpoint —
  hand over the transition relation once as gates, let the solver own
  the region (canonical, shared, subsumption-aware) instead of the
  caller hand-Tseitining a 55-deep membership chain out of clauses.
* **Preprocessing** (Bloqqer/HQSpre-style), with the definition-
  preservation experiment run *first*: blocked-clause elimination can
  destroy exactly the gate structure ID runs on. Being fast on QDIMACS
  is a requirement, so this is not optional — but neither is keeping
  satisfiable answers certified through it.
* **Clausal abstraction** as one calculus containing both search and
  expansion, replacing the alternation front-end's ∃-loop, ∀-loop and
  expansion-budget dispatch.
* **Dependency-scheme survey** (cheap, prior against it, decisive
  either way).
* **Full-solver QRAT** via extension variables for CEGAR cases.

### 4. Robustness / cleanup

* Replace the recursive `is_literal_redundant` with an explicit stack (the
  recursion is bounded by trail depth, but deep instances could still
  overflow the stack).
* `cli.rs` parses arguments by hand and now only serves the secondary
  `qdimacs` binary; the main CLI is `clap`-derived with every
  `incdet::Options` field wired. Fold the one remaining user over or
  drop it.
