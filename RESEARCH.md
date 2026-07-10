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
* QCIR support is the natural next frontend (richer gates than AIGER,
  the QBF community's standard for structured instances).

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
  incremental games loop.
* Concretely next, in-place *monotone* continuation: between solves
  that only added clauses, keep the live solver — retain the root
  trail (root assignments stay forced under a superset matrix), learnt
  clauses, and VSIDS, but invalidate handled cases and their
  conflict-check exclusions (a recorded response need not satisfy new
  clauses) and re-queue determinacy. The blocker is bookkeeping:
  `original_clause_count` is a prefix index today and must become an
  explicit set once originals arrive after learnt clauses; the
  `_add_clause` load path assumes an unassigned world. Measure against
  the carrying baseline on an unrolling workload before committing.

## RQ3 — SMT-LIB as the surface language

**Status: a Boolean-fragment frontend exists** (`src/smtlib.rs`,
auto-detected by the CLI): `declare-const`/`declare-fun` (nullary
Bool), `define-fun` as the definition-level input, assertions over
`and`/`or`/`not`/`=>`/`=`/`xor`/`ite` with hash-consed Tseitin gates,
`(assert (forall (...) (exists (...) body)))`, `push`/`pop`/
`check-sat`/`check-sat-assuming`, and `get-model` printing the
piecewise Skolem functions as `define-fun`s parameterized by the
universal variables. Free constants are solved in the innermost block
(truth-equivalent as long as they do not occur *under* a forall, which
is rejected — that shape needs three blocks, see below). Remaining
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
* **The 3-block gap that matters for synthesis**: the natural bounded
  synthesis shape is ∃ parameters ∀ inputs ∃ gates(determined), which
  the 2QBF core rejects as three blocks even though the innermost block
  is deterministic by construction. Supporting "∃∀∃ with a defined
  third block" is the highest-value core extension for the SYNTCOMP
  direction: the inner block never needs decisions, only
  determinization — the machinery is arguably already there.

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
to push levels, the winning-strategy extraction maps to `get-model`,
and the incrementality between depths is where the interface (RQ2/RQ3)
earns its keep — none of which a one-shot QDIMACS call can express.

* Competition/baselines: Z3's quantifier engines, Yices `ef-solve`,
  SyGuS solvers. The niche for an ID-based engine is structure
  exploitation plus *certified* function output plus incrementality.
* Benchmark plan: SYNTCOMP safety specifications reduced to per-depth
  ∀∃ queries; compare one-shot re-solving vs incremental push/pop to
  quantify what incrementality is worth end to end.
* Open question: which of the derived artifacts (learnt clauses,
  handled cases, Skolem fragments) transfer across game depths — the
  RQ2 dependency-tracking question is exactly the "how much does the
  solver remember between rounds of the game" question.

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
