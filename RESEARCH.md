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

Mapping onto the existing machinery, and what breaks:

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

## RQ3 — SMT-LIB as the surface language

Even restricted to the Boolean/BV fragment, SMT-LIB answers both format
and interface at once:

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
