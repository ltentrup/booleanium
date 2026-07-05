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

### 2. Certificates

* **Skolem function extraction** for SAT results: the data is already there —
  per-variable implication clauses plus decision defaults, in trail order.
  Emit as AIGER or as a QDIMACS-model-like format, and verify in tests by
  substituting into the matrix (a stronger oracle than result comparison).
* **QRAT / clausal proofs** for UNSAT results: the `qrat` module (currently
  commented out in `lib.rs`) was started for this; learned clauses are
  resolvents, so logging them in order should yield checkable proofs.

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

Remaining performance work:

* **Sharper conflict gating**: the syntactic pair check filters only ~10% of
  global checks; investigate stronger cheap filters (e.g. incorporating
  determined constants/functions of premise variables, or caching
  compatible-pair witnesses across checks of the same variable).
* **Cone-of-influence reduction** for the rebuilt (non-incremental) global
  check: only clauses of variables in the transitive premise cone of the
  checked variable are relevant.
* **Watch bookkeeping**: `propagate_function` scans watch lists to find and
  move watched literals; storing the two watched literals per clause would
  make this O(1). Not measurable on current benchmarks, worth revisiting
  with clause databases that have longer clauses.
* **Clause database management**: learned clauses are never deleted and the
  allocator never shrinks; add activity-based deletion and restarts
  (the Varisat-inspired infrastructure — `clause::alloc`, VSIDS — is
  prepared for this).
* **Benchmarking on real instances**: evaluate on QBFEVAL 2QBF tracks
  against CADET/DepQBF, and profile the split between determinacy checks,
  conflict checks, and clause learning (`Statistics` already counts these).
* **Conflict-check model reuse**: `Conflict::assignment` is a `HashSet<Lit>`
  rebuilt per conflict; a `VarVec`-based assignment would avoid hashing in
  the hot path of conflict analysis.

### 4. Robustness / cleanup

* Replace the recursive `is_literal_redundant` with an explicit stack (the
  recursion is bounded by trail depth, but deep instances could still
  overflow the stack).
* `qrat` module: revive or remove.
* Wire `incdet::Options` into the CLI (`clap` is already a dependency but
  `cli.rs` parses arguments by hand).
