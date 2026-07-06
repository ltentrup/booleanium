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

* **Skolem function verification — done**
  (`IncDet::verify_skolem_functions`, CLI `--certify`): every assigned
  variable has the uniform function "assigned polarity iff one of its
  implication clauses fires", the trail provides a topological order, and
  a SAT check refutes the existence of a universal assignment falsifying
  the matrix under these functions. The differential fuzz harness verifies
  the functions of every satisfiable result, and all satisfiable instances
  of the CADET suite certify.
* **Skolem function output**: emit the verified functions in a standard
  format (AIGER) instead of only checking them internally.
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
* **Luby restarts** (`Options::restarts`, kept but off by default): on the
  random suite restarts lost about 2x in aggregate at both base intervals
  100 and 500. Unlike in a SAT solver, a restart discards the level-tagged
  implication structure, and rebuilding it costs SAT-based determinacy and
  conflict checks rather than cheap unit propagation. Worth re-evaluating
  on QBFEVAL instances together with phase saving.

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
* **Clause database management — partially done**
  (`Options::clause_deletion`, default on): every 2000 learnt clauses the
  longer half of those not currently registered as implications (tracked
  by lock reference counts in the allocator) is deleted. No regression on
  the benchmark suite, and long-running instances keep a bounded clause
  database. The residual progressive slowdown on the two suite timeouts
  lives in the *incremental conflict-check solver*, which cannot shed
  retired clauses; the follow-up is to periodically rebuild that solver
  from the live definitions (a "solver reboot"), and to refine the
  deletion heuristic (activity/LBD instead of length).
* **Benchmarking on real instances**: the solver is validated against the
  CADET integration-test suite (117 QDIMACS instances with known results):
  82 correct, 0 wrong, 0 panics, 2 timeouts at 30s (`bug8.qdimacs`,
  `adder2.qdimacs`, both UNSAT), 33 unsupported (more than one quantifier
  alternation). Getting this suite to run also required QDIMACS
  free-variable support and header tolerance. QBFEVAL 2QBF tracks would
  give a competitive comparison against CADET/DepQBF.
* **The two timeout instances are search-bound**: stack sampling first
  suggested XOR-hard conflict checks, so the optional CryptoMiniSat
  backend was made buildable (git binding plus C++14 flags in
  `.cargo/config.toml`), wired in as the conflict-check solver behind the
  `cryptominisat` feature, and root-level definitions are now added as
  raw unguarded clauses so the backend can detect structure (both
  fuzz-validated; no regression for the default varisat backend). Neither
  helped: progress logging shows `adder2` grinding at ~250 conflicts/s
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
  milestones grows 4s → 13s within 30s of solving), which makes
  **learnt-clause deletion** the highest-leverage remaining fix for these
  instances.
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
