# Booleanium

An experimental QBF solver built on [Incremental
Determinization](https://link.springer.com/chapter/10.1007/978-3-319-40970-2_23)
(Rabe & Seshia, SAT'16) with the CAV'18 extensions — conflict-driven
CEGAR and universal case splits — and inspired by
[Varisat](https://jix.one/varisat/).

The core decides 2QBF. A recursive front-end lifts it to **any number of
quantifier alternations**, and satisfiable answers come back as
*functions*: Skolem functions for the existential player, checked before
they are handed over.

## What it does

**Input formats**, auto-detected:

| format | shape |
|---|---|
| QDIMACS | clauses, any prefix depth |
| QAIGER (ASCII AIGER) | combinational circuits, and sequential safety specifications |
| QCIR-G14 | prenex circuits, any prefix depth |
| SMT-LIB | Boolean fragment: declarations, `define-fun`, `push`/`pop`, `check-sat[-assuming]`, `get-model`, quantifier chains of any depth |

The circuit and SMT-LIB paths are *definition-level*: gates arrive as
definitions and keep both implication directions, so determinization
recovers them instead of reconstructing what a one-sided clausal
encoding threw away.

**Output.** A satisfiable verdict carries a strategy, and it is verified
rather than asserted:

- Skolem functions verified by a SAT call (`--certify`).
- Strategy circuits in ASCII AIGER (`--strategy`), universal inputs to
  existential outputs, under the input's own symbol names.
- The same strategy as SMT-LIB `define-fun`s (`get-model` in an SMT-LIB
  session).
- QRAT refutation proofs for unsatisfiable results (`--proof`), checkable
  by the in-tree `qrat_check`.

**As a library** (`src/incremental.rs`): an assertion stack with
`push`/`pop`/`add_clause`/`define_and`/`solve`/`solve_with_assumptions`
— the QBF analogue of IPASIR — with learnt clauses carried across
monotone extensions and an in-place continuation of the live solver.

**Safety games** (`src/aiger.rs`): `solve_safety` decides *unbounded*
realizability by refining a winning region until `W = CPre(W)`, over a
query that stays ∀∃ whatever the game's depth. Bounded unrollings are
available too, both the flat ∀∃ form and a reactive one with an
alternation per time step.

## Usage

```sh
cargo run --release --bin booleanium -- instance.qdimacs
```

The exit code is the verdict: 10 satisfiable, 20 unsatisfiable, 30
unknown. Input is read from the file argument, or stdin if omitted.

```sh
# check the Skolem functions and write the strategy circuit
booleanium --certify --strategy strategy.aag instance.qcir

# emit and check a refutation proof
booleanium --proof proof.qrat instance.qdimacs
qrat_check instance.qdimacs proof.qrat

# an SMT-LIB session
booleanium session.smt2
```

`--no-expansion` solves deep prefixes by the CEGAR loops alone. The two
dispatch paths share almost nothing, so running both is a differential
check on real instances.

## Testing

Correctness rests on differential testing against oracles that share no
code with the solver: brute force for clausal instances, direct circuit
evaluation for QAIGER and QCIR, recursive game evaluation for deep
prefixes, and an explicit backward fixpoint for safety games. Every
satisfiable result in the harnesses is certified, and composed
strategies are checked three independent ways — pointwise, through the
emitted AIGER text, and through the emitted SMT-LIB text.

```sh
cargo test --release
```

Benchmarks: `bench` (2QBF core), `bench_encodings` (input encodings),
`bench_incremental` (the assertion stack), `bench_games` (safety games,
both the unrollings and the region refinement).

## Status and limits

Decides all but one instance of the CADET integration suite, which the
reference solver does not decide either. Deep prefixes have been solved
and certified to 32 quantifier blocks on generated safety games.

Known limits: QRAT proofs are emitted only for 2QBF, and only in a mode
that disables CEGAR and case splits, whose derivations the clausal rules
cannot express. Theories are not implemented — the solver is Boolean.
Non-prenex quantifiers are rejected.

[PLAN.md](PLAN.md) tracks the implementation and its measurements;
[RESEARCH.md](RESEARCH.md) collects the open questions and the
experiments run against them, including the ones that failed.
