# Booleanium

An experimental QBF solver based on [Incremental Determinization](https://link.springer.com/chapter/10.1007/978-3-319-40970-2_23) and inspired by [Varisat](https://jix.one/varisat/).

The solver currently supports 2QBF (a single quantifier alternation). The core
algorithm is validated by differential testing against a brute-force oracle;
see [PLAN.md](PLAN.md) for the state of the implementation and the roadmap.

## Usage

Reads QDIMACS from a file argument or stdin and reports the result via the
exit code (10 = satisfiable, 20 = unsatisfiable):

```sh
cargo run --release --bin booleanium -- instance.qdimacs
```

## Testing

```sh
cargo test
# run the differential fuzz tests with more cases
PROPTEST_CASES=50000 cargo test --release incdet::test::fuzz
```
