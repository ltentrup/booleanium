//! Benchmark for the incremental determinization solver on structured and
//! random 2QBF families. Run with `cargo run --release --bin bench`; set
//! `RUST_LOG=info` to additionally see the solver statistics per instance.

use booleanium::{
    incdet::{IncDet, Options},
    qcnf::QCNF,
    QuantTy, SolverResult,
};
use std::time::Instant;

/// Deterministic xorshift RNG so benchmark instances are reproducible.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn flip(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

/// Parity chain: ∀ u_1..u_n ∃ x_1..x_n with x_1 ↔ u_1 and
/// x_i ↔ x_{i-1} ⊕ u_i. Every x_i is uniquely determined, so the family
/// measures the throughput of determinacy checks and function propagation.
/// The `unsat` variant additionally forces x_n to be constant true, which
/// triggers a conflict whose global check spans the whole chain.
fn parity(n: i32, unsat: bool) -> QCNF {
    let universals: Vec<u32> = (1..=n as u32).collect();
    let existentials: Vec<u32> = (n as u32 + 1..=2 * n as u32).collect();
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    // x_1 <-> u_1
    matrix.push(vec![-1, n + 1]);
    matrix.push(vec![1, -(n + 1)]);
    for i in 2..=n {
        let (u, x, xp) = (i, n + i, n + i - 1);
        // x <-> xp xor u
        matrix.push(vec![xp, u, -x]);
        matrix.push(vec![-xp, -u, -x]);
        matrix.push(vec![-xp, u, x]);
        matrix.push(vec![xp, -u, x]);
    }
    if unsat {
        matrix.push(vec![2 * n]);
    }
    build(&[(QuantTy::Forall, universals), (QuantTy::Exists, existentials)], matrix)
}

/// Random 2QBF with `k` universals, `m` existentials, and `c` clauses of
/// 3 to 5 literals. Exercises decisions, conflicts, and clause learning.
fn random(k: u64, m: u64, c: u64, seed: u64) -> QCNF {
    let mut rng = Rng(seed);
    let universals: Vec<u32> = (1..=k as u32).collect();
    let existentials: Vec<u32> = (k as u32 + 1..=(k + m) as u32).collect();
    let mut matrix = Vec::new();
    for _ in 0..c {
        let len = 3 + rng.below(3);
        let mut clause = Vec::new();
        for idx in 0..len {
            // the first literal is always existential so that universal
            // reduction cannot produce the empty clause; the remaining
            // literals are universal roughly one time in three
            let var = if idx > 0 && rng.below(3) == 0 {
                1 + rng.below(k) as i32
            } else {
                (k + 1 + rng.below(m)) as i32
            };
            clause.push(if rng.flip() { var } else { -var });
        }
        matrix.push(clause);
    }
    build(&[(QuantTy::Forall, universals), (QuantTy::Exists, existentials)], matrix)
}

fn build(prefix: &[(QuantTy, Vec<u32>)], matrix: Vec<Vec<i32>>) -> QCNF {
    let prefix: Vec<(QuantTy, &[u32])> = prefix.iter().map(|(q, v)| (*q, v.as_slice())).collect();
    let matrix: Vec<&[i32]> = matrix.iter().map(Vec::as_slice).collect();
    QCNF::new(&prefix, &matrix)
}

fn run(name: &str, qcnf: &QCNF) {
    // an optional argument selects instances by substring match
    if let Some(filter) = std::env::args().nth(1) {
        // a trailing `$` anchors the filter to the full instance name
        let matches = match filter.strip_suffix('$') {
            Some(exact) => name == exact,
            None => name.contains(&filter),
        };
        if !matches {
            return;
        }
    }
    let mut solver = IncDet::from_qcnf_with_options(qcnf, Options::default());
    let start = Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();
    let result = match result {
        SolverResult::Satisfiable => "sat",
        SolverResult::Unsatisfiable => "unsat",
        SolverResult::Unknown => "unknown",
    };
    println!("{name:<32} {result:>7} {elapsed:>12.3?}");
}

fn main() {
    tracing_subscriber::fmt::init();
    let total = Instant::now();
    for n in [100, 400, 1000] {
        run(&format!("parity-sat-{n}"), &parity(n, false));
    }
    for n in [100, 400, 1000] {
        run(&format!("parity-unsat-{n}"), &parity(n, true));
    }
    let mut configs = Vec::new();
    for seed in 1..=12 {
        configs.push((10, 60, 220, seed));
    }
    for seed in 1..=6 {
        configs.push((12, 90, 330, seed));
    }
    for (k, m, c, seed) in configs {
        run(&format!("random-{k}-{m}-{c}-{seed}"), &random(k, m, c, seed));
    }
    println!("total: {:.3?}", total.elapsed());
}
