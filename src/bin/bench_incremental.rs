//! Benchmark for the incremental solving API on monotone (unrolling)
//! workloads: each step adds variables and clauses to the assertion stack
//! and re-solves, the access pattern of a bounded-model-checking or
//! synthesis loop. Every family runs twice — with in-place continuation
//! and with rebuild-per-solve — to measure what the continuation buys.
//! Run with `cargo run --release --bin bench_incremental`.

use booleanium::{incdet::Options, incremental::IncrementalSolver, SolverResult};
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

/// Unrolls the parity chain one step per solve: step `i` declares a fresh
/// universal `u_i` and existential `x_i` with x_1 ↔ u_1 and
/// x_i ↔ x_{i-1} ⊕ u_i, then re-solves. Everything stays deterministic,
/// so the family measures how much derived state the continuation saves
/// on a pure unrolling. The `unsat` variant forces the last x constant
/// true after the final step.
fn parity_unrolling(solver: &mut IncrementalSolver, steps: u32, unsat: bool) -> SolverResult {
    let mut result = SolverResult::Unknown;
    for i in 1..=steps {
        let (u, x) = (2 * i - 1, 2 * i);
        solver.declare_universal(u);
        solver.declare_existential(x);
        let (u, x) = (i32::try_from(u).unwrap(), i32::try_from(x).unwrap());
        if i == 1 {
            solver.add_clause(&[-u, x]);
            solver.add_clause(&[u, -x]);
        } else {
            let xp = x - 2;
            solver.add_clause(&[xp, u, -x]);
            solver.add_clause(&[-xp, -u, -x]);
            solver.add_clause(&[-xp, u, x]);
            solver.add_clause(&[xp, -u, x]);
        }
        result = solver.solve();
        assert_eq!(result, SolverResult::Satisfiable);
    }
    if unsat {
        solver.add_clause(&[i32::try_from(2 * steps).unwrap()]);
        result = solver.solve();
        assert_eq!(result, SolverResult::Unsatisfiable);
    }
    result
}

/// The parity unrolling with a temporary assumption query after every
/// step (probing a candidate value, as a synthesis loop would): queries
/// run on a throwaway solver, so the continuation of the plain solves
/// must survive them.
fn parity_unrolling_probed(solver: &mut IncrementalSolver, steps: u32) -> SolverResult {
    let mut result = SolverResult::Unknown;
    for i in 1..=steps {
        let (u, x) = (2 * i - 1, 2 * i);
        solver.declare_universal(u);
        solver.declare_existential(x);
        let (u, x) = (i32::try_from(u).unwrap(), i32::try_from(x).unwrap());
        if i == 1 {
            solver.add_clause(&[-u, x]);
            solver.add_clause(&[u, -x]);
        } else {
            let xp = x - 2;
            solver.add_clause(&[xp, u, -x]);
            solver.add_clause(&[-xp, -u, -x]);
            solver.add_clause(&[-xp, u, x]);
            solver.add_clause(&[xp, -u, x]);
        }
        result = solver.solve();
        assert_eq!(result, SolverResult::Satisfiable);
        // probe: can the newest chain output be forced constant true?
        let probe = solver.solve_with_assumptions(&[x]);
        assert_eq!(probe, SolverResult::Unsatisfiable);
    }
    result
}

/// The parity chain solved once, then repeated *scoped* re-solves: push
/// a clause-only frame, solve, pop. Retraction keeps the live solver
/// across the pops; without it every round rebuilds from scratch.
fn parity_scoped(solver: &mut IncrementalSolver, steps: u32) -> SolverResult {
    let mut result = parity_unrolling(solver, steps, false);
    for r in 0..steps {
        let i = r % steps + 1;
        let (u, x) = (i32::try_from(2 * i - 1).unwrap(), i32::try_from(2 * i).unwrap());
        solver.push();
        if i == 1 {
            solver.add_clause(&[-u, x]);
        } else {
            solver.add_clause(&[x - 2, u, -x]);
        }
        result = solver.solve();
        assert_eq!(result, SolverResult::Satisfiable);
        assert!(solver.pop());
    }
    result
}

/// Declares a fixed 2QBF variable set and feeds a random matrix in
/// chunks, re-solving after each chunk: the clause-refinement access
/// pattern (e.g. counterexample-guided loops adding constraints).
fn random_chunks(
    solver: &mut IncrementalSolver,
    k: u64,
    m: u64,
    clauses: u64,
    chunks: u64,
    seed: u64,
) -> SolverResult {
    let mut rng = Rng(seed);
    for v in 1..=k {
        solver.declare_universal(u32::try_from(v).unwrap());
    }
    for v in (k + 1)..=(k + m) {
        solver.declare_existential(u32::try_from(v).unwrap());
    }
    let mut result = SolverResult::Unknown;
    for chunk in 0..chunks {
        let count = clauses / chunks + u64::from(chunk == 0) * (clauses % chunks);
        for _ in 0..count {
            let len = 3 + rng.below(3);
            let mut clause = Vec::new();
            for idx in 0..len {
                // the first literal is always existential so that universal
                // reduction cannot produce the empty clause
                let var = if idx > 0 && rng.below(3) == 0 {
                    i64::try_from(1 + rng.below(k)).unwrap()
                } else {
                    i64::try_from(k + 1 + rng.below(m)).unwrap()
                };
                let var = i32::try_from(var).unwrap();
                clause.push(if rng.flip() { var } else { -var });
            }
            solver.add_clause(&clause);
        }
        result = solver.solve();
    }
    result
}

fn run(name: &str, workload: impl Fn(&mut IncrementalSolver) -> SolverResult) {
    if let Some(filter) = std::env::args().nth(1) {
        if !name.contains(&filter) {
            return;
        }
    }
    for continuation in [true, false] {
        let mut solver = IncrementalSolver::new(Options::default());
        solver.set_continuation(continuation);
        let start = Instant::now();
        let result = workload(&mut solver);
        let elapsed = start.elapsed();
        let result = match result {
            SolverResult::Satisfiable => "sat",
            SolverResult::Unsatisfiable => "unsat",
            SolverResult::Unknown => "unknown",
        };
        let mode = if continuation { "in-place" } else { "rebuild" };
        println!(
            "{name:<32} {mode:>8} {result:>7} {elapsed:>12.3?} (extensions: {})",
            solver.extension_count()
        );
    }
}

fn main() {
    tracing_subscriber::fmt::init();
    let total = Instant::now();
    for n in [50, 100, 200] {
        run(&format!("parity-unroll-sat-{n}"), |solver| parity_unrolling(solver, n, false));
        run(&format!("parity-unroll-unsat-{n}"), |solver| parity_unrolling(solver, n, true));
        run(&format!("parity-unroll-probed-{n}"), |solver| parity_unrolling_probed(solver, n));
        run(&format!("parity-scoped-{n}"), |solver| parity_scoped(solver, n));
    }
    for (k, m, c, chunks, seed) in
        [(10, 60, 220, 10, 1), (10, 60, 220, 10, 2), (12, 90, 330, 15, 1), (12, 90, 330, 15, 2)]
    {
        run(&format!("random-chunks-{k}-{m}-{c}-{seed}"), |solver| {
            random_chunks(solver, k, m, c, chunks, seed)
        });
    }
    println!("total: {:.3?}", total.elapsed());
}
