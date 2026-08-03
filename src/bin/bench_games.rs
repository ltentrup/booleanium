//! End-to-end benchmark for the RQ5 positioning: SYNTCOMP-like safety
//! games unrolled into per-depth ∀∃ queries through the incremental API
//! (`aiger::Unroller`). Each family runs with in-place continuation and
//! with rebuild-per-solve to measure what the incremental stack is worth
//! on the access pattern of a bounded synthesis loop. Run with
//! `cargo run --release --bin bench_games`.

use booleanium::{
    aiger, aiger::Unroller, alternation, incdet::Options, incremental::IncrementalSolver,
    SolverResult,
};
use std::fmt::Write as _;
use std::time::Instant;

/// Builds ASCII AIGER safety specifications programmatically: inputs and
/// latch count are fixed up front (AIGER numbers inputs, then latches,
/// then gates), gates are allocated on demand with constant folding, and
/// latch next-state functions are connected once their gates exist.
struct Aig {
    /// input symbol names (the `controllable_` prefix marks existentials)
    input_names: Vec<String>,
    /// `(next, reset)` per latch, connected after gate construction
    nexts: Vec<Option<(u64, u64)>>,
    ands: Vec<(u64, u64, u64)>,
    next_var: u64,
    outputs: Vec<u64>,
}

impl Aig {
    fn new(input_names: Vec<String>, latches: usize) -> Self {
        let next_var = input_names.len() as u64 + latches as u64 + 1;
        Self {
            input_names,
            nexts: vec![None; latches],
            ands: Vec::new(),
            next_var,
            outputs: Vec::new(),
        }
    }

    fn input(&self, i: usize) -> u64 {
        assert!(i < self.input_names.len());
        2 * (i as u64 + 1)
    }

    fn latch(&self, i: usize) -> u64 {
        assert!(i < self.nexts.len());
        2 * (self.input_names.len() as u64 + i as u64 + 1)
    }

    fn and(&mut self, a: u64, b: u64) -> u64 {
        if a == 0 || b == 0 {
            return 0;
        }
        if a == 1 {
            return b;
        }
        if b == 1 || a == b {
            return a;
        }
        let lhs = 2 * self.next_var;
        self.next_var += 1;
        self.ands.push((lhs, a, b));
        lhs
    }

    fn or(&mut self, a: u64, b: u64) -> u64 {
        self.and(a ^ 1, b ^ 1) ^ 1
    }

    fn or_all(&mut self, lits: &[u64]) -> u64 {
        lits.iter().fold(0, |acc, &l| self.or(acc, l))
    }

    fn and_all(&mut self, lits: &[u64]) -> u64 {
        lits.iter().fold(1, |acc, &l| self.and(acc, l))
    }

    fn xor(&mut self, a: u64, b: u64) -> u64 {
        let left = self.and(a, b ^ 1);
        let right = self.and(a ^ 1, b);
        self.or(left, right)
    }

    fn ite(&mut self, cond: u64, then: u64, otherwise: u64) -> u64 {
        let taken = self.and(cond, then);
        let skipped = self.and(cond ^ 1, otherwise);
        self.or(taken, skipped)
    }

    fn connect(&mut self, latch: usize, next: u64, reset: u64) {
        assert!(self.nexts[latch].is_none());
        self.nexts[latch] = Some((next, reset));
    }

    fn output(&mut self, lit: u64) {
        self.outputs.push(lit);
    }

    fn text(&self) -> String {
        let mut s = String::new();
        let max_var = self.next_var - 1;
        writeln!(
            s,
            "aag {max_var} {} {} {} {}",
            self.input_names.len(),
            self.nexts.len(),
            self.outputs.len(),
            self.ands.len()
        )
        .unwrap();
        for i in 0..self.input_names.len() {
            writeln!(s, "{}", self.input(i)).unwrap();
        }
        for (i, next) in self.nexts.iter().enumerate() {
            let (next, reset) = next.expect("latch connected");
            writeln!(s, "{} {next} {reset}", self.latch(i)).unwrap();
        }
        for &out in &self.outputs {
            writeln!(s, "{out}").unwrap();
        }
        for &(lhs, rhs0, rhs1) in &self.ands {
            writeln!(s, "{lhs} {rhs0} {rhs1}").unwrap();
        }
        for (i, name) in self.input_names.iter().enumerate() {
            writeln!(s, "i{i} {name}").unwrap();
        }
        s
    }
}

/// A bounded-response arbiter: `n` clients raise requests (universal),
/// the controller issues grants (controllable). An error fires when two
/// grants coincide or a request stays pending for `b` consecutive steps.
/// Realizable (at every depth) iff `n <= b` — round-robin serves every
/// client within `n - 1` steps of waiting.
fn arbiter(n: usize, b: usize) -> String {
    let mut names: Vec<String> = (0..n).map(|i| format!("r{i}")).collect();
    names.extend((0..n).map(|i| format!("controllable_g{i}")));
    let mut aig = Aig::new(names, n * b);
    let age = |i: usize, j: usize| i * b + j;
    let mut errors = Vec::new();
    for i in 0..n {
        let (r, g) = (aig.input(i), aig.input(n + i));
        // the age chain: waited j+1 consecutive steps without a grant
        for j in 0..b {
            let source = if j == 0 { r } else { aig.latch(age(i, j - 1)) };
            let next = aig.and(source, g ^ 1);
            aig.connect(age(i, j), next, 0);
        }
        errors.push(aig.latch(age(i, b - 1)));
    }
    for i in 0..n {
        for j in (i + 1)..n {
            let (gi, gj) = (aig.input(n + i), aig.input(n + j));
            let double = aig.and(gi, gj);
            errors.push(double);
        }
    }
    let error = aig.or_all(&errors);
    aig.output(error);
    aig.text()
}

/// The same arbiter, with each client's age held as a **binary
/// counter** instead of a unary shift register: the state encoding a
/// bit-vector frontend would produce, at `ceil(log2(b+1))` latches per
/// client instead of `b`.
///
/// It is the same game. The unary chain
/// (`a[0]' = r & !g`, `a[j]' = a[j-1] & !g`, error on `a[b-1]`) is a
/// saturating counter that starts on a request, advances while no grant
/// arrives, and clears on one — so the binary form is
/// `c' = g ? 0 : (c > 0 | r) ? min(c+1, b) : 0`, with the error on
/// `c == b`. Realizable iff `n <= b`, exactly as before.
///
/// The pair is the measurement RQ4 wants: one problem, two state
/// encodings, and the question of whether the refinement loop's cost
/// follows the *problem* or the *representation*.
fn binary_arbiter(n: usize, b: usize) -> String {
    let width = (usize::BITS - b.leading_zeros()) as usize;
    let mut names: Vec<String> = (0..n).map(|i| format!("r{i}")).collect();
    names.extend((0..n).map(|i| format!("controllable_g{i}")));
    let mut aig = Aig::new(names, n * width);
    let bit = |i: usize, j: usize| i * width + j;
    let mut errors = Vec::new();
    for i in 0..n {
        let (r, g) = (aig.input(i), aig.input(n + i));
        let counter: Vec<u64> = (0..width).map(|j| aig.latch(bit(i, j))).collect();

        // the counter runs when a grant is withheld and something is
        // pending: either a fresh request or a count already started
        let started = aig.or_all(&counter);
        let pending = aig.or(started, r);
        let running = aig.and(pending, g ^ 1);

        // c == b, which is the error and also the value the counter
        // freezes at (the error output is already latched high, so what
        // happens afterwards cannot matter — freezing just keeps the
        // state space honest)
        let at_max: Vec<u64> = counter
            .iter()
            .enumerate()
            .map(|(j, &c)| if b >> j & 1 == 1 { c } else { c ^ 1 })
            .collect();
        let at_max = aig.and_all(&at_max);
        errors.push(at_max);

        // ripple-carry increment
        let mut carry = 1u64;
        let mut incremented = Vec::with_capacity(width);
        for &c in &counter {
            incremented.push(aig.xor(c, carry));
            carry = aig.and(c, carry);
        }

        for (j, (&c, &sum)) in counter.iter().zip(&incremented).enumerate() {
            let advanced = aig.ite(at_max, c, sum);
            let next = aig.and(running, advanced);
            aig.connect(bit(i, j), next, 0);
        }
    }
    for i in 0..n {
        for j in (i + 1)..n {
            let (gi, gj) = (aig.input(n + i), aig.input(n + j));
            let double = aig.and(gi, gj);
            errors.push(double);
        }
    }
    let error = aig.or_all(&errors);
    aig.output(error);
    aig.text()
}

/// A pursuit game on `m` cells, one-hot encoded: the robot (controllable
/// direction `e`) must move every step, the obstacle follows its
/// universal direction `d` — with `may_stay`, a second universal input
/// lets it stand still. An error fires when both occupy the same cell.
/// On a `ring` both wrap around; on a corridor a move off the end stays
/// in place. A ring without staying is safe forever (mirroring
/// preserves the distance). A corridor with a staying obstacle is a
/// classic cop-win pursuit — but only for a *reactive* cop: the ∀∃
/// unrolling fixes the obstacle sequence in advance, and the
/// clairvoyant robot times swaps past it, so even those instances stay
/// satisfiable (see `RESEARCH.md`).
fn pursuit(m: usize, ring: bool, may_stay: bool) -> String {
    let mut names = vec!["d".to_string()];
    if may_stay {
        names.push("s".to_string());
    }
    names.push("controllable_e".to_string());
    let robot_dir = names.len() - 1;
    let mut aig = Aig::new(names, 2 * m);
    let (robot, obstacle) = (|c: usize| c, |c: usize| m + c);
    // moves: direction true is +1, false is -1; entering cell c
    let entering = |aig: &mut Aig, at: &dyn Fn(usize) -> usize, dir: u64, c: usize| -> u64 {
        let mut terms = Vec::new();
        if ring || c > 0 {
            let from = at((c + m - 1) % m);
            let lit = aig.latch(from);
            terms.push(aig.and(dir, lit));
        }
        if ring || c + 1 < m {
            let from = at((c + 1) % m);
            let lit = aig.latch(from);
            terms.push(aig.and(dir ^ 1, lit));
        }
        // a corridor clamps moves off the end to staying in place
        if !ring && c == 0 {
            let lit = aig.latch(at(0));
            terms.push(aig.and(dir ^ 1, lit));
        }
        if !ring && c + 1 == m {
            let lit = aig.latch(at(m - 1));
            terms.push(aig.and(dir, lit));
        }
        aig.or_all(&terms)
    };
    let e = aig.input(robot_dir);
    let d = aig.input(0);
    for c in 0..m {
        let next = entering(&mut aig, &robot, e, c);
        let reset = u64::from(c == 0);
        aig.connect(robot(c), next, reset);
    }
    for c in 0..m {
        let moved = entering(&mut aig, &obstacle, d, c);
        let next = if may_stay {
            let s = aig.input(1);
            let here = aig.latch(obstacle(c));
            let stay = aig.and(s, here);
            let go = aig.and(s ^ 1, moved);
            aig.or(stay, go)
        } else {
            moved
        };
        let reset = u64::from(c == m / 2);
        aig.connect(obstacle(c), next, reset);
    }
    let mut collisions = Vec::new();
    for c in 0..m {
        let (r, o) = (aig.latch(robot(c)), aig.latch(obstacle(c)));
        let hit = aig.and(r, o);
        collisions.push(hit);
    }
    let error = aig.or_all(&collisions);
    aig.output(error);
    aig.text()
}

/// Unrolls a spec to `depth`, solving after every step, and returns the
/// final verdict.
fn unroll(solver: &mut IncrementalSolver, text: &str, depth: u32) -> SolverResult {
    let mut unroller = Unroller::new(text).expect("generated spec parses");
    let mut result = SolverResult::Unknown;
    for _ in 0..depth {
        unroller.step(solver);
        result = solver.solve();
    }
    result
}

/// The unrolling with a probe after every step: "can the controller pick
/// the raw move `probe` of the newest step and still stay safe?" — the
/// assumption-query pattern of a synthesis loop exploring candidate
/// moves.
fn unroll_probed(
    solver: &mut IncrementalSolver,
    text: &str,
    depth: u32,
    probe: usize,
) -> SolverResult {
    let mut unroller = Unroller::new(text).expect("generated spec parses");
    let mut result = SolverResult::Unknown;
    for _ in 0..depth {
        unroller.step(solver);
        result = solver.solve();
        let var = i32::try_from(unroller.current_inputs()[probe]).unwrap();
        solver.solve_with_assumptions(&[var]);
    }
    result
}

fn run(
    name: &str,
    expected: SolverResult,
    workload: impl Fn(&mut IncrementalSolver) -> SolverResult,
) {
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
        assert_eq!(result, expected, "{name}");
        let result = match result {
            SolverResult::Satisfiable => "sat",
            SolverResult::Unsatisfiable => "unsat",
            SolverResult::Unknown => "unknown",
        };
        let mode = if continuation { "in-place" } else { "rebuild" };
        println!(
            "{name:<32} {mode:>8} {result:>7} {elapsed:>12.3?} (extensions: {})",
            solver.extension_total()
        );
    }
}

fn main() {
    tracing_subscriber::fmt::init();
    let total = Instant::now();
    let (sat, unsat) = (SolverResult::Satisfiable, SolverResult::Unsatisfiable);
    // the depths keep every instance inside the tractable range mapped
    // out by per-depth probing (the arbiter beyond 2 clients and the
    // rings beyond depth ~13 blow up combinatorially)
    for (n, b, depth, expected) in [(2, 2, 16, sat), (3, 2, 16, unsat)] {
        let text = arbiter(n, b);
        run(&format!("arbiter-{n}-{b}-depth-{depth}"), expected, |solver| {
            unroll(solver, &text, depth)
        });
    }
    {
        let (n, b, depth) = (2, 2, 12);
        let text = arbiter(n, b);
        // probe after every step: grant client 0 in the newest step
        run(&format!("arbiter-{n}-{b}-probed-{depth}"), sat, |solver| {
            unroll_probed(solver, &text, depth, n)
        });
    }
    for (m, depth) in [(6, 24), (8, 12), (4, 12)] {
        let text = pursuit(m, true, false);
        run(&format!("ring-{m}-depth-{depth}"), sat, |solver| unroll(solver, &text, depth));
    }
    {
        // the corridor pursuit stays satisfiable even though the real
        // game is cop-win: the obstacle sequence is fixed in advance
        // (universal), so the clairvoyant robot times swaps past it
        let (m, depth) = (4, 12);
        let text = pursuit(m, false, true);
        run(&format!("corridor-{m}-depth-{depth}"), sat, |solver| unroll(solver, &text, depth));
    }
    // causality report: is the found bounded strategy also a winning
    // strategy of the *real* game (reads no future inputs)?
    for (name, text, depth) in [
        ("ring-6-depth-8", pursuit(6, true, false), 8),
        ("corridor-4-depth-8", pursuit(4, false, true), 8),
    ] {
        if let Some(filter) = std::env::args().nth(1) {
            if !name.contains(&filter) {
                continue;
            }
        }
        let mut solver = IncrementalSolver::new(Options::default());
        let mut unroller = Unroller::new(&text).expect("generated spec parses");
        for _ in 0..depth {
            unroller.step(&mut solver);
            assert_eq!(solver.solve(), SolverResult::Satisfiable);
        }
        let strategy = solver.skolem_model().expect("satisfiable").to_aiger(&|_| None);
        let causal = unroller.strategy_is_causal(&strategy).expect("strategy parses");
        println!("{name:<24} strategy causal: {causal}");
    }

    // Depth scaling of the *reactive* encoding: one quantifier
    // alternation per step, so the prefix grows with the depth instead
    // of staying at two blocks. This is the project's only source of
    // deep prefixes with independently known verdicts — the CADET suite
    // tops out at seven blocks and every corpus in reach is 2QBF or
    // 3QBF — so it is what the remaining alternation work has to be
    // judged on.
    println!();
    // per-family depth caps; the solve stays cheap well past these,
    // what stops the run first is the size of the composed strategy
    /// Circuit gates above which the benchmark reports the size and
    /// skips the SAT check.
    const VERIFY_LIMIT: usize = 100_000;
    for (name, text, max_depth) in [
        ("scale-arbiter-2-2", arbiter(2, 2), 12),
        ("scale-arbiter-3-2", arbiter(3, 2), 16),
        ("scale-ring-4", pursuit(4, true, false), 16),
        ("scale-corridor-4-stay", pursuit(4, false, true), 10),
    ] {
        if let Some(filter) = std::env::args().nth(1) {
            if !name.contains(&filter) {
                continue;
            }
        }
        let unroller = Unroller::new(&text).expect("generated spec parses");
        for depth in 1..=max_depth {
            let qcnf = unroller.alternating(depth);
            // `BENCH_DUMP=<dir>` writes the family out as QDIMACS, so
            // the deep-prefix instances can be reproduced, profiled, or
            // handed to another solver
            if let Ok(dir) = std::env::var("BENCH_DUMP") {
                let path = std::path::Path::new(&dir).join(format!("{name}-{depth:02}.qdimacs"));
                std::fs::write(path, format!("{qcnf}")).expect("dump directory is writable");
            }
            let blocks = qcnf.prefix.iter().filter(|(_, vars)| !vars.is_empty()).count();
            let start = Instant::now();
            let (result, strategy) = alternation::solve_certified(
                &qcnf,
                Options::default(),
                alternation::EXPANSION_BUDGET,
            );
            let elapsed = start.elapsed();
            // Verification is reported separately because on deep
            // prefixes it, not the solve, is the bottleneck. Both sizes
            // are reported because they diverge: the strategy is a
            // shared DAG and grows slowly, while the circuit a
            // monolithic build makes of it grows exponentially, and it
            // is the circuit the check has to pay for. The budget is
            // therefore on gates, and the build that measures them is
            // cheap next to the check itself.
            let size = strategy.as_ref().map_or(0, |s| s.size());
            let universals: Vec<_> = qcnf
                .prefix
                .iter()
                .filter(|(q, _)| *q == booleanium::QuantTy::Forall)
                .flat_map(|(_, vars)| vars.iter().copied())
                .collect();
            let gates = strategy.as_ref().map_or(0, |s| s.gates(&universals));
            let certified = match &strategy {
                Some(_) if gates > VERIFY_LIMIT => {
                    format!("{size} nodes, {gates} gates, unverified")
                }
                Some(strategy) => {
                    let start = Instant::now();
                    let ok = alternation::verify_strategy(&qcnf, strategy);
                    let verdict = if ok { "certified" } else { "INVALID" };
                    format!("{size} nodes, {gates} gates, {verdict} in {:.3?}", start.elapsed())
                }
                None => String::new(),
            };
            let verdict = match result {
                SolverResult::Satisfiable => "sat",
                SolverResult::Unsatisfiable => "unsat",
                SolverResult::Unknown => "unknown",
            };
            println!(
                "{name:<16} depth {depth:>2} {blocks:>3} blocks {:>6} vars {:>7} clauses                  {verdict:>7} {elapsed:>12.3?} {certified}",
                qcnf.prefix.iter().map(|(_, vars)| vars.len()).sum::<usize>(),
                qcnf.matrix.len(),
            );
            if elapsed.as_secs_f64() > 20.0 || result == SolverResult::Unknown {
                break;
            }
        }
    }

    // The winning-region refinement: instead of unrolling the game to a
    // depth, shrink `W` by counterexample until `W = CPre(W)`. The query
    // stays ∀∃ whatever the game's depth, every refinement is an
    // addition, and the answer is *unbounded* realizability rather than
    // a bounded approximation — the access pattern the incremental
    // interface was built for.
    println!();
    for (name, text) in [
        ("game-arbiter-2-2", arbiter(2, 2)),
        ("game-arbiter-3-2", arbiter(3, 2)),
        ("game-ring-4", pursuit(4, true, false)),
        ("game-corridor-4-stay", pursuit(4, false, true)),
        // larger circuits at similar round counts: what a rebuild costs
        // grows with the circuit, what the search costs grows with the
        // region, so these separate the two
        ("game-arbiter-3-3", arbiter(3, 3)),
        ("game-arbiter-4-4", arbiter(4, 4)),
        ("game-ring-6", pursuit(6, true, false)),
    ] {
        if let Some(filter) = std::env::args().nth(1) {
            if !name.contains(&filter) {
                continue;
            }
        }
        // `BENCH_DUMP=<dir>` writes the game spec out as ASCII AIGER,
        // so a family can be reproduced, profiled, or checked against
        // another tool
        if let Ok(dir) = std::env::var("BENCH_DUMP") {
            let path = std::path::Path::new(&dir).join(format!("{name}.aag"));
            std::fs::write(path, &text).expect("dump directory is writable");
        }
        for continuation in [true, false] {
            let start = Instant::now();
            // core options are A/B-able from the environment: the
            // refinement loop drives the core very differently from the
            // 2QBF corpora the defaults were fitted on, so which
            // extensions pay here is a question the benchmark should be
            // able to answer without a rebuild
            let mut options = Options::default();
            if std::env::var("BENCH_RESTARTS").is_ok() {
                options.restarts = true;
            }
            if std::env::var("BENCH_NO_CASE_SPLITS").is_ok() {
                options.case_splits = false;
            }
            if std::env::var("BENCH_NO_CEGAR").is_ok() {
                options.cegar = false;
            }
            let outcome = aiger::solve_safety_with_continuation(
                &text,
                options,
                continuation,
            )
            .expect("generated spec parses");
            let elapsed = start.elapsed();
            let mode = if continuation { "in-place" } else { "rebuild" };
            println!(
                "{name:<22} {mode:>8} {:>14} {:>3} rounds ({:>3} safe, {:>3} fallback) \
                 {:>4} cubes {:>4} extensions {elapsed:>12.3?}",
                if outcome.realizable { "realizable" } else { "unrealizable" },
                outcome.rounds,
                outcome.safe_rounds,
                outcome.fallback_rounds,
                outcome.losing.len(),
                outcome.extensions,
            );
        }
    }

    // The state-encoding comparison (RQ4/RQ5): the same arbiter game
    // with each client's age as a unary shift register and as a binary
    // counter — the encoding a bit-vector frontend would produce. The
    // question is whether the refinement loop's cost follows the
    // *problem* or the *representation*, and the honest way to ask it
    // is to price the region three ways: the cubes the loop actually
    // discovered, a near-minimal cube cover of the true losing region
    // (how many cubes the region *needs*), and what a word-level
    // description would be.
    println!();
    println!(
        "{:<24} {:>7} {:>13} {:>7} {:>7} {:>7} {:>7} {:>12}",
        "family", "latches", "verdict", "rounds", "cubes", "ideal", "width", "time"
    );
    // (k, b) pairs: k = b sits on the realizability boundary, and
    // holding k at 2 while b grows is the axis a word-level region
    // should win on — the unary state space grows with the deadline,
    // the binary one with its logarithm
    for (name, text) in [
        ("region-arbiter-2-2 unary", arbiter(2, 2)),
        ("region-arbiter-2-2 binary", binary_arbiter(2, 2)),
        ("region-arbiter-2-4 unary", arbiter(2, 4)),
        ("region-arbiter-2-4 binary", binary_arbiter(2, 4)),
        ("region-arbiter-2-6 unary", arbiter(2, 6)),
        ("region-arbiter-2-6 binary", binary_arbiter(2, 6)),
        ("region-arbiter-2-8 unary", arbiter(2, 8)),
        ("region-arbiter-2-8 binary", binary_arbiter(2, 8)),
        ("region-arbiter-2-12 unary", arbiter(2, 12)),
        ("region-arbiter-2-12 binary", binary_arbiter(2, 12)),
        ("region-arbiter-2-16 unary", arbiter(2, 16)),
        ("region-arbiter-2-16 binary", binary_arbiter(2, 16)),
        ("region-arbiter-3-3 unary", arbiter(3, 3)),
        ("region-arbiter-3-3 binary", binary_arbiter(3, 3)),
        ("region-arbiter-4-4 unary", arbiter(4, 4)),
        ("region-arbiter-4-4 binary", binary_arbiter(4, 4)),
        ("region-ring-4", pursuit(4, true, false)),
        ("region-ring-6", pursuit(6, true, false)),
        ("region-corridor-4-stay", pursuit(4, false, true)),
    ] {
        if let Some(filter) = std::env::args().nth(1) {
            if !name.contains(&filter) {
                continue;
            }
        }
        let latches = text
            .lines()
            .next()
            .and_then(|h| h.split_ascii_whitespace().nth(3))
            .and_then(|f| f.parse::<usize>().ok())
            .expect("header parses");
        #[cfg(feature = "probe")]
        booleanium::probe::reset();
        let mut options = Options::default();
        if std::env::var("BENCH_CONFLICT_HINTS").is_ok() {
            options.conflict_hints = true;
        }
        let start = Instant::now();
        let outcome = aiger::solve_safety(&text, options).expect("generated spec parses");
        let elapsed = start.elapsed();
        let width = if outcome.losing.is_empty() {
            0.0
        } else {
            outcome.losing.iter().map(Vec::len).sum::<usize>() as f64
                / outcome.losing.len() as f64
        };
        let ideal = minimal_cover(&text, latches).map_or("-".to_string(), |c| c.to_string());
        println!(
            "{name:<24} {latches:>7} {:>13} {:>7} {:>7} {ideal:>7} {width:>7.1} {elapsed:>12.3?}",
            if outcome.realizable { "realizable" } else { "unrealizable" },
            outcome.rounds,
            outcome.losing.len(),
        );
        #[cfg(feature = "probe")]
        for report in [
            booleanium::probe::wave_report(),
            booleanium::probe::cone_report(),
            booleanium::probe::hint_report(),
        ]
        .into_iter()
        .flatten()
        {
            println!("    {report}");
        }
    }
    // The control (RQ5): the same fixpoint driven by two competing SAT
    // solvers, which is what a developer writes when they do not want
    // to depend on a quantified solver. Same games, same oracle, no
    // shared code — the number that says whether the quantified path is
    // buying anything.
    println!();
    println!(
        "{:<26} {:>7} {:>13} {:>16} {:>12} {:>16} {:>12}",
        "family", "latches", "verdict", "booleanium", "time", "two solvers", "time"
    );
    for (name, text) in [
        ("control-arbiter-2-2", arbiter(2, 2)),
        ("control-arbiter-3-2", arbiter(3, 2)),
        ("control-arbiter-3-3", arbiter(3, 3)),
        ("control-arbiter-2-8", arbiter(2, 8)),
        ("control-ring-4", pursuit(4, true, false)),
        ("control-corridor-4-stay", pursuit(4, false, true)),
        ("control-arbiter-4-4", arbiter(4, 4)),
        ("control-ring-6", pursuit(6, true, false)),
    ] {
        if let Some(filter) = std::env::args().nth(1) {
            if !name.contains(&filter) {
                continue;
            }
        }
        let latches = text
            .lines()
            .next()
            .and_then(|h| h.split_ascii_whitespace().nth(3))
            .and_then(|f| f.parse::<usize>().ok())
            .expect("header parses");
        let start = Instant::now();
        let ours = aiger::solve_safety(&text, Options::default()).expect("spec parses");
        let ours_time = start.elapsed();
        let start = Instant::now();
        let theirs = two_solver_fixpoint(&text);
        let theirs_time = start.elapsed();
        assert_eq!(
            ours.realizable, theirs.realizable,
            "the control disagrees with the solver on {name}"
        );
        println!(
            "{name:<26} {latches:>7} {:>13} {:>16} {ours_time:>12.3?} {:>16} {theirs_time:>12.3?}",
            if ours.realizable { "realizable" } else { "unrealizable" },
            format!("{} r / {} c", ours.rounds, ours.losing.len()),
            format!("{} r / {} c / {} i", theirs.rounds, theirs.cubes, theirs.refinements),
        );
    }
    println!("total: {:.3?}", total.elapsed());
}

/// The size of a near-minimal cube cover of the true losing region,
/// computed without the solver: an explicit backward fixpoint over the
/// state space, then greedy prime-implicant expansion and greedy set
/// cover. This is the number the refinement loop's cube count should be
/// compared against — not to the loop's own previous run.
///
/// Returns `None` when the state space is too large to sweep.
fn minimal_cover(text: &str, latches: usize) -> Option<usize> {
    if latches > 20 {
        return None;
    }
    let losing = aiger::losing_states(text, latches).ok()?;
    let states = 1usize << latches;
    let targets: Vec<usize> = (0..states).filter(|&s| losing[s]).collect();
    if targets.is_empty() {
        return Some(0);
    }

    // every losing state expands to a maximal cube that stays losing;
    // literals are dropped in a fixed order, so the result is a prime
    // implicant of the losing set
    let mut primes: Vec<(usize, usize)> = Vec::new(); // (mask of fixed bits, values)
    for &state in &targets {
        let mut mask = (1usize << latches) - 1;
        for bit in 0..latches {
            let candidate = mask & !(1 << bit);
            let inside = (0..states).all(|s| {
                s & candidate != state & candidate || losing[s]
            });
            if inside {
                mask = candidate;
            }
        }
        primes.push((mask, state & mask));
    }
    primes.sort_unstable();
    primes.dedup();

    // greedy set cover over the prime implicants
    let mut uncovered: Vec<bool> = losing;
    let mut chosen = 0;
    while uncovered.iter().any(|&u| u) {
        let best = primes
            .iter()
            .max_by_key(|&&(mask, values)| {
                (0..states).filter(|&s| s & mask == values && uncovered[s]).count()
            })
            .copied()?;
        let gain = (0..states).filter(|&s| s & best.0 == best.1 && uncovered[s]).count();
        if gain == 0 {
            return None;
        }
        for (s, covered) in uncovered.iter_mut().enumerate() {
            if s & best.0 == best.1 {
                *covered = false;
            }
        }
        chosen += 1;
    }
    Some(chosen)
}

// ---------------------------------------------------------------------
// The control for RQ5: the same winning-region fixpoint, driven by two
// competing SAT solvers instead of by a quantified solver.
//
// This is what a practitioner writes when they want a safety game
// solved and do not want to depend on a QBF solver: CEGAR over the
// round's ∀∃ query, with one solver proposing a state and an
// uncontrollable move and a second checking whether a controllable
// answer exists. It shares nothing with `booleanium` — its own AIGER
// parser, its own CNF encoding, varisat used directly — because a
// control that reuses the machinery under test is not a control.
// ---------------------------------------------------------------------

use varisat::ExtendFormula;

struct Spec {
    /// input literals, with the controllable ones flagged
    inputs: Vec<u64>,
    controllable: Vec<bool>,
    /// `(literal, next, reset)` per latch
    latches: Vec<(u64, u64, u64)>,
    outputs: Vec<u64>,
    ands: Vec<(u64, u64, u64)>,
}

fn parse_spec(text: &str) -> Spec {
    let mut lines = text.lines();
    let header: Vec<u64> = lines
        .next()
        .expect("header")
        .split_ascii_whitespace()
        .skip(1)
        .map(|f| f.parse().expect("header field"))
        .collect();
    let (num_inputs, num_latches, num_outputs, num_ands) =
        (header[1] as usize, header[2] as usize, header[3] as usize, header[4] as usize);
    let mut take = |n: usize| -> Vec<Vec<u64>> {
        (0..n)
            .map(|_| {
                lines
                    .next()
                    .expect("line")
                    .split_ascii_whitespace()
                    .map(|f| f.parse().expect("literal"))
                    .collect()
            })
            .collect()
    };
    let inputs: Vec<u64> = take(num_inputs).into_iter().map(|l| l[0]).collect();
    let latches: Vec<(u64, u64, u64)> = take(num_latches)
        .into_iter()
        .map(|l| (l[0], l[1], l.get(2).copied().unwrap_or(0)))
        .collect();
    let outputs: Vec<u64> = take(num_outputs).into_iter().map(|l| l[0]).collect();
    let ands: Vec<(u64, u64, u64)> =
        take(num_ands).into_iter().map(|l| (l[0], l[1], l[2])).collect();

    let mut controllable = vec![false; inputs.len()];
    for line in lines {
        if let Some(rest) = line.strip_prefix('i') {
            if let Some((pos, name)) = rest.split_once(' ') {
                if let Ok(pos) = pos.parse::<usize>() {
                    if pos < controllable.len() {
                        controllable[pos] =
                            name.starts_with("controllable_") || name.starts_with("2 ");
                    }
                }
            }
        }
    }
    Spec { inputs, controllable, latches, outputs, ands }
}

/// Encodes one copy of the combinational circuit. `input_lit` supplies a
/// literal per input — a shared variable for the free ones, a constant
/// for the ones this copy fixes — and `state` the current-state
/// literals. Returns the error literal and the next-state literals.
fn encode_copy(
    spec: &Spec,
    solver: &mut varisat::Solver<'static>,
    one: varisat::Lit,
    state: &[varisat::Lit],
    input_lit: &[varisat::Lit],
) -> (varisat::Lit, Vec<varisat::Lit>) {
    let mut wire: std::collections::HashMap<u64, varisat::Lit> = std::collections::HashMap::new();
    for (position, &lit) in spec.inputs.iter().enumerate() {
        wire.insert(lit / 2, input_lit[position]);
    }
    for (idx, &(lit, _, _)) in spec.latches.iter().enumerate() {
        wire.insert(lit / 2, state[idx]);
    }
    let value = |l: u64, wire: &std::collections::HashMap<u64, varisat::Lit>| match l {
        0 => !one,
        1 => one,
        _ => {
            let base = wire[&(l / 2)];
            if l & 1 == 1 {
                !base
            } else {
                base
            }
        }
    };
    for &(lhs, rhs0, rhs1) in &spec.ands {
        let gate = solver.new_lit();
        let (a, b) = (value(rhs0, &wire), value(rhs1, &wire));
        solver.add_clause(&[!gate, a]);
        solver.add_clause(&[!gate, b]);
        solver.add_clause(&[gate, !a, !b]);
        wire.insert(lhs / 2, gate);
    }
    // the error is the disjunction of the outputs
    let error = solver.new_lit();
    let mut forward = vec![!error];
    for &out in &spec.outputs {
        let lit = value(out, &wire);
        solver.add_clause(&[error, !lit]);
        forward.push(lit);
    }
    solver.add_clause(&forward);
    let next = spec.latches.iter().map(|&(_, n, _)| value(n, &wire)).collect();
    (error, next)
}

struct ControlOutcome {
    realizable: bool,
    rounds: u32,
    cubes: usize,
    refinements: u32,
}

/// `νW. CPre(W)` by CEGAR over two SAT solvers.
fn two_solver_fixpoint(text: &str) -> ControlOutcome {
    let spec = parse_spec(text);
    let latches = spec.latches.len();
    let uncontrollable: Vec<usize> =
        (0..spec.inputs.len()).filter(|&i| !spec.controllable[i]).collect();
    let controllable: Vec<usize> =
        (0..spec.inputs.len()).filter(|&i| spec.controllable[i]).collect();

    // the responder: "given this state and uncontrollable move, can the
    // controller avoid the error and stay in the region?" One solver for
    // the whole run — the region only ever shrinks, which only ever adds
    // clauses
    let mut responder = varisat::Solver::new();
    let one = responder.new_lit();
    responder.add_clause(&[one]);
    let state: Vec<varisat::Lit> = (0..latches).map(|_| responder.new_lit()).collect();
    let inputs: Vec<varisat::Lit> =
        (0..spec.inputs.len()).map(|_| responder.new_lit()).collect();
    let (error, next) = encode_copy(&spec, &mut responder, one, &state, &inputs);
    responder.add_clause(&[!error]);

    let mut cubes: Vec<Vec<(usize, bool)>> = Vec::new();
    let mut responses: Vec<Vec<bool>> = Vec::new();
    let mut rounds = 0;
    let mut refinements = 0;

    loop {
        // the candidate solver is rebuilt per round: its refinements
        // speak about the region, and the region just changed. The
        // responses themselves are kept and re-instantiated, so nothing
        // learnt about the game is thrown away.
        rounds += 1;
        let mut candidate = varisat::Solver::new();
        let c_one = candidate.new_lit();
        candidate.add_clause(&[c_one]);
        let c_state: Vec<varisat::Lit> = (0..latches).map(|_| candidate.new_lit()).collect();
        let c_inputs: Vec<varisat::Lit> =
            (0..spec.inputs.len()).map(|_| candidate.new_lit()).collect();
        // the proposed state must still be in the region
        for cube in &cubes {
            let clause: Vec<varisat::Lit> = cube
                .iter()
                .map(|&(idx, v)| if v { !c_state[idx] } else { c_state[idx] })
                .collect();
            candidate.add_clause(&clause);
        }
        for response in &responses {
            let mut lits = c_inputs.clone();
            for (bit, &position) in controllable.iter().enumerate() {
                lits[position] = if response[bit] { c_one } else { !c_one };
            }
            let (err, nxt) = encode_copy(&spec, &mut candidate, c_one, &c_state, &lits);
            // this response is answered only if it errors or leaves the
            // region: `err ∨ ⋁_k next ∈ cube_k`
            let mut clause = vec![err];
            for cube in &cubes {
                // `inside` *is* "the successor lands in this cube", in
                // both directions: the clause below uses it positively,
                // and a one-sided definition lets the solver set it
                // true for free, which excludes nothing
                let inside = candidate.new_lit();
                let mut reverse = vec![inside];
                for &(idx, v) in cube {
                    let lit = if v { nxt[idx] } else { !nxt[idx] };
                    candidate.add_clause(&[!inside, lit]);
                    reverse.push(!lit);
                }
                candidate.add_clause(&reverse);
                clause.push(inside);
            }
            candidate.add_clause(&clause);
        }

        let (found, model) = loop {
            if !candidate.solve().expect("plain SAT") {
                break (false, Vec::new());
            }
            // index by variable, not by position: varisat's model omits
            // variables it never had to assign, and reading those as
            // false silently asks the responder about a different
            // candidate than the one the solver found — which loops
            // forever, because the refinement then excludes nothing
            let valuation: std::collections::HashMap<usize, bool> =
                candidate.model().expect("model after sat")
                    .iter()
                    .map(|l| (l.var().index(), l.is_positive()))
                    .collect();
            let read = |l: varisat::Lit| {
                valuation.get(&l.var().index()).copied().unwrap_or(false) == l.is_positive()
            };

            // ask the responder about this candidate
            let mut assumptions: Vec<varisat::Lit> = Vec::new();
            for (idx, &l) in c_state.iter().enumerate() {
                assumptions.push(if read(l) { state[idx] } else { !state[idx] });
            }
            for &position in &uncontrollable {
                let l = c_inputs[position];
                assumptions
                    .push(if read(l) { inputs[position] } else { !inputs[position] });
            }
            responder.assume(&assumptions);
            if responder.solve().expect("plain SAT") {
                // the controller answers: refine and try again
                let valuation: std::collections::HashMap<usize, bool> =
                    responder.model().expect("model after sat")
                        .iter()
                        .map(|l| (l.var().index(), l.is_positive()))
                        .collect();
                let answer: Vec<bool> = controllable
                    .iter()
                    .map(|&p| {
                        let l = inputs[p];
                        valuation.get(&l.var().index()).copied().unwrap_or(false)
                            == l.is_positive()
                    })
                    .collect();
                let mut lits = c_inputs.clone();
                for (bit, &position) in controllable.iter().enumerate() {
                    lits[position] = if answer[bit] { c_one } else { !c_one };
                }
                let (err, nxt) = encode_copy(&spec, &mut candidate, c_one, &c_state, &lits);
                let mut clause = vec![err];
                for cube in &cubes {
                    let inside = candidate.new_lit();
                    let mut reverse = vec![inside];
                    for &(idx, v) in cube {
                        let lit = if v { nxt[idx] } else { !nxt[idx] };
                        candidate.add_clause(&[!inside, lit]);
                        reverse.push(!lit);
                    }
                    candidate.add_clause(&reverse);
                    clause.push(inside);
                }
                candidate.add_clause(&clause);
                responses.push(answer);
                refinements += 1;
                continue;
            }
            // no answer: a genuine losing state, generalised by the
            // responder's own unsatisfiable core
            let core: Vec<varisat::Lit> =
                responder.failed_core().expect("core after unsat").to_vec();
            let cube: Vec<(usize, bool)> = state
                .iter()
                .enumerate()
                .filter_map(|(idx, &s)| {
                    core.iter().find(|c| c.var() == s.var()).map(|c| (idx, c.is_positive()))
                })
                .collect();
            break (true, cube);
        };

        if !found {
            let initial: Vec<bool> = spec.latches.iter().map(|&(_, _, r)| r == 1).collect();
            let realizable = !cubes
                .iter()
                .any(|cube| cube.iter().all(|&(idx, v)| initial[idx] == v));
            return ControlOutcome { realizable, rounds, cubes: cubes.len(), refinements };
        }
        if model.is_empty() {
            // every state loses
            let realizable = false;
            cubes.push(Vec::new());
            return ControlOutcome { realizable, rounds, cubes: cubes.len(), refinements };
        }
        // the successor may no longer land in the new cube
        let clause: Vec<varisat::Lit> =
            model.iter().map(|&(idx, v)| if v { !next[idx] } else { next[idx] }).collect();
        responder.add_clause(&clause);
        cubes.push(model);
    }
}
