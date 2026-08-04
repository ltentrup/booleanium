//! The RQ1 paired-encoding experiment: the same circuit families
//! rendered as (a) a QCIR circuit consumed by the definition-level
//! frontend, (b) two-sided Tseitin CNF, and (c) one-sided
//! Plaisted–Greenbaum CNF, solved by the same core. Measures what the
//! input format is worth: how many variables the initial propagation
//! determinizes, and what that does to decisions, conflicts, and time.
//! Run with `cargo run --release --bin bench_encodings`.

use booleanium::{
    incdet::{IncDet, Options},
    qcir,
    qcnf::QCNF,
    QuantTy, SolverResult,
};
use std::fmt::Write as _;
use std::time::Instant;

/// A combinational 2QBF circuit: inputs are variables `1..=universals`
/// (∀) and `universals+1..=universals+existentials` (∃), gates are
/// numbered after the inputs in definition order, and the output
/// literal must hold. Literals are signed variable numbers.
struct Circuit {
    universals: usize,
    existentials: usize,
    gates: Vec<Gate>,
    output: i32,
}

enum Gate {
    And(Vec<i32>),
    Or(Vec<i32>),
    Xor(i32, i32),
}

impl Circuit {
    fn inputs(&self) -> usize {
        self.universals + self.existentials
    }

    fn gate_var(&self, index: usize) -> i32 {
        i32::try_from(self.inputs() + index + 1).expect("variable fits an i32")
    }

    /// The circuit as QCIR text (named identifiers keep the numbering).
    fn to_qcir(&self) -> String {
        let mut s = String::from("#QCIR-G14\n");
        let list = |from: usize, count: usize| {
            (from + 1..=from + count).map(|v| format!("v{v}")).collect::<Vec<_>>().join(", ")
        };
        if self.universals > 0 {
            let _ = writeln!(s, "forall({})", list(0, self.universals));
        }
        if self.existentials > 0 {
            let _ = writeln!(s, "exists({})", list(self.universals, self.existentials));
        }
        let lit = |l: i32| if l < 0 { format!("-v{}", -l) } else { format!("v{l}") };
        let _ = writeln!(s, "output({})", lit(self.output));
        for (idx, gate) in self.gates.iter().enumerate() {
            let name = lit(self.gate_var(idx));
            let (op, args): (&str, Vec<String>) = match gate {
                Gate::And(args) => ("and", args.iter().map(|&a| lit(a)).collect()),
                Gate::Or(args) => ("or", args.iter().map(|&a| lit(a)).collect()),
                Gate::Xor(a, b) => ("xor", vec![lit(*a), lit(*b)]),
            };
            let _ = writeln!(s, "{name} = {op}({})", args.join(", "));
        }
        s
    }

    /// The prefix shared by both CNF encodings: ∀ inputs, then the
    /// existential inputs and all gate variables.
    fn cnf_prefix(&self) -> (Vec<u32>, Vec<u32>) {
        let universals: Vec<u32> =
            (1..=self.universals).map(|v| u32::try_from(v).unwrap()).collect();
        let existentials: Vec<u32> = (self.universals + 1..=self.inputs() + self.gates.len())
            .map(|v| u32::try_from(v).unwrap())
            .collect();
        (universals, existentials)
    }

    /// Two-sided Tseitin CNF: every gate is fully defined.
    fn to_two_sided(&self) -> QCNF {
        let matrix = self.two_sided_matrix();
        self.build(&matrix)
    }

    /// The two-sided clauses, in DIMACS literals.
    fn two_sided_matrix(&self) -> Vec<Vec<i32>> {
        let mut matrix: Vec<Vec<i32>> = Vec::new();
        for (idx, gate) in self.gates.iter().enumerate() {
            let g = self.gate_var(idx);
            match gate {
                Gate::And(args) => {
                    let mut long = vec![g];
                    for &a in args {
                        matrix.push(vec![-g, a]);
                        long.push(-a);
                    }
                    matrix.push(long);
                }
                Gate::Or(args) => {
                    let mut long = vec![-g];
                    for &a in args {
                        matrix.push(vec![g, -a]);
                        long.push(a);
                    }
                    matrix.push(long);
                }
                Gate::Xor(a, b) => {
                    matrix.push(vec![-g, *a, *b]);
                    matrix.push(vec![-g, -a, -b]);
                    matrix.push(vec![g, -a, *b]);
                    matrix.push(vec![g, *a, -b]);
                }
            }
        }
        matrix.push(vec![self.output]);
        matrix
    }

    /// One-sided Plaisted–Greenbaum CNF: each gate keeps only the
    /// implication directions its polarities require, computed by
    /// polarity propagation from the output.
    fn to_plaisted_greenbaum(&self) -> QCNF {
        // polarity[gate] = (positive needed, negative needed)
        let mut polarity = vec![(false, false); self.gates.len()];
        let mut queue: Vec<i32> = vec![self.output];
        while let Some(l) = queue.pop() {
            let var = usize::try_from(l.abs()).unwrap();
            if var <= self.inputs() {
                continue;
            }
            let idx = var - self.inputs() - 1;
            let slot = &mut polarity[idx];
            let flag = if l > 0 { &mut slot.0 } else { &mut slot.1 };
            if *flag {
                continue;
            }
            *flag = true;
            match &self.gates[idx] {
                Gate::And(args) | Gate::Or(args) => {
                    for &a in args {
                        queue.push(if l > 0 { a } else { -a });
                    }
                }
                Gate::Xor(a, b) => {
                    // xor constrains both polarities of both arguments
                    queue.extend([*a, -*a, *b, -*b]);
                }
            }
        }
        let mut matrix: Vec<Vec<i32>> = Vec::new();
        for (idx, gate) in self.gates.iter().enumerate() {
            let g = self.gate_var(idx);
            let (pos, neg) = polarity[idx];
            match gate {
                Gate::And(args) => {
                    if pos {
                        for &a in args {
                            matrix.push(vec![-g, a]);
                        }
                    }
                    if neg {
                        let mut long = vec![g];
                        long.extend(args.iter().map(|&a| -a));
                        matrix.push(long);
                    }
                }
                Gate::Or(args) => {
                    if pos {
                        let mut long = vec![-g];
                        long.extend(args.iter().copied());
                        matrix.push(long);
                    }
                    if neg {
                        for &a in args {
                            matrix.push(vec![g, -a]);
                        }
                    }
                }
                Gate::Xor(a, b) => {
                    if pos {
                        matrix.push(vec![-g, *a, *b]);
                        matrix.push(vec![-g, -a, -b]);
                    }
                    if neg {
                        matrix.push(vec![g, -a, *b]);
                        matrix.push(vec![g, *a, -b]);
                    }
                }
            }
        }
        matrix.push(vec![self.output]);
        self.build(&matrix)
    }

    fn build(&self, matrix: &[Vec<i32>]) -> QCNF {
        let (universals, existentials) = self.cnf_prefix();
        let prefix: Vec<(QuantTy, &[u32])> = if universals.is_empty() {
            vec![(QuantTy::Exists, &existentials[..])]
        } else {
            vec![(QuantTy::Forall, &universals[..]), (QuantTy::Exists, &existentials[..])]
        };
        let matrix_refs: Vec<&[i32]> = matrix.iter().map(Vec::as_slice).collect();
        QCNF::new(&prefix, &matrix_refs)
    }
}

/// A builder over the fixed input variables.
struct Builder {
    circuit: Circuit,
}

impl Builder {
    fn new(universals: usize, existentials: usize) -> Self {
        Self { circuit: Circuit { universals, existentials, gates: Vec::new(), output: 0 } }
    }

    fn universal(&self, i: usize) -> i32 {
        i32::try_from(i + 1).expect("fits")
    }

    fn existential(&self, i: usize) -> i32 {
        i32::try_from(self.circuit.universals + i + 1).expect("fits")
    }

    fn push(&mut self, gate: Gate) -> i32 {
        self.circuit.gates.push(gate);
        self.circuit.gate_var(self.circuit.gates.len() - 1)
    }

    fn xor(&mut self, a: i32, b: i32) -> i32 {
        self.push(Gate::Xor(a, b))
    }

    fn and(&mut self, args: Vec<i32>) -> i32 {
        self.push(Gate::And(args))
    }

    fn or(&mut self, args: Vec<i32>) -> i32 {
        self.push(Gate::Or(args))
    }

    fn finish(mut self, output: i32) -> Circuit {
        self.circuit.output = output;
        self.circuit
    }
}

/// ∀ a, b (two `n`-bit words) ∃ y: `a + y = b` modulo `2^n` — a
/// *word-level* operation as an eager bit-blaster leaves it, a
/// ripple-carry chain of gate definitions. Satisfiable (`y = b - a`),
/// and `y` is determined by `a` and `b`, but only *implicitly*: the
/// gates define the sum bits from `a` and `y`, so determinizing `y`
/// means inverting the adder through its definitions rather than
/// reading them forwards. This is RQ3's question — whether bit-blasting
/// into definitions keeps enough structure — posed one level above RQ1.
fn adder_inverse(n: usize) -> Circuit {
    let mut bld = Builder::new(2 * n, n);
    let a = |i: usize| i;
    let b = |i: usize| n + i;
    let mut carry: Option<i32> = None;
    let mut equal = Vec::new();
    for i in 0..n {
        let (ai, yi) = (bld.universal(a(i)), bld.existential(i));
        let half = bld.xor(ai, yi);
        let sum = match carry {
            Some(c) => bld.xor(half, c),
            None => half,
        };
        // the carry out: two of the three inputs high
        carry = Some(match carry {
            Some(c) => {
                let ay = bld.and(vec![ai, yi]);
                let ac = bld.and(vec![ai, c]);
                let yc = bld.and(vec![yi, c]);
                bld.or(vec![ay, ac, yc])
            }
            None => bld.and(vec![ai, yi]),
        });
        let bi = bld.universal(b(i));
        equal.push(-bld.xor(sum, bi));
    }
    let ok = bld.and(equal);
    bld.finish(ok)
}

/// ∀ x (an `n`-bit word) ∃ y: `y <u x` or `x = 0` — an unsigned
/// comparison, the other shape a bit-blaster produces, under a
/// *disjunctive* top so nothing is forced from the output. Satisfiable,
/// but `y` is a genuine choice rather than a function of `x`, which is
/// where RQ1 found the encodings separating.
fn comparator_choice(n: usize) -> Circuit {
    let mut bld = Builder::new(n, n);
    // less-than by a borrow chain from the least significant bit
    let mut less: Option<i32> = None;
    for i in 0..n {
        let (xi, yi) = (bld.universal(i), bld.existential(i));
        let below = bld.and(vec![-yi, xi]);
        let equal_bit = -bld.xor(yi, xi);
        less = Some(match less {
            Some(previous) => {
                let carried = bld.and(vec![equal_bit, previous]);
                bld.or(vec![below, carried])
            }
            None => below,
        });
    }
    let zero = bld.and((0..n).map(|i| -bld.universal(i)).collect::<Vec<_>>());
    let ok = bld.or(vec![less.expect("n > 0"), zero]);
    bld.finish(ok)
}

/// ∀ x_1..x_n ∃ y_1..y_n: every y_i must equal the prefix parity
/// x_1 ⊕ … ⊕ x_i (satisfiable; the ↔ per output is exactly what a
/// one-sided encoding weakens).
fn parity_equalities(n: usize) -> Circuit {
    let mut b = Builder::new(n, n);
    let mut prefix = b.universal(0);
    let mut mismatches = Vec::new();
    for i in 0..n {
        if i > 0 {
            let x = b.universal(i);
            prefix = b.xor(prefix, x);
        }
        let y = b.existential(i);
        mismatches.push(-b.xor(y, prefix));
    }
    let ok = b.and(mismatches);
    b.finish(ok)
}

/// ∀ address bits and data leaves ∃ y: y must equal the multiplexer
/// output selecting the addressed leaf (satisfiable).
fn mux_tree(address_bits: usize) -> Circuit {
    let leaves = 1 << address_bits;
    let mut b = Builder::new(address_bits + leaves, 1);
    let mut layer: Vec<i32> = (0..leaves).map(|i| b.universal(address_bits + i)).collect();
    for bit in 0..address_bits {
        let a = b.universal(bit);
        layer = layer
            .chunks(2)
            .map(|pair| {
                let low = b.and(vec![-a, pair[0]]);
                let high = b.and(vec![a, pair[1]]);
                b.or(vec![low, high])
            })
            .collect();
    }
    let y = b.existential(0);
    let mismatch = b.xor(y, layer[0]);
    b.finish(-mismatch)
}

/// ∀ x_1..x_n ∃ y_1..y_n: either every y_i equals x_i or every y_i
/// equals ¬x_i (satisfiable — pick a side). The disjunctive top means
/// unit propagation from the output forces nothing, so the backward
/// implication directions that Plaisted–Greenbaum drops are exactly
/// what determinizes the comparison gates. Built from and/or only
/// (xor constrains both polarities and would mask the effect).
fn choice_of_relation(n: usize) -> Circuit {
    let mut b = Builder::new(n, n);
    let mut equal = Vec::new();
    let mut inverted = Vec::new();
    for i in 0..n {
        let (x, y) = (b.universal(i), b.existential(i));
        let both = b.and(vec![y, x]);
        let neither = b.and(vec![-y, -x]);
        equal.push(b.or(vec![both, neither]));
        let only_y = b.and(vec![y, -x]);
        let only_x = b.and(vec![-y, x]);
        inverted.push(b.or(vec![only_y, only_x]));
    }
    let left = b.and(equal);
    let right = b.and(inverted);
    let out = b.or(vec![left, right]);
    b.finish(out)
}

/// Deterministic xorshift RNG for reproducible random circuits.
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
}

/// A random and/or/xor circuit over `u` universal and `e` existential
/// inputs (mixed verdicts across seeds).
fn random_circuit(u: usize, e: usize, gates: usize, seed: u64) -> Circuit {
    let mut rng = Rng(seed);
    let mut b = Builder::new(u, e);
    for idx in 0..gates {
        let defined = u64::try_from(u + e + idx).unwrap();
        let lit = |rng: &mut Rng| {
            let raw = i32::try_from(rng.below(2 * defined)).unwrap();
            let var = raw / 2 + 1;
            if raw % 2 == 0 {
                var
            } else {
                -var
            }
        };
        let (a, second) = (lit(&mut rng), lit(&mut rng));
        match rng.below(3) {
            0 => b.and(vec![a, second]),
            1 => b.or(vec![a, second]),
            _ => b.xor(a, second),
        };
    }
    let out = {
        let defined = u64::try_from(u + e + gates).unwrap();
        let raw = i32::try_from(rng.below(2 * defined)).unwrap();
        let var = raw / 2 + 1;
        if raw % 2 == 0 {
            var
        } else {
            -var
        }
    };
    b.finish(out)
}

/// Solves one encoding and reports verdict, time, and structure
/// recovery (initially determinized variables / all existentials).
/// How many existentials the *matrix itself* determines from the
/// universals, by Padoa's criterion.
///
/// This separates the two explanations for a low initially-determinized
/// count. Either the structure is not there — the formula genuinely
/// leaves those variables free — or it is there and propagation does
/// not find it. Propagation only cascades through clauses that force a
/// value locally; definability is the semantic question, over the whole
/// matrix at once, and it is the ceiling on what any amount of
/// detection could recover.
///
/// `v` is definable from the universals iff no two models agreeing on
/// every universal disagree on `v`. Take two copies of the matrix
/// sharing the universal variables and renaming everything else apart,
/// then ask for a model of the pair with `v` true in one copy and false
/// in the other: unsatisfiable means `v` is a function of the
/// universals.
fn definable_from_universals(circuit: &Circuit) -> Option<usize> {
    use varisat::{ExtendFormula, Lit as VLit, Solver};

    let matrix = circuit.two_sided_matrix();
    let inputs = circuit.inputs();
    let total = inputs + circuit.gates.len();
    // the primed copy renames every non-universal variable
    let prime = |v: i32| -> i32 {
        if v as usize <= circuit.universals {
            v
        } else {
            v + i32::try_from(total).expect("variable count fits an i32")
        }
    };
    let encode = |l: i32| VLit::from_dimacs(isize::try_from(l).expect("literal fits"));

    let mut solver = Solver::new();
    // A matrix with no models makes every variable vacuously definable
    // — no two models can disagree when there are none — so the
    // question is meaningless there and the count would be a
    // measurement artifact rather than structure.
    {
        let mut plain = Solver::new();
        for clause in &matrix {
            plain.add_clause(&clause.iter().map(|&l| encode(l)).collect::<Vec<_>>());
        }
        if !plain.solve().expect("the matrix is decidable") {
            return None;
        }
    }
    for clause in &matrix {
        let original: Vec<VLit> = clause.iter().map(|&l| encode(l)).collect();
        solver.add_clause(&original);
        let copy: Vec<VLit> =
            clause.iter().map(|&l| encode(l.signum() * prime(l.abs()))).collect();
        solver.add_clause(&copy);
    }
    // every existential and every gate variable is a candidate
    Some(
        (circuit.universals + 1..=total)
            .filter(|&v| {
                let v = i32::try_from(v).expect("variable fits an i32");
                solver.assume(&[encode(v), encode(-prime(v))]);
                !solver.solve().expect("the definability query is decidable")
            })
            .count(),
    )
}

/// Node cap for the Skolem-function BDDs: past this the answer is
/// "it blew up", which is the only answer that matters.
const BDD_LIMIT: usize = 1_000_000;

fn measure(name: &str, encoding: &str, qcnf: &QCNF) -> SolverResult {
    let mut options = Options::default();
    if std::env::var("BENCH_DEEP_DETERMINACY").is_ok() {
        options.deep_determinacy = true;
    }
    let mut solver = IncDet::from_qcnf_with_options(qcnf, options);
    let start = Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();
    let existentials: usize =
        qcnf.prefix.iter().filter(|(q, _)| *q == QuantTy::Exists).map(|(_, vars)| vars.len()).sum();
    // Skolem functions as BDDs, in the prefix order and in the order
    // that interleaves the two halves of the universal block — the
    // classic split between an exponential and a linear BDD for
    // arithmetic over two operands.
    let bdd = if result == SolverResult::Satisfiable {
        let model = solver.skolem_model();
        let universals = model.universals().len();
        let half = (universals + 1) / 2;
        let interleaved = |index: usize| -> u32 {
            let level = if index < half { 2 * index } else { 2 * (index - half) + 1 };
            u32::try_from(level).expect("level fits u32")
        };
        let show = |size: Option<(usize, usize)>| {
            size.map_or_else(|| ">1M".to_string(), |(largest, _)| largest.to_string())
        };
        format!(
            "{}/{}",
            show(model.bdd_size(BDD_LIMIT, &|index| u32::try_from(index).expect("fits"))),
            show(model.bdd_size(BDD_LIMIT, &interleaved)),
        )
    } else {
        "-".to_string()
    };
    let verdict = match result {
        SolverResult::Satisfiable => "sat",
        SolverResult::Unsatisfiable => "unsat",
        SolverResult::Unknown => "unknown",
    };
    println!(
        "{name:<24} {encoding:>10} {verdict:>7} {elapsed:>12.3?}  initial {:>5}/{existentials:<5} decisions {:>6} conflicts {:>6} bdd {bdd:>11}",
        solver.initial_deterministic().map_or_else(|| "-".to_string(), |d| d.to_string()),
        solver.decisions(),
        solver.conflicts(),
    );
    result
}

fn run(name: &str, circuit: &Circuit) {
    if let Some(filter) = std::env::args().nth(1) {
        if !name.contains(&filter) {
            return;
        }
    }
    if std::env::var("BENCH_DEFINABILITY").is_ok() {
        let total = circuit.existentials + circuit.gates.len();
        let definable = definable_from_universals(circuit)
            .map_or_else(|| "vacuous".to_string(), |d| d.to_string());
        println!("{name:<24} {:>10} definable {definable:>7}/{total:<5}", "padoa");
    }
    let parsed = qcir::parse_qcir(&circuit.to_qcir()).expect("generated circuit parses");
    assert!(!parsed.negated);
    let definition = measure(name, "qcir", &parsed.qcnf);
    let two_sided = measure(name, "two-sided", &circuit.to_two_sided());
    let pg = measure(name, "pg", &circuit.to_plaisted_greenbaum());
    assert_eq!(definition, two_sided, "{name}: encodings must agree");
    assert_eq!(definition, pg, "{name}: encodings must agree");
}

fn main() {
    tracing_subscriber::fmt::init();
    let total = Instant::now();
    for n in [16, 32, 64] {
        run(&format!("parity-eq-{n}"), &parity_equalities(n));
    }
    for bits in [3, 4, 5] {
        run(&format!("mux-tree-{bits}"), &mux_tree(bits));
    }
    for n in [8, 12, 16] {
        run(&format!("choice-{n}"), &choice_of_relation(n));
    }
    // Random circuits are the family where gate inputs are picked
    // independently at random, so a gate's premises are frequently
    // *other gates sharing inputs* — heavy reconvergent fanout, and
    // premises that are therefore correlated. Enough seeds to tell a
    // real effect from search variance; the structured families above
    // (parity, mux tree, adder) are the contrast.
    for seed in 1..=24 {
        run(&format!("random-6-10-40-{seed:02}"), &random_circuit(6, 10, 40, seed));
    }
    for seed in 1..=12 {
        run(&format!("random-8-14-60-{seed:02}"), &random_circuit(8, 14, 60, seed));
    }
    // widths chosen to show *scaling*: the inverted adder is the
    // definitional shape (∀x ∃y. x = y + c), where ID determinizes
    // every bit by propagation and nothing enumerates, so it should
    // stay linear in the width
    for n in [4, 8, 16, 32, 64] {
        run(&format!("bv-add-inverse-{n}"), &adder_inverse(n));
    }
    for n in [4, 6, 8] {
        run(&format!("bv-ult-choice-{n}"), &comparator_choice(n));
    }
    println!("total: {:.3?}", total.elapsed());
}
