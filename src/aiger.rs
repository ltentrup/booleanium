//! QAIGER input: 2QBF instances given as AIGER circuits.
//!
//! This is the definition-level input path: the circuit arrives as *gate
//! definitions* instead of clauses, so no structure is lost to one-sided
//! (Plaisted–Greenbaum-style) CNF encodings — every gate variable is
//! deterministic by construction and incremental determinization recovers
//! all of them in the initial propagation.
//!
//! The QAIGER convention (following CADET): the input is a combinational
//! ASCII AIGER circuit; inputs whose symbol name starts with `"2 "` are
//! *controllable* (existential), all other inputs — and latches, which are
//! treated as uncontrollable inputs — are universal. The formula asks
//! whether for every assignment of the universal inputs the controllable
//! inputs can be set such that the output is true. AND gates become
//! existential variables defined by their two-sided Tseitin clauses; bad
//! signals are conjoined with the outputs.
//!
//! [`Unroller`] is the *sequential* reading of the same format: latches
//! advance by their next-state functions from their reset values, outputs
//! are error signals to keep false, and each time step becomes one
//! monotone extension of an incremental ∀∃ solver — the per-depth bounded
//! safety queries of a synthesis loop (SYNTCOMP marks controllable inputs
//! with the `controllable_` name prefix, accepted alongside `"2 "`).

use crate::{incremental::IncrementalSolver, qcnf::QCNF, QuantTy, SolverResult};
use std::collections::HashSet;
use std::fmt;

/// Whether an input symbol name marks a controllable (existential) input:
/// the QAIGER convention (`"2 "`, following CADET) or the SYNTCOMP
/// synthesis convention (`"controllable_"`).
fn is_controllable(name: &str) -> bool {
    name.starts_with("2 ") || name.starts_with("controllable_")
}

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
    pub line: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "aiger parse error in line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for ParseError {}

struct And {
    lhs: u64,
    rhs0: u64,
    rhs1: u64,
}

struct Latch {
    lit: u64,
    next: u64,
    /// reset value, 0 or 1 (uninitialized latches are not supported)
    reset: u64,
}

/// An ASCII AIGER (`aag`) file, read far enough for QAIGER purposes.
struct Aiger {
    max_var: u64,
    inputs: Vec<u64>,
    latches: Vec<Latch>,
    outputs: Vec<u64>,
    ands: Vec<And>,
    /// symbol names of the inputs, by input position
    input_names: Vec<Option<String>>,
    /// symbol names of the outputs, by output position
    output_names: Vec<Option<String>>,
}

/// Parses an ASCII AIGER file and converts it into a 2QBF instance.
///
/// # Errors
///
/// Returns an error if the input is not a well-formed combinational ASCII
/// AIGER file.
pub fn parse_qaiger(input: &str) -> Result<QCNF, ParseError> {
    let aiger = parse_aag(input)?;
    Ok(to_qcnf(&aiger))
}

fn err(line: usize, message: impl Into<String>) -> ParseError {
    ParseError { message: message.into(), line }
}

fn parse_aag(input: &str) -> Result<Aiger, ParseError> {
    let mut lines = input.lines().enumerate();
    let (_, header) = lines.next().ok_or_else(|| err(1, "empty input"))?;
    let fields: Vec<&str> = header.split_ascii_whitespace().collect();
    if fields.first() != Some(&"aag") {
        return Err(err(1, "expected an ASCII AIGER header starting with 'aag'"));
    }
    let numbers: Vec<u64> = fields[1..]
        .iter()
        .map(|f| f.parse().map_err(|_| err(1, format!("invalid header field {f}"))))
        .collect::<Result<_, _>>()?;
    if numbers.len() < 5 {
        return Err(err(1, "header needs at least the fields M I L O A"));
    }
    let (max_var, num_inputs, num_latches, num_outputs, num_ands) =
        (numbers[0], numbers[1], numbers[2], numbers[3], numbers[4]);
    let num_bad = numbers.get(5).copied().unwrap_or(0);
    if numbers.get(6).is_some_and(|&c| c > 0) {
        return Err(err(1, "invariant constraints are not supported"));
    }

    let mut next = |what: &str| {
        lines
            .next()
            .ok_or_else(|| err(usize::MAX, format!("unexpected end of file reading {what}")))
    };
    let mut literal = |what: &str| -> Result<(usize, Vec<u64>), ParseError> {
        let (no, line) = next(what)?;
        let lits = line
            .split_ascii_whitespace()
            .map(|f| f.parse().map_err(|_| err(no + 1, format!("invalid literal {f}"))))
            .collect::<Result<Vec<u64>, _>>()?;
        Ok((no, lits))
    };

    let mut inputs = Vec::new();
    for _ in 0..num_inputs {
        let (no, lits) = literal("an input")?;
        match lits[..] {
            [lit] if lit % 2 == 0 && lit >= 2 => inputs.push(lit),
            _ => return Err(err(no + 1, "an input must be a single positive literal")),
        }
    }
    let mut latches = Vec::new();
    for _ in 0..num_latches {
        let (no, lits) = literal("a latch")?;
        match lits[..] {
            [lit, next] if lit % 2 == 0 && lit >= 2 => {
                latches.push(Latch { lit, next, reset: 0 });
            }
            [lit, next, reset] if lit % 2 == 0 && lit >= 2 && reset <= 1 => {
                latches.push(Latch { lit, next, reset });
            }
            [lit, _, reset] if reset == lit => {
                return Err(err(no + 1, "uninitialized latches are not supported"));
            }
            _ => return Err(err(no + 1, "a latch needs the fields lit next [reset]")),
        }
    }
    let mut outputs = Vec::new();
    for _ in 0..num_outputs + num_bad {
        let (no, lits) = literal("an output")?;
        match lits[..] {
            [lit] => outputs.push(lit),
            _ => return Err(err(no + 1, "an output must be a single literal")),
        }
    }
    let mut ands = Vec::new();
    for _ in 0..num_ands {
        let (no, lits) = literal("an and gate")?;
        match lits[..] {
            [lhs, rhs0, rhs1] if lhs % 2 == 0 && lhs >= 2 => ands.push(And { lhs, rhs0, rhs1 }),
            _ => return Err(err(no + 1, "an and gate needs the fields lhs rhs0 rhs1")),
        }
    }

    // symbol table: input names carry controllability, output names
    // identify the defined variables of strategy circuits
    let mut input_names = vec![None; inputs.len()];
    let mut output_names = vec![None; outputs.len()];
    for (_, line) in lines {
        if line.starts_with('c') {
            break;
        }
        let target = match line.chars().next() {
            Some('i') => &mut input_names,
            Some('o') => &mut output_names,
            _ => continue,
        };
        if let Some((pos, name)) = line[1..].split_once(' ') {
            if let Ok(pos) = pos.parse::<usize>() {
                if pos < target.len() {
                    target[pos] = Some(name.to_string());
                }
            }
        }
    }

    Ok(Aiger { max_var, inputs, latches, outputs, ands, input_names, output_names })
}

fn to_qcnf(aiger: &Aiger) -> QCNF {
    // aiger variable v keeps the DIMACS number v; one fresh variable
    // represents the constant true
    let true_var = i32::try_from(aiger.max_var).expect("variable count fits an i32") + 1;
    let lit = |aiger_lit: u64| -> i32 {
        match aiger_lit {
            0 => -true_var,
            1 => true_var,
            _ => {
                let var = i32::try_from(aiger_lit / 2).expect("variable fits an i32");
                if aiger_lit % 2 == 0 {
                    var
                } else {
                    -var
                }
            }
        }
    };

    let mut universals: Vec<u32> = Vec::new();
    let mut existentials: Vec<u32> = vec![true_var.unsigned_abs()];
    for (pos, &input) in aiger.inputs.iter().enumerate() {
        let controllable = aiger.input_names[pos].as_deref().is_some_and(is_controllable);
        let var = u32::try_from(input / 2).expect("variable fits a u32");
        if controllable {
            existentials.push(var);
        } else {
            universals.push(var);
        }
    }
    for latch in &aiger.latches {
        universals.push(u32::try_from(latch.lit / 2).expect("variable fits a u32"));
    }
    for and in &aiger.ands {
        existentials.push(u32::try_from(and.lhs / 2).expect("variable fits a u32"));
    }

    let mut matrix: Vec<Vec<i32>> = Vec::new();
    // the constant true
    matrix.push(vec![true_var]);
    // the output(s) must hold: a single output is asserted directly, several
    // outputs (or bad signals) are conjoined
    match aiger.outputs[..] {
        [] => {}
        [out] => matrix.push(vec![lit(out)]),
        ref outs => matrix.extend(outs.iter().map(|&out| vec![lit(out)])),
    }
    // two-sided Tseitin definition of every gate; clauses touching the
    // constant simplify away during loading
    for and in &aiger.ands {
        matrix.push(vec![-lit(and.lhs), lit(and.rhs0)]);
        matrix.push(vec![-lit(and.lhs), lit(and.rhs1)]);
        matrix.push(vec![lit(and.lhs), -lit(and.rhs0), -lit(and.rhs1)]);
    }

    let prefix: Vec<(QuantTy, &[u32])> =
        vec![(QuantTy::Forall, &universals[..]), (QuantTy::Exists, &existentials[..])];
    let matrix_refs: Vec<&[i32]> = matrix.iter().map(Vec::as_slice).collect();
    QCNF::new(&prefix, &matrix_refs)
}

/// What an AIGER variable denotes, by position in its section.
#[derive(Clone, Copy)]
enum Class {
    Input(usize),
    Latch(usize),
    Gate(usize),
}

/// A sequential AIGER safety specification unrolled step by step into an
/// incremental ∀∃ solver — the per-depth bounded safety queries of a
/// synthesis loop.
///
/// The SYNTCOMP reading of the circuit: outputs (and bad signals) are
/// *error* signals that the controllable inputs must keep false at every
/// step against every play of the uncontrollable inputs; latches start at
/// their reset values and advance by their next-state functions. Each
/// [`Unroller::step`] declares fresh copies of the inputs and gates,
/// connects the latches to the previous step, and asserts the error
/// signals false; solving after `k` steps asks whether the system stays
/// safe for `k` steps. The unrolling is monotone (declarations and
/// clauses only), so plain re-solves ride the in-place continuation.
///
/// The Skolem function of a controllable input at step `t` may depend on
/// the whole universal input sequence, including later steps — the
/// clairvoyant relaxation inherent to a ∀∃ prefix. A satisfiable depth is
/// therefore a *necessary* condition for realizability, and an
/// unsatisfiable depth refutes it outright.
pub struct Unroller {
    aiger: Aiger,
    /// controllability of each input, by input position
    controllable: Vec<bool>,
    /// what each AIGER variable denotes, indexed by variable number
    classes: Vec<Option<Class>>,
    /// solver variable of the constant true, allocated on the first step
    true_var: Option<u32>,
    /// solver variables of the latches at the frontier time step
    latch_vars: Vec<u32>,
    /// solver variables of the inputs of the most recent step, by input
    /// position
    input_vars: Vec<u32>,
    /// every input variable declared so far: `(solver var, step,
    /// controllable)` with steps numbered from 1
    declared_inputs: Vec<(u32, u32, bool)>,
    depth: u32,
}

impl Unroller {
    /// Parses a sequential ASCII AIGER safety specification.
    ///
    /// # Errors
    ///
    /// Returns an error if the input is not a well-formed ASCII AIGER
    /// file with initialized latches.
    pub fn new(input: &str) -> Result<Self, ParseError> {
        let aiger = parse_aag(input)?;
        let controllable =
            aiger.input_names.iter().map(|n| n.as_deref().is_some_and(is_controllable)).collect();
        let var = |lit: u64| usize::try_from(lit / 2).expect("variable fits a usize");
        let mut classes = vec![None; usize::try_from(aiger.max_var).expect("fits") + 1];
        for (pos, &input) in aiger.inputs.iter().enumerate() {
            classes[var(input)] = Some(Class::Input(pos));
        }
        for (idx, latch) in aiger.latches.iter().enumerate() {
            classes[var(latch.lit)] = Some(Class::Latch(idx));
        }
        for (idx, and) in aiger.ands.iter().enumerate() {
            classes[var(and.lhs)] = Some(Class::Gate(idx));
        }
        Ok(Self {
            aiger,
            controllable,
            classes,
            true_var: None,
            latch_vars: Vec::new(),
            input_vars: Vec::new(),
            declared_inputs: Vec::new(),
            depth: 0,
        })
    }

    /// The number of steps unrolled so far.
    #[must_use]
    pub fn depth(&self) -> u32 {
        self.depth
    }

    /// The solver variables of the inputs of the most recent step, by
    /// input position — the handles a synthesis loop needs to probe
    /// current-step moves with assumption queries. Empty before the
    /// first step.
    #[must_use]
    pub fn current_inputs(&self) -> &[u32] {
        &self.input_vars
    }

    /// Unrolls one time step into the solver: fresh input and gate
    /// copies, the latch connection to the previous step, and the error
    /// signals asserted false. Solve after stepping to obtain the
    /// bounded-safety verdict for the new depth.
    ///
    /// # Panics
    ///
    /// Panics if the circuit references an undefined variable.
    pub fn step(&mut self, solver: &mut IncrementalSolver) {
        let dimacs = |v: u32| i32::try_from(v).expect("variable fits an i32");
        let true_var = *self.true_var.get_or_insert_with(|| {
            let v = solver.fresh_var();
            solver.declare_existential(v);
            solver.add_clause(&[dimacs(v)]);
            v
        });
        if self.depth == 0 {
            // the latches take their reset values at time zero
            for latch in &self.aiger.latches {
                let v = solver.fresh_var();
                solver.declare_existential(v);
                solver.add_clause(&[if latch.reset == 1 { dimacs(v) } else { -dimacs(v) }]);
                self.latch_vars.push(v);
            }
        }
        let mut input_vars = Vec::with_capacity(self.aiger.inputs.len());
        for &controllable in &self.controllable {
            let v = solver.fresh_var();
            if controllable {
                solver.declare_existential(v);
            } else {
                solver.declare_universal(v);
            }
            self.declared_inputs.push((v, self.depth + 1, controllable));
            input_vars.push(v);
        }
        let mut gate_vars = Vec::with_capacity(self.aiger.ands.len());
        for _ in &self.aiger.ands {
            let v = solver.fresh_var();
            solver.declare_existential(v);
            gate_vars.push(v);
        }
        // an AIGER literal at the current time step as a solver literal
        let lit = |aiger_lit: u64| -> i32 {
            let var = match aiger_lit {
                0 => return -dimacs(true_var),
                1 => return dimacs(true_var),
                _ => {
                    let index = usize::try_from(aiger_lit / 2).expect("variable fits a usize");
                    let class = self.classes[index].expect("defined variable");
                    match class {
                        Class::Input(pos) => input_vars[pos],
                        Class::Latch(idx) => self.latch_vars[idx],
                        Class::Gate(idx) => gate_vars[idx],
                    }
                }
            };
            if aiger_lit % 2 == 0 {
                dimacs(var)
            } else {
                -dimacs(var)
            }
        };
        for (idx, and) in self.aiger.ands.iter().enumerate() {
            let lhs = dimacs(gate_vars[idx]);
            solver.add_clause(&[-lhs, lit(and.rhs0)]);
            solver.add_clause(&[-lhs, lit(and.rhs1)]);
            solver.add_clause(&[lhs, -lit(and.rhs0), -lit(and.rhs1)]);
        }
        // the error signals must not fire at this step
        for &out in &self.aiger.outputs {
            solver.add_clause(&[-lit(out)]);
        }
        // advance the latches: the next frontier copy equals the
        // next-state literal evaluated at the current step
        let next_vars: Vec<u32> = self
            .aiger
            .latches
            .iter()
            .map(|latch| {
                let v = solver.fresh_var();
                solver.declare_existential(v);
                solver.add_clause(&[-dimacs(v), lit(latch.next)]);
                solver.add_clause(&[dimacs(v), -lit(latch.next)]);
                v
            })
            .collect();
        self.latch_vars = next_vars;
        self.input_vars = input_vars;
        self.depth += 1;
    }

    /// Unrolls the specification into a *reactive* QBF: one quantifier
    /// alternation per time step, `∀I₀ ∃C₀ ∀I₁ ∃C₁ …`, with the gate,
    /// latch, and controllable variables of step `t` in the existential
    /// block of that step. A controllable input may therefore depend
    /// only on the uncontrollable inputs of its own step and earlier —
    /// which is what the game actually grants the controller.
    ///
    /// This is the honest counterpart of the flat ∀∃ unrolling
    /// [`Unroller::step`] builds. That one puts every universal input
    /// ahead of every controllable one, so its Skolem functions may
    /// read the future; a satisfiable answer is only *necessary* for
    /// realizability and needs [`Unroller::strategy_is_causal`]
    /// afterwards. Here causality is a property of the prefix, so a
    /// satisfiable answer *is* realizability for the depth — paid for
    /// with `2·depth` quantifier blocks instead of two.
    ///
    /// The two encodings genuinely disagree: a pursuit game whose
    /// obstacle can stand still is lost by a reactive robot but won by
    /// a clairvoyant one that times its swaps around a known obstacle
    /// sequence, so the flat unrolling reports satisfiable where this
    /// one reports unsatisfiable (see `RESEARCH.md`, RQ5).
    #[must_use]
    pub fn alternating(&self, depth: u32) -> QCNF {
        use crate::literal::{Lit, Var};
        let var = Var::from_dimacs;

        let mut prefix: Vec<(QuantTy, Vec<Var>)> = Vec::new();
        let mut matrix: Vec<Vec<i32>> = Vec::new();
        let mut next: i32 = 1;
        let fresh = |next: &mut i32| {
            let v = *next;
            *next += 1;
            v
        };

        // constants: the true literal and the latch reset values. They
        // are quantifier-independent, so they ride in the first
        // existential block.
        let true_var = fresh(&mut next);
        let mut existential: Vec<Var> = vec![var(true_var)];
        matrix.push(vec![true_var]);
        let mut latch_vars: Vec<i32> = Vec::new();
        for latch in &self.aiger.latches {
            let v = fresh(&mut next);
            existential.push(var(v));
            matrix.push(vec![if latch.reset == 1 { v } else { -v }]);
            latch_vars.push(v);
        }

        for _ in 0..depth {
            let mut universal: Vec<Var> = Vec::new();
            let mut input_vars: Vec<i32> = Vec::with_capacity(self.aiger.inputs.len());
            for &controllable in &self.controllable {
                let v = fresh(&mut next);
                if controllable {
                    existential.push(var(v));
                } else {
                    universal.push(var(v));
                }
                input_vars.push(v);
            }
            let mut gate_vars: Vec<i32> = Vec::with_capacity(self.aiger.ands.len());
            for _ in &self.aiger.ands {
                let v = fresh(&mut next);
                existential.push(var(v));
                gate_vars.push(v);
            }
            // an AIGER literal at this step, as a DIMACS literal
            let lit = |aiger_lit: u64| -> i32 {
                let v = match aiger_lit {
                    0 => return -true_var,
                    1 => return true_var,
                    _ => {
                        let index = usize::try_from(aiger_lit / 2).expect("fits");
                        match self.classes[index].expect("defined variable") {
                            Class::Input(pos) => input_vars[pos],
                            Class::Latch(idx) => latch_vars[idx],
                            Class::Gate(idx) => gate_vars[idx],
                        }
                    }
                };
                if aiger_lit % 2 == 0 {
                    v
                } else {
                    -v
                }
            };
            for (idx, and) in self.aiger.ands.iter().enumerate() {
                let lhs = gate_vars[idx];
                matrix.push(vec![-lhs, lit(and.rhs0)]);
                matrix.push(vec![-lhs, lit(and.rhs1)]);
                matrix.push(vec![lhs, -lit(and.rhs0), -lit(and.rhs1)]);
            }
            // no error signal may fire at this step
            for &out in &self.aiger.outputs {
                matrix.push(vec![-lit(out)]);
            }
            // the next state, defined from this step and read by the next
            let mut advanced: Vec<i32> = Vec::with_capacity(self.aiger.latches.len());
            for latch in &self.aiger.latches {
                let v = fresh(&mut next);
                existential.push(var(v));
                matrix.push(vec![-v, lit(latch.next)]);
                matrix.push(vec![v, -lit(latch.next)]);
                advanced.push(v);
            }
            latch_vars = advanced;
            prefix.push((QuantTy::Forall, universal));
            prefix.push((QuantTy::Exists, std::mem::take(&mut existential)));
        }
        QCNF {
            prefix,
            matrix: matrix
                .into_iter()
                .map(|clause| clause.into_iter().map(Lit::from_dimacs).collect())
                .collect(),
        }
    }

    /// Checks whether a strategy circuit for this unrolling (an ASCII
    /// AIGER emitted by `SkolemModel::to_aiger` with numeric labels) is
    /// *causal*: every controllable input's value depends only on
    /// uncontrollable inputs of its own step or earlier. A bounded ∀∃
    /// answer is only a *necessary* condition for realizability because
    /// its Skolem functions may read future universal inputs; a causal
    /// strategy closes the gap — it wins the real game for the unrolled
    /// depth. The check is *semantic*: per controllable output, a SAT
    /// call asks whether two copies of the circuit that agree on all
    /// inputs of steps up to the output's step can disagree on the
    /// output (structural cones are too coarse — the region selectors
    /// of a piecewise model routinely mix steps even when the selected
    /// values agree).
    ///
    /// # Errors
    ///
    /// Returns an error if the strategy text is not a well-formed
    /// combinational ASCII AIGER circuit.
    pub fn strategy_is_causal(&self, strategy: &str) -> Result<bool, ParseError> {
        use crate::literal::Lit;
        use crate::sat::{varisat::Varisat, LookupSolver, SatSolver};

        let circuit = parse_aag(strategy)?;
        let steps: std::collections::HashMap<u32, (u32, bool)> =
            self.declared_inputs.iter().map(|&(v, s, c)| (v, (s, c))).collect();
        let parse_name =
            |name: &Option<String>| -> Option<u32> { name.as_deref().and_then(|n| n.parse().ok()) };
        let input_step: Vec<Option<u32>> = circuit
            .input_names
            .iter()
            .map(|name| parse_name(name).and_then(|v| steps.get(&v).map(|&(s, _)| s)))
            .collect();
        let offset = i32::try_from(circuit.max_var).expect("variable count fits an i32") + 1;
        // `copy` 0/1 selects the circuit copy; constants share one
        // always-true variable at DIMACS 2 * offset
        let key = |l: u64, copy: i32| -> Lit {
            let truth = 2 * offset;
            match l {
                0 => Lit::from_dimacs(-truth),
                1 => Lit::from_dimacs(truth),
                _ => {
                    let var = i32::try_from(l / 2).expect("variable fits an i32") + copy * offset;
                    Lit::from_dimacs(if l % 2 == 0 { var } else { -var })
                }
            }
        };

        for (position, &out) in circuit.outputs.iter().enumerate() {
            let Some(var) = parse_name(&circuit.output_names[position]) else {
                continue;
            };
            let Some(&(step, controllable)) = steps.get(&var) else {
                continue;
            };
            if !controllable {
                continue;
            }
            let mut solver = LookupSolver::<Varisat>::default();
            solver.set_var_count(usize::try_from(2 * offset).expect("fits") + 1);
            let truth = solver.lookup(key(1, 0));
            solver.add_clause(&[truth]);
            for copy in 0..2 {
                for and in &circuit.ands {
                    let lhs = solver.lookup(key(and.lhs, copy));
                    let rhs0 = solver.lookup(key(and.rhs0, copy));
                    let rhs1 = solver.lookup(key(and.rhs1, copy));
                    solver.add_clause(&[!lhs, rhs0]);
                    solver.add_clause(&[!lhs, rhs1]);
                    solver.add_clause(&[lhs, !rhs0, !rhs1]);
                }
            }
            // inputs of steps up to the output's step are shared
            for (pos, &input) in circuit.inputs.iter().enumerate() {
                if input_step[pos].is_some_and(|s| s <= step) {
                    let a = solver.lookup(key(input, 0));
                    let b = solver.lookup(key(input, 1));
                    solver.add_clause(&[!a, b]);
                    solver.add_clause(&[a, !b]);
                }
            }
            // can the two copies disagree on this output?
            let a = solver.lookup(key(out, 0));
            let b = solver.lookup(key(out, 1));
            solver.add_clause(&[a, b]);
            solver.add_clause(&[!a, !b]);
            if solver.solve().unwrap() {
                return Ok(false);
            }
        }
        Ok(true)
    }
}



/// The outcome of a safety-game fixpoint computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SafetyOutcome {
    /// whether the controller wins from the initial state — an
    /// *unbounded* answer, not a bounded approximation
    pub realizable: bool,
    /// the losing region, as cubes over the latches (index, value);
    /// its complement is the greatest fixpoint `νW. CPre(W)`
    pub losing: Vec<Vec<(usize, bool)>>,
    /// refinement rounds taken, i.e. incremental solves
    pub rounds: u32,
    /// how many of those computed the *safe states* (`CPre(⊤)`) before
    /// the backward induction began
    pub safe_rounds: u32,
    /// in-place monotone extensions the incremental core managed over
    /// the run — how much of the refinement the continuation actually
    /// absorbed, rather than falling back to a rebuild
    pub extensions: u32,
    /// rounds whose refutation carried no verifiable universal witness,
    /// so a single state had to be proved losing by assumption queries
    pub fallback_rounds: u32,
}

/// Solves a safety game by shrinking the winning region instead of
/// unrolling the game.
///
/// The winning region starts as *all* states and is refined by the
/// query "from every state of `W`, whatever the environment plays, can
/// the controller avoid the error and stay in `W`?" — the one-step
/// controllable predecessor, `∀ state, uncontrollable. ∃ controllable`,
/// which is **2QBF whatever the game's depth**. Unsatisfiable yields a
/// universal witness: a state (and the environment move refuting it)
/// that is not in `CPre(W)`, so its whole cube leaves `W` and the query
/// is re-asked. Satisfiable means `W = CPre(W)`, the greatest fixpoint,
/// and the controller wins iff the initial state survived.
///
/// Every refinement is an *addition* — fresh membership variables and
/// clauses, with the previous round's constraint retired by a unit on
/// its activation literal — so the whole loop rides the in-place
/// monotone continuation of [`IncrementalSolver`] and every learnt
/// clause carries across rounds. This is the access pattern the
/// incremental interface was designed for, and unlike the unrolling
/// ([`Unroller`]) it answers realizability outright rather than for a
/// bound, with a winning region instead of a depth-limited strategy.
///
/// # Errors
///
/// Returns an error if the input is not a well-formed ASCII AIGER
/// safety specification.
///
/// # Panics
///
/// Panics if a refutation arrives without a verifiable universal
/// witness, which would leave the refinement with nothing to remove.
pub fn solve_safety(
    input: &str,
    options: crate::incdet::Options,
) -> Result<SafetyOutcome, ParseError> {
    solve_safety_with_continuation(input, options, true)
}

/// [`solve_safety`] with the in-place continuation switchable, so a
/// benchmark can price what the incremental stack is worth on this
/// loop against rebuilding the core per refinement.
///
/// # Errors
///
/// Returns an error if the input is not a well-formed ASCII AIGER
/// safety specification.
///
/// # Panics
///
/// Panics if an unsatisfiable region query yields no losing state,
/// which cannot happen.
#[allow(clippy::too_many_lines)]
pub fn solve_safety_with_continuation(
    input: &str,
    options: crate::incdet::Options,
    continuation: bool,
) -> Result<SafetyOutcome, ParseError> {
    let aiger = parse_aag(input)?;
    let controllable: Vec<bool> =
        aiger.input_names.iter().map(|n| n.as_deref().is_some_and(is_controllable)).collect();
    let var = |lit: u64| usize::try_from(lit / 2).expect("variable fits a usize");
    let mut classes = vec![None; usize::try_from(aiger.max_var).expect("fits") + 1];
    for (pos, &input) in aiger.inputs.iter().enumerate() {
        classes[var(input)] = Some(Class::Input(pos));
    }
    for (idx, latch) in aiger.latches.iter().enumerate() {
        classes[var(latch.lit)] = Some(Class::Latch(idx));
    }
    for (idx, and) in aiger.ands.iter().enumerate() {
        classes[var(and.lhs)] = Some(Class::Gate(idx));
    }

    let mut solver = IncrementalSolver::new(options);
    solver.set_continuation(continuation);
    let dimacs = |v: u32| i32::try_from(v).expect("variable fits an i32");
    let universal = |solver: &mut IncrementalSolver| {
        let v = solver.fresh_var();
        solver.declare_universal(v);
        v
    };
    // the current state and the environment move are the universals;
    // everything the controller computes from them is existential
    let state_vars: Vec<u32> = aiger.latches.iter().map(|_| universal(&mut solver)).collect();
    let input_vars: Vec<u32> = controllable
        .iter()
        .map(|&c| {
            if c {
                let v = solver.fresh_var();
                solver.declare_existential(v);
                v
            } else {
                universal(&mut solver)
            }
        })
        .collect();
    let existential = |solver: &mut IncrementalSolver| {
        let v = solver.fresh_var();
        solver.declare_existential(v);
        v
    };
    let true_var = existential(&mut solver);
    solver.add_clause(&[dimacs(true_var)]);
    let gate_vars: Vec<u32> = aiger.ands.iter().map(|_| existential(&mut solver)).collect();
    let lit = |aiger_lit: u64| -> i32 {
        let v = match aiger_lit {
            0 => return -dimacs(true_var),
            1 => return dimacs(true_var),
            _ => match classes[var(aiger_lit)].expect("defined variable") {
                Class::Input(pos) => input_vars[pos],
                Class::Latch(idx) => state_vars[idx],
                Class::Gate(idx) => gate_vars[idx],
            },
        };
        if aiger_lit % 2 == 0 {
            dimacs(v)
        } else {
            -dimacs(v)
        }
    };
    for (idx, and) in aiger.ands.iter().enumerate() {
        let lhs = dimacs(gate_vars[idx]);
        solver.add_clause(&[-lhs, lit(and.rhs0)]);
        solver.add_clause(&[-lhs, lit(and.rhs1)]);
        solver.add_clause(&[lhs, -lit(and.rhs0), -lit(and.rhs1)]);
    }
    // the successor state, named so the winning region can speak about it
    let next_vars: Vec<u32> = aiger
        .latches
        .iter()
        .map(|latch| {
            let v = existential(&mut solver);
            solver.add_clause(&[-dimacs(v), lit(latch.next)]);
            solver.add_clause(&[dimacs(v), -lit(latch.next)]);
            v
        })
        .collect();

    // `outside[k]` holds iff the state is in one of the first k losing
    // cubes; the same chain over the successor is `next_outside`. Both
    // grow by one link per round, so nothing is ever rewritten.
    let mut outside: Option<u32> = None;
    let mut next_outside: Option<u32> = None;
    let mut losing: Vec<Vec<(usize, bool)>> = Vec::new();
    let mut rounds = 0u32;
    // The refinement runs in two phases. The first asks only "can the
    // controller avoid the error *now*", with no reference to the
    // successor, and its fixpoint is the set of **safe states** —
    // `CPre(⊤)`, a strictly better starting region than the whole state
    // space. Seeding the induction with it is the classical order, and
    // it matters here because the phase-one query is the smaller one:
    // it never mentions the successor, so its refutations are simpler
    // and their witnesses generalize to bigger cubes. Games whose error
    // is a state predicate — two tokens on one cell, a raised error
    // latch — are almost entirely decided by this phase.
    let mut induction = false;
    let mut safe_rounds = 0;
    let mut fallback_rounds = 0;

    loop {
        rounds += 1;
        // The round's constraint goes in a pushed frame and is popped
        // again once answered. Retiring it by an activation literal
        // instead left every clause learnt under it in the database
        // for the rest of the run, referring to a literal that could
        // never fire again; popping drops exactly those and keeps what
        // was learnt about the circuit and the region.
        solver.push();
        let relax: Vec<i32> = outside.iter().map(|&v| dimacs(v)).collect();
        for &out in &aiger.outputs {
            let mut clause = vec![-lit(out)];
            clause.extend(&relax);
            solver.add_clause(&clause);
        }
        if induction {
            if let Some(next_out) = next_outside {
                let mut clause = vec![-dimacs(next_out)];
                clause.extend(&relax);
                solver.add_clause(&clause);
            }
        }

        let began = std::time::Instant::now();
        let verdict = solver.solve();
        let refuted = began.elapsed();
        if verdict != SolverResult::Unsatisfiable {
            if !induction {
                // the safe states are known; now demand that the
                // controller can also *stay* among them
                induction = true;
                safe_rounds = rounds;
                solver.pop();
                continue;
            }
            // `W = CPre(W)`: the greatest fixpoint is reached
            let initial: Vec<bool> = aiger.latches.iter().map(|l| l.reset == 1).collect();
            let realizable = !losing
                .iter()
                .any(|cube| cube.iter().all(|&(idx, value)| initial[idx] == value));
            return Ok(SafetyOutcome {
                realizable,
                losing,
                rounds,
                safe_rounds,
                extensions: solver.extension_total(),
                fallback_rounds,
            });
        }
        // Aim the witness minimization at the state variables: the
        // environment's move is projected away, so only state literals
        // are worth dropping — and each one dropped doubles the
        // excluded region. The complete variant never comes back
        // empty-handed on an unsatisfiable round, so the region always
        // shrinks by a full cube.
        let state_set: HashSet<i32> = state_vars.iter().map(|&v| dimacs(v)).collect();
        let had_witness = solver.universal_witness().is_some();
        let witness = solver
            .universal_witness_complete(&|l| state_set.contains(&l.abs()))
            .expect("an unsatisfiable round has a winning universal move");
        if !had_witness {
            fallback_rounds += 1;
        }
        tracing::debug!(
            round = rounds,
            induction,
            solve = refuted.as_secs_f64(),
            extract = began.elapsed().as_secs_f64() - refuted.as_secs_f64(),
            literals = witness.len(),
            fallback = !had_witness,
            "refinement round"
        );
        let cube: Vec<(usize, bool)> = witness
            .iter()
            .filter_map(|&l| {
                let v = u32::try_from(l.abs()).expect("fits");
                state_vars.iter().position(|&s| s == v).map(|idx| (idx, l > 0))
            })
            .collect();
        if cube.is_empty() {
            // every state loses, so the initial one does too
            return Ok(SafetyOutcome {
                realizable: false,
                losing: vec![Vec::new()],
                rounds,
                safe_rounds,
                extensions: solver.extension_total(),
                fallback_rounds,
            });
        }

        // extend both membership chains by the new cube
        let link = |solver: &mut IncrementalSolver, vars: &[u32], chain: &mut Option<u32>| {
            let inside = solver.fresh_var();
            solver.declare_existential(inside);
            let cube_lits: Vec<i32> = cube
                .iter()
                .map(|&(idx, value)| {
                    if value {
                        dimacs(vars[idx])
                    } else {
                        -dimacs(vars[idx])
                    }
                })
                .collect();
            for &l in &cube_lits {
                solver.add_clause(&[-dimacs(inside), l]);
            }
            let mut reverse = vec![dimacs(inside)];
            reverse.extend(cube_lits.iter().map(|l| -l));
            solver.add_clause(&reverse);

            let joined = solver.fresh_var();
            solver.declare_existential(joined);
            solver.add_clause(&[-dimacs(inside), dimacs(joined)]);
            let mut forward = vec![-dimacs(joined), dimacs(inside)];
            if let Some(previous) = *chain {
                solver.add_clause(&[-dimacs(previous), dimacs(joined)]);
                forward.push(dimacs(previous));
            }
            solver.add_clause(&forward);
            *chain = Some(joined);
        };
        // the round's constraint has served its purpose; drop it and
        // the clauses learnt under it, then extend the region in the
        // base frame where the next round will read it
        solver.pop();
        link(&mut solver, &state_vars, &mut outside);
        link(&mut solver, &next_vars, &mut next_outside);
        losing.push(cube.clone());
    }
}

/// The value of an AIGER literal under a variable valuation.
fn litval(val: &[bool], l: u64) -> bool {
    match l {
        0 => false,
        1 => true,
        _ => val[usize::try_from(l / 2).unwrap()] ^ (l % 2 == 1),
    }
}

/// The exact winning region of a safety game, by explicit backward
/// iteration over the state space: start with every state and drop
/// those from which some environment move defeats every controller
/// move, until nothing changes. Independent of everything
/// [`solve_safety`] does — no solver, no encoding, no cubes.
fn winning_region(aiger: &Aiger, is_controllable: &[bool]) -> Vec<bool> {
    let positions = |want: bool| -> Vec<usize> {
        is_controllable
            .iter()
            .enumerate()
            .filter(|&(_, &c)| c == want)
            .map(|(p, _)| p)
            .collect()
    };
    let (uncontrollable, controllable) = (positions(false), positions(true));
    let latches = aiger.latches.len();
    let var = |l: u64| usize::try_from(l / 2).unwrap();
    let mut winning = vec![true; 1 << latches];
    loop {
        let mut next_winning = winning.clone();
        for state in 0..1usize << latches {
            if !winning[state] {
                continue;
            }
            let survives = (0..1u64 << uncontrollable.len()).all(|env| {
                (0..1u64 << controllable.len()).any(|ctl| {
                    let mut values =
                        vec![false; usize::try_from(aiger.max_var).unwrap() + 1];
                    for (bit, &pos) in uncontrollable.iter().enumerate() {
                        values[var(aiger.inputs[pos])] = env >> bit & 1 == 1;
                    }
                    for (bit, &pos) in controllable.iter().enumerate() {
                        values[var(aiger.inputs[pos])] = ctl >> bit & 1 == 1;
                    }
                    for (idx, latch) in aiger.latches.iter().enumerate() {
                        values[var(latch.lit)] = state >> idx & 1 == 1;
                    }
                    for and in &aiger.ands {
                        values[var(and.lhs)] =
                            litval(&values, and.rhs0) && litval(&values, and.rhs1);
                    }
                    if aiger.outputs.iter().any(|&out| litval(&values, out)) {
                        return false;
                    }
                    let successor = aiger
                        .latches
                        .iter()
                        .enumerate()
                        .filter(|(_, l)| litval(&values, l.next))
                        .fold(0usize, |acc, (idx, _)| acc | 1 << idx);
                    winning[successor]
                })
            });
            next_winning[state] = survives;
        }
        if next_winning == winning {
            return winning;
        }
        winning = next_winning;
    }
}


/// The states from which the controller loses, by explicit backward
/// iteration over the whole state space — no solver, no encoding, no
/// cubes. Exposed for the benchmarks, which price the refinement
/// loop's region against the region the game actually has.
///
/// # Errors
///
/// Returns an error if the input is not a well-formed ASCII AIGER file.
pub fn losing_states(input: &str, latches: usize) -> Result<Vec<bool>, ParseError> {
    let aiger = parse_aag(input)?;
    debug_assert_eq!(aiger.latches.len(), latches);
    let is_controllable: Vec<bool> =
        aiger.input_names.iter().map(|n| n.as_deref().is_some_and(is_controllable)).collect();
    Ok(winning_region(&aiger, &is_controllable).into_iter().map(|w| !w).collect())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{incdet::IncDet, SolverResult};

    #[allow(clippy::needless_pass_by_value)]
    fn solve(input: &str) -> SolverResult {
        let qcnf = parse_qaiger(input).expect("parses");
        let mut solver = IncDet::from_qcnf_with_options(&qcnf, crate::incdet::Options::default());
        let result = solver.solve();
        assert_eq!(result, qcnf.brute_force());
        if result == SolverResult::Satisfiable {
            assert!(solver.verify_skolem_functions());
        }
        result
    }

    #[test]
    fn qaiger_and() {
        // forall x, exists y: x & y — the universal x can be false
        let input = "aag 3 2 0 1 1\n2\n4\n6\n6 2 4\ni0 1 x\ni1 2 y\n";
        assert_eq!(solve(input), SolverResult::Unsatisfiable);
    }

    #[test]
    fn qaiger_equiv() {
        // forall x, exists y: x <-> y
        let input = "aag 5 2 0 1 3\n2\n4\n10\n6 2 5\n8 3 4\n10 7 9\ni0 1 x\ni1 2 y\n";
        assert_eq!(solve(input), SolverResult::Satisfiable);
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(256))]
        #[test]
        fn differential_qaiger(
            universals in 1usize..=4,
            controllables in 0usize..=4,
            gates in proptest::collection::vec((0u64..1000, 0u64..1000), 0..=12),
            output in 0u64..1000,
        ) {
            let inputs = universals + controllables;
            let mut text = format!(
                "aag {} {} 0 1 {}\n",
                inputs + gates.len(),
                inputs,
                gates.len()
            );
            for i in 0..inputs {
                text.push_str(&format!("{}\n", 2 * (i + 1)));
            }
            // a literal over the variables defined so far (inputs and
            // earlier gates), including the constants 0 and 1
            let pick = |seed: u64, defined: usize| seed % (2 * defined as u64 + 2);
            text.push_str(&format!("{}\n", pick(output, inputs + gates.len())));
            for (idx, &(a, b) ) in gates.iter().enumerate() {
                let lhs = 2 * (inputs + idx + 1) as u64;
                let defined = inputs + idx;
                text.push_str(&format!("{} {} {}\n", lhs, pick(a, defined), pick(b, defined)));
            }
            for i in 0..inputs {
                let quant = if i < universals { 1 } else { 2 };
                text.push_str(&format!("i{i} {quant} v{i}\n"));
            }
            solve(&text);
        }
    }

    /// Evaluates an AIGER literal under a variable valuation.
    /// Simulates the circuit for `k` steps under the given input bit
    /// streams (`stream[t]` holds the step-`t` value of the input at the
    /// given positions) and reports whether every error output stays
    /// false. Gates must be in dependency order.
    fn simulate_safe(
        aiger: &Aiger,
        uncontrollable: &[usize],
        controllable: &[usize],
        universal_seq: u64,
        control_seq: u64,
        k: u32,
    ) -> bool {
        let var = |l: u64| usize::try_from(l / 2).unwrap();
        let mut state: Vec<bool> = aiger.latches.iter().map(|l| l.reset == 1).collect();
        for t in 0..k {
            let mut values = vec![false; usize::try_from(aiger.max_var).unwrap() + 1];
            for (bit, &pos) in uncontrollable.iter().enumerate() {
                let stream_bit = t as usize * uncontrollable.len() + bit;
                values[var(aiger.inputs[pos])] = universal_seq >> stream_bit & 1 == 1;
            }
            for (bit, &pos) in controllable.iter().enumerate() {
                let stream_bit = t as usize * controllable.len() + bit;
                values[var(aiger.inputs[pos])] = control_seq >> stream_bit & 1 == 1;
            }
            for (idx, latch) in aiger.latches.iter().enumerate() {
                values[var(latch.lit)] = state[idx];
            }
            for and in &aiger.ands {
                values[var(and.lhs)] = litval(&values, and.rhs0) && litval(&values, and.rhs1);
            }
            if aiger.outputs.iter().any(|&out| litval(&values, out)) {
                return false;
            }
            state = aiger.latches.iter().map(|l| litval(&values, l.next)).collect();
        }
        true
    }

    /// The exact winning region, by explicit backward iteration; see
    /// [`super::winning_region`]. Kept as a thin alias so the tests
    /// read as before.
    fn winning_region(aiger: &Aiger, is_controllable: &[bool]) -> Vec<bool> {
        super::winning_region(aiger, is_controllable)
    }

    /// Runs the refinement loop and checks its answer, and its whole
    /// winning region, against the explicit fixpoint.
    fn check_safety(text: &str) -> SafetyOutcome {
        let aiger = parse_aag(text).expect("parses");
        let is_controllable: Vec<bool> =
            aiger.input_names.iter().map(|n| n.as_deref().is_some_and(is_controllable)).collect();
        let expected = winning_region(&aiger, &is_controllable);
        let outcome =
            solve_safety(text, crate::incdet::Options::default()).expect("spec parses");

        // every state the loop removed must really be losing, and every
        // state it kept must really be winning
        for (state, &winning) in expected.iter().enumerate() {
            let removed = outcome.losing.iter().any(|cube| {
                cube.iter().all(|&(idx, value)| (state >> idx & 1 == 1) == value)
            });
            assert_eq!(!removed, winning, "state {state} of:\n{text}");
        }
        let initial = aiger
            .latches
            .iter()
            .enumerate()
            .filter(|(_, l)| l.reset == 1)
            .fold(0usize, |acc, (idx, _)| acc | 1 << idx);
        assert_eq!(outcome.realizable, expected[initial], "verdict of:\n{text}");
        outcome
    }

    #[test]
    fn safety_generalizes_only_what_it_may() {
        // The fuzz's minimal case for a soundness bug in the fallback
        // extraction: the error is a latch, so `latch0` is losing
        // outright, and from `¬latch0 ∧ latch1` the controller cannot
        // stop `latch0` rising. Only the all-clear state survives.
        // Generalizing a self-reduced move by "the restriction is still
        // unsatisfiable" would drop `latch0` from the cube and take the
        // winning state with it — that test says *some* point of the
        // cube wins, not every point.
        let text = concat!(
            "aag 11 3 2 1 6\n2\n4\n6\n8 15 1\n10 8 0\n8\n",
            "12 6 4\n14 6 11\n16 14 14\n18 13 9\n20 4 2\n22 17 15\n",
            "i0 u0\ni1 controllable_c1\ni2 controllable_c2\n"
        );
        let outcome = check_safety(text);
        assert!(!outcome.realizable, "the initial state has the error latch set");
        assert_eq!(outcome.losing.len(), 2);
    }

    /// The `arbiter-4-4` benchmark family, verified against the
    /// explicit fixpoint rather than against another run of the solver.
    ///
    /// It is the one benchmark whose *verdict* the soundness fix above
    /// changed: four requesters, each losing after four consecutive
    /// steps of asking without a grant, and grants that may not
    /// overlap. Round-robin answers every requester every fourth step,
    /// so the gap is exactly three and the game is realizable — but
    /// only just, and the over-general cubes the old extraction
    /// produced removed the states that make it work, which reported
    /// it unrealizable in 21 ms. It is now realizable, in 57 rounds.
    ///
    /// Ignored by default: the explicit fixpoint sweeps 2^16 states
    /// and the solve takes minutes. Run with `--ignored`.
    #[test]
    #[ignore = "explicit backward fixpoint over 2^16 states, and a solve of minutes"]
    fn safety_arbiter_4_4_is_realizable() {
        let text = concat!(
            "aag 55 8 16 1 31\n2\n4\n6\n8\n10\n12\n14\n16\n",
            "18 50 0\n20 52 0\n22 54 0\n24 56 0\n26 58 0\n28 60 0\n30 62 0\n32 64 0\n",
            "34 66 0\n36 68 0\n38 70 0\n40 72 0\n42 74 0\n44 76 0\n46 78 0\n48 80 0\n",
            "111\n",
            "50 2 11\n52 18 11\n54 20 11\n56 22 11\n58 4 13\n60 26 13\n62 28 13\n64 30 13\n",
            "66 6 15\n68 34 15\n70 36 15\n72 38 15\n74 8 17\n76 42 17\n78 44 17\n80 46 17\n",
            "82 10 12\n84 10 14\n86 10 16\n88 12 14\n90 12 16\n92 14 16\n",
            "94 25 33\n96 94 41\n98 96 49\n100 98 83\n102 100 85\n104 102 87\n",
            "106 104 89\n108 106 91\n110 108 93\n",
            "i0 r0\ni1 r1\ni2 r2\ni3 r3\n",
            "i4 controllable_g0\ni5 controllable_g1\ni6 controllable_g2\ni7 controllable_g3\n"
        );
        let outcome = check_safety(text);
        assert!(outcome.realizable);
    }

    #[test]
    fn safety_copycat_is_realizable() {
        // error = u xor c: the controller copies and wins forever, so
        // no state is ever removed and the fixpoint is immediate
        let text = "aag 5 2 0 1 3\n2\n4\n10\n6 2 5\n8 3 4\n10 7 9\ni0 u\ni1 controllable_c\n";
        let outcome = check_safety(text);
        assert!(outcome.realizable);
        assert!(outcome.losing.is_empty());
        // one round establishes that every state is safe, one that the
        // controller can stay among them
        assert_eq!((outcome.safe_rounds, outcome.rounds), (1, 2));
    }

    #[test]
    fn safety_latch_delay_is_unrealizable() {
        // error = latch, latch next = uncontrollable input: the
        // environment raises the input and the controller cannot stop
        // it, so every state is lost and the initial one with it
        let text = "aag 2 1 1 1 0\n2\n4 2\n4\ni0 u\n";
        let outcome = check_safety(text);
        assert!(!outcome.realizable);
    }

    #[test]
    fn safety_refines_to_a_nontrivial_region() {
        // error = latch AND u; latch next = c. The controller must keep
        // the latch low forever: the state with the latch set is
        // losing, the state with it clear is winning, and the initial
        // state is the clear one.
        let text = concat!(
            "aag 4 2 1 1 1\n",
            "2\n4\n",       // u, controllable_c
            "6 4 0\n",      // latch := c
            "8\n",          // error
            "8 6 2\n",      // latch AND u
            "i0 u\ni1 controllable_c\n"
        );
        let outcome = check_safety(text);
        assert!(outcome.realizable);
        assert_eq!(outcome.losing.len(), 1);
    }

    /// The *reactive* bounded-safety oracle matching the alternating
    /// unrolling: at every step the environment moves first and the
    /// controller answers, so the controller's move may depend on the
    /// environment's moves so far but not on its future ones. Played
    /// out recursively over the concrete latch state, which is what
    /// makes it independent of everything the solver does.
    fn reactive_safe(aiger: &Aiger, is_controllable: &[bool], k: u32) -> bool {
        let positions = |want: bool| -> Vec<usize> {
            is_controllable
                .iter()
                .enumerate()
                .filter(|&(_, &c)| c == want)
                .map(|(p, _)| p)
                .collect()
        };
        let (uncontrollable, controllable) = (positions(false), positions(true));
        let state: Vec<bool> = aiger.latches.iter().map(|l| l.reset == 1).collect();
        reactive_from(aiger, &uncontrollable, &controllable, &state, k)
    }

    /// One step of [`reactive_safe`] from a concrete state: for every
    /// environment move there must be a controller move that stays safe
    /// now and keeps the remaining steps winnable.
    fn reactive_from(
        aiger: &Aiger,
        uncontrollable: &[usize],
        controllable: &[usize],
        state: &[bool],
        k: u32,
    ) -> bool {
        if k == 0 {
            return true;
        }
        let var = |l: u64| usize::try_from(l / 2).unwrap();
        (0..1u64 << uncontrollable.len()).all(|env| {
            (0..1u64 << controllable.len()).any(|ctl| {
                let mut values = vec![false; usize::try_from(aiger.max_var).unwrap() + 1];
                for (bit, &pos) in uncontrollable.iter().enumerate() {
                    values[var(aiger.inputs[pos])] = env >> bit & 1 == 1;
                }
                for (bit, &pos) in controllable.iter().enumerate() {
                    values[var(aiger.inputs[pos])] = ctl >> bit & 1 == 1;
                }
                for (idx, latch) in aiger.latches.iter().enumerate() {
                    values[var(latch.lit)] = state[idx];
                }
                for and in &aiger.ands {
                    values[var(and.lhs)] = litval(&values, and.rhs0) && litval(&values, and.rhs1);
                }
                if aiger.outputs.iter().any(|&out| litval(&values, out)) {
                    return false;
                }
                let next: Vec<bool> =
                    aiger.latches.iter().map(|l| litval(&values, l.next)).collect();
                reactive_from(aiger, uncontrollable, controllable, &next, k - 1)
            })
        })
    }

    /// The clairvoyant bounded-safety oracle matching the ∀∃ unrolling
    /// semantics: for every uncontrollable input sequence there must be a
    /// controllable input sequence keeping every step safe.
    fn clairvoyant_safe(aiger: &Aiger, is_controllable: &[bool], k: u32) -> bool {
        let positions = |want: bool| -> Vec<usize> {
            is_controllable
                .iter()
                .enumerate()
                .filter(|&(_, &c)| c == want)
                .map(|(p, _)| p)
                .collect()
        };
        let (uncontrollable, controllable) = (positions(false), positions(true));
        let universal_bits = uncontrollable.len() * k as usize;
        let control_bits = controllable.len() * k as usize;
        (0..1u64 << universal_bits).all(|universal_seq| {
            (0..1u64 << control_bits).any(|control_seq| {
                simulate_safe(aiger, &uncontrollable, &controllable, universal_seq, control_seq, k)
            })
        })
    }

    /// Unrolls a spec depth by depth, checking every verdict against the
    /// clairvoyant simulation oracle and certifying satisfiable results.
    fn check_unrolling(text: &str, k: u32, continuation: bool) -> Vec<SolverResult> {
        let aiger = parse_aag(text).expect("parses");
        let is_controllable: Vec<bool> =
            aiger.input_names.iter().map(|n| n.as_deref().is_some_and(is_controllable)).collect();
        let mut unroller = Unroller::new(text).expect("parses");
        let mut solver =
            crate::incremental::IncrementalSolver::new(crate::incdet::Options::default());
        solver.set_continuation(continuation);
        let mut verdicts = Vec::new();
        for t in 1..=k {
            unroller.step(&mut solver);
            let result = solver.solve();
            let expected = if clairvoyant_safe(&aiger, &is_controllable, t) {
                SolverResult::Satisfiable
            } else {
                SolverResult::Unsatisfiable
            };
            assert_eq!(result, expected, "depth {t} of:\n{text}");
            if result == SolverResult::Satisfiable {
                assert!(solver.verify(), "certificate at depth {t} of:\n{text}");
            }
            verdicts.push(result);
        }
        verdicts
    }

    #[cfg(feature = "probe")]
    static ALT_DEPTHS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    #[cfg(feature = "probe")]
    static ALT_DISAGREE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

    /// Solves the alternating unrolling of a spec at every depth up to
    /// `k` and checks each verdict against the reactive game oracle,
    /// which shares no code with the solver. Satisfiable results carry
    /// a composed strategy, verified against the instance.
    fn check_alternating(text: &str, k: u32) -> Vec<SolverResult> {
        let aiger = parse_aag(text).expect("parses");
        let is_controllable: Vec<bool> =
            aiger.input_names.iter().map(|n| n.as_deref().is_some_and(is_controllable)).collect();
        let unroller = Unroller::new(text).expect("parses");
        let mut verdicts = Vec::new();
        for t in 1..=k {
            let qcnf = unroller.alternating(t);
            let (result, strategy) = crate::alternation::solve_certified(
                &qcnf,
                crate::incdet::Options::default(),
                crate::alternation::EXPANSION_BUDGET,
            );
            let expected = if reactive_safe(&aiger, &is_controllable, t) {
                SolverResult::Satisfiable
            } else {
                SolverResult::Unsatisfiable
            };
            assert_eq!(result, expected, "depth {t} of:\n{text}");
            #[cfg(feature = "probe")]
            {
                use std::sync::atomic::Ordering::Relaxed;
                ALT_DEPTHS.fetch_add(1, Relaxed);
                if clairvoyant_safe(&aiger, &is_controllable, t)
                    != (expected == SolverResult::Satisfiable)
                {
                    ALT_DISAGREE.fetch_add(1, Relaxed);
                }
            }
            if result == SolverResult::Satisfiable {
                let strategy = strategy.expect("a satisfiable answer carries a strategy");
                assert!(
                    crate::alternation::verify_strategy(&qcnf, &strategy),
                    "strategy at depth {t} of:\n{text}"
                );
            }
            verdicts.push(result);
        }
        verdicts
    }

    #[test]
    fn alternating_latch_delay() {
        // the same specs as the flat unrolling, now with one alternation
        // per step: the reactive oracle and the solver must agree
        let text = "aag 2 1 1 1 0\n2\n4 2\n4\ni0 u\n";
        assert_eq!(
            check_alternating(text, 2),
            [SolverResult::Satisfiable, SolverResult::Unsatisfiable]
        );
    }

    #[test]
    fn alternating_copycat() {
        // c_t = u_t keeps the error false, and it is causal, so the
        // reactive prefix is satisfiable at every depth just like the
        // flat one
        let text = "aag 5 2 0 1 3\n2\n4\n10\n6 2 5\n8 3 4\n10 7 9\ni0 u\ni1 controllable_c\n";
        assert!(check_alternating(text, 4).iter().all(|&v| v == SolverResult::Satisfiable));
    }

    #[test]
    fn alternating_refuses_clairvoyance() {
        // The controller must announce the *next* input: latch0 stores
        // c, a "started" latch masks the first step, and the error is
        // `started AND (latch0 xor u)`. A reactive controller picks c_t
        // before seeing u_{t+1} and the environment answers it, so the
        // game is lost from depth 2; a clairvoyant one reads the whole
        // input sequence up front and simply copies it.
        let text = concat!(
            "aag 8 2 2 1 4\n",
            "2\n4\n",             // u, controllable_c
            "6 4 0\n",            // latch0 := c
            "8 1 0\n",            // started := true
            "16\n",               // error
            "10 6 3\n",           // latch0 AND not u
            "12 7 2\n",           // not latch0 AND u
            "14 11 13\n",         // NOR of the two, so 15 is the xor
            "16 8 15\n",          // started AND xor
            "i0 u\ni1 controllable_c\n"
        );
        let aiger = parse_aag(text).expect("parses");
        let is_controllable: Vec<bool> =
            aiger.input_names.iter().map(|n| n.as_deref().is_some_and(is_controllable)).collect();

        // the flat ∀∃ prefix lets the Skolem functions read the future
        for k in 1..=3 {
            assert!(clairvoyant_safe(&aiger, &is_controllable, k), "clairvoyant depth {k}");
        }
        // the alternating prefix does not, and the solver agrees with
        // the reactive oracle at every depth
        assert_eq!(
            check_alternating(text, 3),
            [
                SolverResult::Satisfiable,
                SolverResult::Unsatisfiable,
                SolverResult::Unsatisfiable
            ]
        );
    }

    #[test]
    fn unroller_latch_delay() {
        // error = latch, latch next = uncontrollable input: safe at depth
        // 1 (reset), lost at depth 2 (the environment raises the input)
        let text = "aag 2 1 1 1 0\n2\n4 2\n4\ni0 u\n";
        let verdicts = check_unrolling(text, 2, true);
        assert_eq!(verdicts, [SolverResult::Satisfiable, SolverResult::Unsatisfiable]);
    }

    #[test]
    fn unroller_reset_one() {
        // error = latch with reset 1: lost at depth 1 already
        let text = "aag 2 1 1 1 0\n2\n4 0 1\n4\ni0 u\n";
        assert_eq!(check_unrolling(text, 1, true), [SolverResult::Unsatisfiable]);
    }

    #[test]
    fn unroller_copycat() {
        // error = u xor c: the controller keeps it false forever by
        // copying; the SYNTCOMP "controllable_" prefix marks c
        let text = "aag 5 2 0 1 3\n2\n4\n10\n6 2 5\n8 3 4\n10 7 9\ni0 u\ni1 controllable_c\n";
        let verdicts = check_unrolling(text, 4, true);
        assert!(verdicts.iter().all(|&v| v == SolverResult::Satisfiable));
        // the copy strategy is forced (c_t = u_t) and reads only the
        // current step: causal, so the bounded answers certify the game
        let mut unroller = Unroller::new(text).expect("parses");
        let mut solver =
            crate::incremental::IncrementalSolver::new(crate::incdet::Options::default());
        for _ in 0..4 {
            unroller.step(&mut solver);
            assert_eq!(solver.solve(), SolverResult::Satisfiable);
        }
        let strategy = solver.skolem_model().expect("satisfiable").to_aiger(&|_| None);
        assert!(unroller.strategy_is_causal(&strategy).expect("strategy parses"));
    }

    #[test]
    fn unroller_clairvoyance_is_detected() {
        // the controller must *predict* the next step's universal input:
        // a latch carries c into the next step, where the error compares
        // it with the fresh u (guarded by a started latch so step one is
        // safe). Clairvoyantly winnable — c_t := u_{t+1} — but every
        // winning strategy must read a future input, so the causality
        // check rejects it.
        let text = "aag 8 2 2 1 4\n2\n4\n6 4\n8 1\n16\n10 6 3\n12 7 2\n14 11 13\n16 8 15\ni0 u\ni1 controllable_c\n";
        let verdicts = check_unrolling(text, 3, true);
        assert!(verdicts.iter().all(|&v| v == SolverResult::Satisfiable));
        let mut unroller = Unroller::new(text).expect("parses");
        let mut solver =
            crate::incremental::IncrementalSolver::new(crate::incdet::Options::default());
        for _ in 0..3 {
            unroller.step(&mut solver);
            assert_eq!(solver.solve(), SolverResult::Satisfiable);
        }
        let strategy = solver.skolem_model().expect("satisfiable").to_aiger(&|_| None);
        assert!(!unroller.strategy_is_causal(&strategy).expect("strategy parses"));
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(256))]
        #[test]
        fn differential_unrolling(
            universals in 0usize..=2,
            controllables in 0usize..=2,
            latches in proptest::collection::vec((0u64..1000, proptest::bool::ANY), 0..=2),
            gates in proptest::collection::vec((0u64..1000, 0u64..1000), 0..=6),
            output in 0u64..1000,
            k in 1u32..=3,
            continuation: bool,
        ) {
            let inputs = universals + controllables;
            let vars = inputs + latches.len() + gates.len();
            let mut text = format!("aag {vars} {inputs} {} 1 {}\n", latches.len(), gates.len());
            for i in 0..inputs {
                text.push_str(&format!("{}\n", 2 * (i + 1)));
            }
            // a literal over the given number of defined variables,
            // including the constants
            let pick = |seed: u64, defined: usize| seed % (2 * defined as u64 + 2);
            // latch next-state functions may read the whole circuit
            for (idx, &(next, reset)) in latches.iter().enumerate() {
                let lit = 2 * (inputs + idx + 1);
                text.push_str(&format!("{lit} {} {}\n", pick(next, vars), u64::from(reset)));
            }
            text.push_str(&format!("{}\n", pick(output, vars)));
            // gates read inputs, latches, and earlier gates
            for (idx, &(a, b)) in gates.iter().enumerate() {
                let lhs = 2 * (inputs + latches.len() + idx + 1) as u64;
                let defined = inputs + latches.len() + idx;
                text.push_str(&format!("{lhs} {} {}\n", pick(a, defined), pick(b, defined)));
            }
            for i in 0..inputs {
                let name = if i < universals { "u" } else { "controllable_c" };
                text.push_str(&format!("i{i} {name}{i}\n"));
            }
            check_unrolling(&text, k, continuation);
            // and the same spec as a *game* rather than an unrolling:
            // the refinement loop's whole winning region against the
            // explicit backward fixpoint, which answers realizability
            // outright instead of for a bound
            check_safety(&text);
            // the same spec through the reactive prefix, against the
            // reactive oracle: one alternation per step exercises the
            // alternation front-end on structured deep prefixes, which
            // the random-QCNF fuzz does not produce
            check_alternating(&text, k);
            #[cfg(feature = "probe")]
            {
                use std::sync::atomic::Ordering::Relaxed;
                eprintln!(
                    "alternating: {} depths, {} disagree with the clairvoyant encoding",
                    ALT_DEPTHS.load(Relaxed),
                    ALT_DISAGREE.load(Relaxed)
                );
            }
        }
    }

    #[test]
    fn qaiger_constant_output() {
        // output is the constant true, no inputs matter
        let input = "aag 1 1 0 1 0\n2\n1\ni0 1 x\n";
        assert_eq!(solve(input), SolverResult::Satisfiable);
        let input = "aag 1 1 0 1 0\n2\n0\ni0 1 x\n";
        assert_eq!(solve(input), SolverResult::Unsatisfiable);
    }
}
