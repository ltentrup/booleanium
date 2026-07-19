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

use crate::{incremental::IncrementalSolver, qcnf::QCNF, QuantTy};
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
    fn litval(val: &[bool], l: u64) -> bool {
        match l {
            0 => false,
            1 => true,
            _ => val[usize::try_from(l / 2).unwrap()] ^ (l % 2 == 1),
        }
    }

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
