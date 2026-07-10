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

use crate::{qcnf::QCNF, QuantTy};
use std::fmt;

/// Prefix of input symbol names that marks controllable (existential)
/// inputs.
const CONTROLLABLE_PREFIX: &str = "2 ";

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

/// An ASCII AIGER (`aag`) file, read far enough for QAIGER purposes.
struct Aiger {
    max_var: u64,
    inputs: Vec<u64>,
    latches: Vec<u64>,
    outputs: Vec<u64>,
    ands: Vec<And>,
    /// symbol names of the inputs, by input position
    input_names: Vec<Option<String>>,
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
            // the next-state (and optional reset) literals are irrelevant
            // for the combinational QAIGER interpretation
            [lit, ..] if lit % 2 == 0 && lit >= 2 => latches.push(lit),
            _ => return Err(err(no + 1, "a latch must start with a positive literal")),
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

    // symbol table: only input names are relevant (controllability)
    let mut input_names = vec![None; inputs.len()];
    for (_, line) in lines {
        if line.starts_with('c') {
            break;
        }
        if let Some(rest) = line.strip_prefix('i') {
            if let Some((pos, name)) = rest.split_once(' ') {
                if let Ok(pos) = pos.parse::<usize>() {
                    if pos < input_names.len() {
                        input_names[pos] = Some(name.to_string());
                    }
                }
            }
        }
    }

    Ok(Aiger { max_var, inputs, latches, outputs, ands, input_names })
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
        let controllable = aiger.input_names[pos]
            .as_deref()
            .is_some_and(|name| name.starts_with(CONTROLLABLE_PREFIX));
        let var = u32::try_from(input / 2).expect("variable fits a u32");
        if controllable {
            existentials.push(var);
        } else {
            universals.push(var);
        }
    }
    for &latch in &aiger.latches {
        universals.push(u32::try_from(latch / 2).expect("variable fits a u32"));
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
                text.push_str(&format!("i{} {} v{}\n", i, quant, i));
            }
            solve(&text);
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
