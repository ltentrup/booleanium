//! QCIR input: prenex QCIR-G14 circuits.
//!
//! Like the QAIGER path, this is a definition-level input: gates arrive
//! as definitions and become existential variables with their two-sided
//! Tseitin clauses, so incremental determinization recovers all of them
//! in the initial propagation. Beyond AIGER's AND gates, QCIR offers
//! `and`, `or`, `xor`, and `ite` with arbitrary arity where applicable.
//!
//! Supported shape: *prenex* circuits (quantifier blocks up front, no
//! quantifiers inside gates) whose prefix collapses to at most two
//! blocks before the gates — ∀∃, a single block, or ∃∀. An ∃∀ prefix is
//! solved by *negation*: gate definitions are self-dual, so flipping the
//! quantifiers and negating the output yields the ∀∃ dual whose verdict
//! is inverted ([`Qcir::negated`]). Identifiers may be QCIR "cleansed"
//! integers or arbitrary names; both are interned, and
//! [`Qcir::name_of`] maps solver variables back to their surface names
//! (for strategy output).

use crate::{qcnf::QCNF, QuantTy};
use std::collections::HashMap;
use std::fmt;

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
    pub line: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "qcir parse error in line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for ParseError {}

/// A parsed prenex QCIR instance, converted to clauses.
#[derive(Debug)]
pub struct Qcir {
    pub qcnf: QCNF,
    /// whether the instance was negated to reach the ∀∃ shape: the
    /// solver's verdict must be inverted, and satisfiability artifacts
    /// (models, strategies) describe the negation
    pub negated: bool,
    /// interned surface names, by variable id (1-based)
    names: Vec<String>,
}

impl Qcir {
    /// The surface name of a solver variable (DIMACS numbering), if the
    /// variable came from the input (gates and inputs both have names).
    #[must_use]
    pub fn name_of(&self, var: i32) -> Option<String> {
        usize::try_from(var)
            .ok()
            .and_then(|v| v.checked_sub(1))
            .and_then(|v| self.names.get(v))
            .cloned()
    }
}

fn err(line: usize, message: impl Into<String>) -> ParseError {
    ParseError { message: message.into(), line }
}

/// Interns identifiers to 1-based variable ids.
#[derive(Default)]
struct Interner {
    ids: HashMap<String, u32>,
    names: Vec<String>,
}

impl Interner {
    fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.ids.get(name) {
            return id;
        }
        let id = u32::try_from(self.names.len()).expect("variable count fits a u32") + 1;
        self.ids.insert(name.to_string(), id);
        self.names.push(name.to_string());
        id
    }
}

/// A literal token: an optionally negated identifier.
fn parse_lit(token: &str, line: usize, interner: &mut Interner) -> Result<i32, ParseError> {
    let (negated, name) = match token.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, token),
    };
    if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return Err(err(line, format!("invalid identifier {token}")));
    }
    let id = i32::try_from(interner.intern(name)).expect("variable id fits an i32");
    Ok(if negated { -id } else { id })
}

/// The comma-separated arguments inside `head(...)`.
fn arguments(text: &str) -> Vec<&str> {
    let inner = text.trim();
    if inner.is_empty() {
        return Vec::new();
    }
    inner.split(',').map(str::trim).collect()
}

/// Parses a prenex QCIR-G14 instance and converts it into clauses.
///
/// # Errors
///
/// Returns an error for malformed input, non-prenex quantifiers, and
/// prefixes that do not collapse to a supported 2QBF shape.
#[allow(clippy::too_many_lines)]
pub fn parse_qcir(input: &str) -> Result<Qcir, ParseError> {
    let mut interner = Interner::default();
    // quantifier blocks in order; adjacent same-quantifier blocks merge
    let mut prefix: Vec<(QuantTy, Vec<u32>)> = Vec::new();
    let mut output: Option<i32> = None;
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut gate_vars: Vec<u32> = Vec::new();
    let mut defined: std::collections::HashSet<u32> = std::collections::HashSet::new();

    let declare =
        |prefix: &mut Vec<(QuantTy, Vec<u32>)>, quant: QuantTy, vars: Vec<u32>| match prefix
            .last_mut()
        {
            Some((q, block)) if *q == quant => block.extend(vars),
            _ => prefix.push((quant, vars)),
        };

    for (no, raw) in input.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let line = line.strip_suffix(';').unwrap_or(line);
        let Some(open) = line.find('(') else {
            return Err(err(no + 1, "expected a declaration or gate definition"));
        };
        // gate definitions have the shape `name = op(args)`
        if let Some((name, definition)) = line.split_once('=') {
            if output.is_none() {
                return Err(err(no + 1, "gate definitions must follow the output declaration"));
            }
            let name = name.trim();
            let gate = parse_lit(name, no + 1, &mut interner)?;
            let gate =
                u32::try_from(gate).map_err(|_| err(no + 1, "a gate name must not be negated"))?;
            if !defined.insert(gate) {
                return Err(err(no + 1, format!("gate {name} is defined twice")));
            }
            let definition = definition.trim();
            let Some(open) = definition.find('(') else {
                return Err(err(no + 1, "expected a gate definition"));
            };
            let Some(inner) = definition[open + 1..].strip_suffix(')') else {
                return Err(err(no + 1, "expected a closing parenthesis"));
            };
            let op = definition[..open].trim();
            if op == "exists" || op == "forall" {
                return Err(err(no + 1, "only prenex instances are supported"));
            }
            let mut args = Vec::new();
            for token in arguments(inner) {
                args.push(parse_lit(token, no + 1, &mut interner)?);
            }
            let g = i32::try_from(gate).expect("id fits an i32");
            match op {
                "and" => {
                    let mut long: Vec<i32> = vec![g];
                    for &a in &args {
                        matrix.push(vec![-g, a]);
                        long.push(-a);
                    }
                    matrix.push(long);
                }
                "or" => {
                    let mut long: Vec<i32> = vec![-g];
                    for &a in &args {
                        matrix.push(vec![g, -a]);
                        long.push(a);
                    }
                    matrix.push(long);
                }
                "xor" => {
                    let [a, b] = args[..] else {
                        return Err(err(no + 1, "xor takes exactly two arguments"));
                    };
                    matrix.push(vec![-g, a, b]);
                    matrix.push(vec![-g, -a, -b]);
                    matrix.push(vec![g, -a, b]);
                    matrix.push(vec![g, a, -b]);
                }
                "ite" => {
                    let [c, t, e] = args[..] else {
                        return Err(err(no + 1, "ite takes exactly three arguments"));
                    };
                    matrix.push(vec![-g, -c, t]);
                    matrix.push(vec![-g, c, e]);
                    matrix.push(vec![g, -c, -t]);
                    matrix.push(vec![g, c, -e]);
                }
                _ => return Err(err(no + 1, format!("unsupported gate operation {op}"))),
            }
            gate_vars.push(gate);
            continue;
        }
        let Some(inner) = line[open + 1..].strip_suffix(')') else {
            return Err(err(no + 1, "expected a closing parenthesis"));
        };
        let head = line[..open].trim();
        match head {
            "free" | "exists" | "forall" => {
                if output.is_some() {
                    return Err(err(no + 1, "quantifier blocks must precede the output"));
                }
                let quant = if head == "forall" { QuantTy::Forall } else { QuantTy::Exists };
                let mut vars = Vec::new();
                for token in arguments(inner) {
                    let lit = parse_lit(token, no + 1, &mut interner)?;
                    let var = u32::try_from(lit)
                        .map_err(|_| err(no + 1, "declared variables must not be negated"))?;
                    vars.push(var);
                }
                declare(&mut prefix, quant, vars);
            }
            "output" => {
                if output.is_some() {
                    return Err(err(no + 1, "duplicate output declaration"));
                }
                let tokens = arguments(inner);
                let [token] = tokens[..] else {
                    return Err(err(no + 1, "output takes exactly one literal"));
                };
                output = Some(parse_lit(token, no + 1, &mut interner)?);
            }
            _ => return Err(err(no + 1, format!("unsupported declaration {head}"))),
        }
    }
    let Some(output) = output else {
        return Err(err(input.lines().count(), "missing output declaration"));
    };

    // undeclared identifiers (free variables) join the outermost
    // existential block, matching the QDIMACS convention
    let declared: std::collections::HashSet<u32> = prefix
        .iter()
        .flat_map(|(_, vars)| vars.iter().copied())
        .chain(gate_vars.iter().copied())
        .collect();
    let free: Vec<u32> = (1..=u32::try_from(interner.names.len()).expect("fits"))
        .filter(|v| !declared.contains(v))
        .collect();
    if !free.is_empty() {
        match prefix.first_mut() {
            Some((QuantTy::Exists, block)) => {
                block.splice(0..0, free.iter().copied());
            }
            _ => prefix.insert(0, (QuantTy::Exists, free)),
        }
    }

    // decide the solve shape: gates are innermost existentials, so the
    // prefix must end existentially (or be flipped by negation)
    let negated = match prefix.last() {
        Some((QuantTy::Forall, _)) if prefix.len() > 1 => {
            // ∃∀ (or deeper): negate; only ∃∀ collapses to two blocks
            if prefix.len() > 2 {
                return Err(err(input.lines().count(), "only 2QBF prefixes are supported"));
            }
            for (quant, _) in &mut prefix {
                *quant = match quant {
                    QuantTy::Exists => QuantTy::Forall,
                    QuantTy::Forall => QuantTy::Exists,
                };
            }
            true
        }
        _ => {
            if prefix.len() > 2 {
                return Err(err(input.lines().count(), "only 2QBF prefixes are supported"));
            }
            false
        }
    };
    match prefix.last_mut() {
        Some((QuantTy::Exists, block)) => block.extend(gate_vars),
        _ => prefix.push((QuantTy::Exists, gate_vars)),
    }
    matrix.push(vec![if negated { -output } else { output }]);

    let prefix_refs: Vec<(QuantTy, &[u32])> =
        prefix.iter().map(|(q, vars)| (*q, vars.as_slice())).collect();
    let matrix_refs: Vec<&[i32]> = matrix.iter().map(Vec::as_slice).collect();
    let qcnf = QCNF::new(&prefix_refs, &matrix_refs);
    Ok(Qcir { qcnf, negated, names: interner.names })
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{incdet::IncDet, SolverResult};

    /// Solves a QCIR instance and returns the *instance* verdict
    /// (inverting the solver verdict for negated instances), certifying
    /// native satisfiable results.
    fn solve(input: &str) -> SolverResult {
        let qcir = parse_qcir(input).expect("parses");
        let mut solver =
            IncDet::from_qcnf_with_options(&qcir.qcnf, crate::incdet::Options::default());
        let result = solver.solve();
        assert_eq!(result, qcir.qcnf.brute_force(), "solver disagrees with oracle on:\n{input}");
        if result == SolverResult::Satisfiable {
            assert!(solver.verify_skolem_functions());
        }
        match (result, qcir.negated) {
            (SolverResult::Satisfiable, true) => SolverResult::Unsatisfiable,
            (SolverResult::Unsatisfiable, true) => SolverResult::Satisfiable,
            (verdict, _) => verdict,
        }
    }

    #[test]
    fn named_forall_exists() {
        // forall x exists y: x <-> y
        let input = "#QCIR-G14\nforall(x)\nexists(y)\noutput(g)\ng = and(a, b)\na = or(-x, y)\nb = or(x, -y)\n";
        assert_eq!(solve(input), SolverResult::Satisfiable);
        // forall x exists y: x /\ y is falsified by x = 0
        let input = "#QCIR-G14\nforall(x)\nexists(y)\noutput(g)\ng = and(x, y)\n";
        assert_eq!(solve(input), SolverResult::Unsatisfiable);
    }

    #[test]
    fn cleansed_gates() {
        // xor and ite over cleansed identifiers
        let input = "#QCIR-G14\nforall(1)\nexists(2)\noutput(3)\n3 = xor(1, 2)\n";
        assert_eq!(solve(input), SolverResult::Satisfiable);
        let input = "#QCIR-G14\nforall(1, 2)\nexists(3)\noutput(4)\n4 = ite(1, 3, -3)\n";
        assert_eq!(solve(input), SolverResult::Satisfiable);
    }

    #[test]
    fn exists_forall_by_negation() {
        // exists y forall x: x \/ y — realizable with y = 1
        let input = "#QCIR-G14\nexists(y)\nforall(x)\noutput(g)\ng = or(x, y)\n";
        let qcir = parse_qcir(input).expect("parses");
        assert!(qcir.negated);
        assert_eq!(solve(input), SolverResult::Satisfiable);
        // exists y forall x: x <-> y — no constant y works
        let input = "#QCIR-G14\nexists(y)\nforall(x)\noutput(g)\ng = and(a, b)\na = or(-x, y)\nb = or(x, -y)\n";
        assert_eq!(solve(input), SolverResult::Unsatisfiable);
    }

    #[test]
    fn shape_errors() {
        // three genuine blocks
        let input = "#QCIR-G14\nexists(a)\nforall(x)\nexists(b)\noutput(g)\ng = and(a, b, x)\n";
        assert!(parse_qcir(input).is_err());
        // non-prenex quantifier gate
        let input = "#QCIR-G14\nforall(x)\noutput(g)\ng = exists(y; x)\n";
        assert!(parse_qcir(input).is_err());
    }

    /// Direct circuit evaluation, independent of the Tseitin conversion:
    /// gate values by operation over the input assignment.
    #[derive(Clone, Copy)]
    enum Op {
        And,
        Or,
        Xor,
        Ite,
    }

    struct Gate {
        op: Op,
        args: Vec<i32>,
    }

    fn eval(values: &[bool], lit: i32) -> bool {
        values[usize::try_from(lit.abs()).unwrap()] == (lit > 0)
    }

    /// The clairvoyant ∀∃ oracle on the circuit itself: for every
    /// universal assignment there must be an existential assignment
    /// making the output true (gates evaluated functionally).
    fn circuit_oracle(
        universals: usize,
        existentials: usize,
        gates: &[Gate],
        output: i32,
    ) -> SolverResult {
        let total = universals + existentials + gates.len();
        let winnable = (0..1u32 << universals).all(|u| {
            (0..1u32 << existentials).any(|e| {
                let mut values = vec![false; total + 1];
                for i in 0..universals {
                    values[i + 1] = u >> i & 1 == 1;
                }
                for i in 0..existentials {
                    values[universals + i + 1] = e >> i & 1 == 1;
                }
                for (idx, gate) in gates.iter().enumerate() {
                    let var = universals + existentials + idx + 1;
                    values[var] = match gate.op {
                        Op::And => gate.args.iter().all(|&a| eval(&values, a)),
                        Op::Or => gate.args.iter().any(|&a| eval(&values, a)),
                        Op::Xor => eval(&values, gate.args[0]) != eval(&values, gate.args[1]),
                        Op::Ite => {
                            if eval(&values, gate.args[0]) {
                                eval(&values, gate.args[1])
                            } else {
                                eval(&values, gate.args[2])
                            }
                        }
                    };
                }
                eval(&values, output)
            })
        });
        if winnable {
            SolverResult::Satisfiable
        } else {
            SolverResult::Unsatisfiable
        }
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(256))]
        /// Random prenex circuits in both quantifier orders, checked
        /// against direct circuit evaluation.
        #[test]
        fn differential_qcir(
            universals in 1usize..=4,
            existentials in 0usize..=4,
            specs in proptest::collection::vec((0u8..4, 0u64..10000, 0u64..10000, 0u64..10000), 0..=10),
            output in 0u64..10000,
            flipped: bool,
        ) {
            let inputs = universals + existentials;
            // a literal over the identifiers defined so far
            let pick = |seed: u64, defined: usize| {
                let raw = i32::try_from(seed % (2 * defined as u64)).unwrap();
                let var = raw / 2 + 1;
                if raw % 2 == 0 { var } else { -var }
            };
            let mut gates = Vec::new();
            for (idx, &(op, a, b, c)) in specs.iter().enumerate() {
                let defined = inputs + idx;
                let (op, args) = match op {
                    0 => (Op::And, vec![pick(a, defined), pick(b, defined)]),
                    1 => (Op::Or, vec![pick(a, defined), pick(b, defined)]),
                    2 => (Op::Xor, vec![pick(a, defined), pick(b, defined)]),
                    _ => (Op::Ite, vec![pick(a, defined), pick(b, defined), pick(c, defined)]),
                };
                gates.push(Gate { op, args });
            }
            let output = pick(output, inputs + gates.len());

            // render the instance; flipped swaps the quantifier order
            // (the existential-then-universal shape solved by negation)
            let mut text = String::from("#QCIR-G14\n");
            let block = |quant: &str, from: usize, count: usize| {
                let vars: Vec<String> = (from..from + count).map(|v| format!("{}", v + 1)).collect();
                if vars.is_empty() { String::new() } else { format!("{quant}({})\n", vars.join(", ")) }
            };
            // flipped declares the first group existential and the second
            // universal: the exists-forall shape solved by negation
            let (first, second) = if flipped { ("exists", "forall") } else { ("forall", "exists") };
            text.push_str(&block(first, 0, universals));
            text.push_str(&block(second, universals, existentials));
            text.push_str(&format!("output({output})\n"));
            for (idx, gate) in gates.iter().enumerate() {
                let name = inputs + idx + 1;
                let op = match gate.op { Op::And => "and", Op::Or => "or", Op::Xor => "xor", Op::Ite => "ite" };
                let args: Vec<String> = gate.args.iter().map(ToString::to_string).collect();
                text.push_str(&format!("{name} = {op}({})\n", args.join(", ")));
            }

            let expected = if flipped {
                // exists-forall truth: some assignment of the outer
                // (first-declared) variables works for all inner ones
                let outer_wins = (0..1u32 << universals).any(|u| {
                    (0..1u32 << existentials).all(|e| {
                        let total = inputs + gates.len();
                        let mut values = vec![false; total + 1];
                        for i in 0..universals {
                            values[i + 1] = u >> i & 1 == 1;
                        }
                        for i in 0..existentials {
                            values[universals + i + 1] = e >> i & 1 == 1;
                        }
                        for (idx, gate) in gates.iter().enumerate() {
                            let var = inputs + idx + 1;
                            values[var] = match gate.op {
                                Op::And => gate.args.iter().all(|&a| eval(&values, a)),
                                Op::Or => gate.args.iter().any(|&a| eval(&values, a)),
                                Op::Xor => eval(&values, gate.args[0]) != eval(&values, gate.args[1]),
                                Op::Ite => {
                                    if eval(&values, gate.args[0]) {
                                        eval(&values, gate.args[1])
                                    } else {
                                        eval(&values, gate.args[2])
                                    }
                                }
                            };
                        }
                        eval(&values, output)
                    })
                });
                if outer_wins { SolverResult::Satisfiable } else { SolverResult::Unsatisfiable }
            } else {
                circuit_oracle(universals, existentials, &gates, output)
            };
            proptest::prop_assert_eq!(solve(&text), expected, "instance:\n{}", &text);
        }
    }
}
