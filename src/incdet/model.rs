//! Extraction of the piecewise Skolem model of a satisfiable result.
//!
//! The model mirrors the certificate structure (see
//! [`crate::incdet::certify`]): region `k` of the handled cases covers its
//! cube minus the cubes handled before it, and the final solver state
//! covers everything outside all cubes. Within a region, every assigned
//! existential variable carries the uniform function "assigned literal
//! holds iff one of its implication clauses fires"; the trail provides a
//! dependency order in which the functions can be evaluated (or emitted)
//! as a circuit over the universal variables.

use crate::{
    incdet::casesplit::{HandledCase, SnapshotFunction},
    incdet::IncDet,
    literal::{Lit, Var},
    QuantTy,
};
use std::collections::HashMap;
use std::fmt::Write;

/// The piecewise Skolem functions of a satisfiable result, detached from
/// the solver.
#[derive(Debug, Clone)]
pub struct SkolemModel {
    universals: Vec<Var>,
    regions: Vec<Region>,
    /// the functions of the final solver state, in dependency order
    final_chain: Vec<(Lit, Function)>,
}

#[derive(Debug, Clone)]
enum Region {
    /// constant response literals overriding the final chain on the cube
    Response { cube: Vec<Lit>, response: Vec<Lit> },
    /// a full snapshot chain, valid on the cube
    Closed { cube: Vec<Lit>, chain: Vec<(Lit, Function)> },
}

impl Region {
    fn cube(&self) -> &[Lit] {
        match self {
            Region::Response { cube, .. } | Region::Closed { cube, .. } => cube,
        }
    }
}

/// A region's rendered condition, its function names, and its response.
type RegionData<'a> = (String, HashMap<Var, String>, Option<&'a Vec<Lit>>);

#[derive(Debug, Clone)]
enum Function {
    /// the literal holds unconditionally
    Constant,
    /// the literal holds iff one of the implication clauses fires (all
    /// literals of the clause other than the defined one are false)
    Implications(Vec<Vec<Lit>>),
}

fn convert(chain: &[SnapshotFunction]) -> Vec<(Lit, Function)> {
    chain
        .iter()
        .map(|f| {
            let function = if f.constant {
                Function::Constant
            } else {
                Function::Implications(f.implications.clone())
            };
            (f.lit, function)
        })
        .collect()
}

impl IncDet {
    /// Extracts the piecewise Skolem model. Must only be called after
    /// [`IncDet::solve`] returned [`crate::SolverResult::Satisfiable`].
    #[must_use]
    pub fn skolem_model(&self) -> SkolemModel {
        let universals = self
            .prefix
            .iter()
            .filter(|scope| scope.quantifier == QuantTy::Forall)
            .flat_map(|scope| scope.variables.iter().copied())
            .collect();
        let regions = self
            .handled_cases
            .iter()
            .map(|case| match case {
                HandledCase::Response { cube, response } => {
                    Region::Response { cube: cube.clone(), response: response.clone() }
                }
                HandledCase::Closed { cube, functions } => {
                    Region::Closed { cube: cube.clone(), chain: convert(functions) }
                }
            })
            .collect();
        let final_chain = convert(&self.snapshot_functions());
        SkolemModel { universals, regions, final_chain }
    }
}

fn truth(lit: Lit, values: &HashMap<Var, bool>) -> bool {
    let value = values
        .get(&lit.var())
        .copied()
        .expect("every referenced variable is defined earlier in the chain");
    if lit.is_positive() {
        value
    } else {
        !value
    }
}

fn eval_chain(chain: &[(Lit, Function)], values: &mut HashMap<Var, bool>) {
    for (lit, function) in chain {
        let fires = match function {
            Function::Constant => true,
            Function::Implications(clauses) => clauses.iter().any(|clause| {
                clause.iter().filter(|l| l.var() != lit.var()).all(|&l| !truth(l, values))
            }),
        };
        values.insert(lit.var(), if lit.is_positive() { fires } else { !fires });
    }
}

impl SkolemModel {
    /// The universal variables (the parameters of the Skolem functions),
    /// in DIMACS numbering.
    #[must_use]
    pub fn universals(&self) -> Vec<i32> {
        self.universals.iter().map(|v| v.to_dimacs()).collect()
    }

    /// Every variable the model defines somewhere: the final chain plus
    /// variables only some region defines (a CEGAR response can cover a
    /// variable the final solver state leaves unassigned). Final-chain
    /// variables first, in chain order.
    pub(crate) fn defined_vars(&self) -> Vec<Var> {
        let mut vars: Vec<Var> = self.final_chain.iter().map(|(l, _)| l.var()).collect();
        let mut seen: std::collections::HashSet<Var> = vars.iter().copied().collect();
        for region in &self.regions {
            let extra: Box<dyn Iterator<Item = Var>> = match region {
                Region::Response { response, .. } => Box::new(response.iter().map(|l| l.var())),
                Region::Closed { chain, .. } => Box::new(chain.iter().map(|(l, _)| l.var())),
            };
            for var in extra {
                if seen.insert(var) {
                    vars.push(var);
                }
            }
        }
        vars
    }

    /// A rough node count of the encoded functions.
    pub(crate) fn size(&self) -> usize {
        let chain = |chain: &[(Lit, Function)]| {
            chain
                .iter()
                .map(|(_, f)| match f {
                    Function::Constant => 1,
                    Function::Implications(clauses) => {
                        clauses.iter().map(Vec::len).sum::<usize>() + 1
                    }
                })
                .sum::<usize>()
        };
        chain(&self.final_chain)
            + self
                .regions
                .iter()
                .map(|region| match region {
                    Region::Response { cube, response } => cube.len() + response.len(),
                    Region::Closed { cube, chain: c } => cube.len() + chain(c),
                })
                .sum::<usize>()
    }

    /// Evaluates the model at the given universal assignment (DIMACS
    /// literals; every universal variable must be covered). Returns the
    /// values of all existential variables the model defines.
    #[must_use]
    pub fn evaluate(&self, universal: &[i32]) -> HashMap<i32, bool> {
        let mut values: HashMap<Var, bool> =
            universal.iter().map(|&l| (Lit::from_dimacs(l).var(), l > 0)).collect();
        let mut final_values = values.clone();
        eval_chain(&self.final_chain, &mut final_values);

        for region in &self.regions {
            let cube_holds = region.cube().iter().all(|&l| truth(l, &final_values));
            if !cube_holds {
                continue;
            }
            match region {
                Region::Response { response, .. } => {
                    values = final_values;
                    for &l in response {
                        values.insert(l.var(), l.is_positive());
                    }
                }
                Region::Closed { chain, .. } => {
                    eval_chain(chain, &mut values);
                }
            }
            return finish(&self.universals, values);
        }
        finish(&self.universals, final_values)
    }

    /// Renders the model as SMT-LIB `define-fun`s over the universal
    /// variables. `name` maps DIMACS variables to their surface names;
    /// unnamed variables get internal names. Only named existential
    /// variables receive a public definition; everything else is emitted
    /// as internal helper functions.
    #[must_use]
    #[allow(clippy::too_many_lines, clippy::similar_names)]
    pub fn to_smtlib(&self, name: &dyn Fn(i32) -> Option<String>) -> String {
        let mut out = String::new();
        let params: Vec<(Var, String)> = self
            .universals
            .iter()
            .map(|&v| {
                let n = name(v.to_dimacs()).unwrap_or_else(|| format!("_u{}", v.to_dimacs()));
                (v, n)
            })
            .collect();
        let param_decl: String =
            params.iter().map(|(_, n)| format!("({n} Bool)")).collect::<Vec<_>>().join(" ");
        let param_args: String =
            params.iter().map(|(_, n)| n.clone()).collect::<Vec<_>>().join(" ");
        let call = |f: &str| {
            if params.is_empty() {
                f.to_string()
            } else {
                format!("({f} {param_args})")
            }
        };

        // one emitted helper chain per region plus the final chain
        let mut counter = 0usize;
        let mut emit_chain = |out: &mut String,
                              chain: &[(Lit, Function)],
                              params_known: &[(Var, String)]|
         -> HashMap<Var, String> {
            let mut refs: HashMap<Var, String> = HashMap::new();
            let reference = |refs: &HashMap<Var, String>, l: Lit| -> String {
                let base = params_known
                    .iter()
                    .find(|(v, _)| *v == l.var())
                    .map_or_else(|| call(&refs[&l.var()]), |(_, n)| n.clone());
                if l.is_positive() {
                    base
                } else {
                    format!("(not {base})")
                }
            };
            for (lit, function) in chain {
                let fires = match function {
                    Function::Constant => "true".to_string(),
                    Function::Implications(clauses) => {
                        let fire: Vec<String> = clauses
                            .iter()
                            .map(|clause| {
                                let others: Vec<String> = clause
                                    .iter()
                                    .filter(|l| l.var() != lit.var())
                                    .map(|&l| reference(&refs, !l))
                                    .collect();
                                match others.len() {
                                    0 => "true".to_string(),
                                    1 => others[0].clone(),
                                    _ => format!("(and {})", others.join(" ")),
                                }
                            })
                            .collect();
                        match fire.len() {
                            0 => "false".to_string(),
                            1 => fire[0].clone(),
                            _ => format!("(or {})", fire.join(" ")),
                        }
                    }
                };
                let body = if lit.is_positive() { fires } else { format!("(not {fires})") };
                let fname = format!("_f{counter}");
                counter += 1;
                let _ = writeln!(out, "  (define-fun {fname} ({param_decl}) Bool {body})");
                refs.insert(lit.var(), fname);
            }
            refs
        };

        let _ = writeln!(out, "(");
        let final_refs = emit_chain(&mut out, &self.final_chain, &params);
        // region conditions and per-region values
        let mut region_data: Vec<RegionData> = Vec::new();
        for region in &self.regions {
            let cond: Vec<String> = region
                .cube()
                .iter()
                .map(|&l| {
                    let base = params
                        .iter()
                        .find(|(v, _)| *v == l.var())
                        .map_or_else(|| call(&final_refs[&l.var()]), |(_, n)| n.clone());
                    if l.is_positive() {
                        base
                    } else {
                        format!("(not {base})")
                    }
                })
                .collect();
            let cond = match cond.len() {
                0 => "true".to_string(),
                1 => cond[0].clone(),
                _ => format!("(and {})", cond.join(" ")),
            };
            match region {
                Region::Response { response, .. } => {
                    region_data.push((cond, HashMap::new(), Some(response)));
                }
                Region::Closed { chain, .. } => {
                    let refs = emit_chain(&mut out, chain, &params);
                    region_data.push((cond, refs, None));
                }
            }
        }

        // public definitions for the named existentials: the final chain
        // plus region-only variables (their value outside the defining
        // regions is unconstrained, emitted as false)
        for var in self.defined_vars() {
            let base = final_refs.get(&var).map_or_else(|| "false".to_string(), |f| call(f));
            let Some(public) = name(var.to_dimacs()) else {
                continue;
            };
            let mut body = base.clone();
            for (cond, refs, response) in region_data.iter().rev() {
                let value = match response {
                    Some(response) => match response.iter().find(|l| l.var() == var) {
                        Some(l) if l.is_positive() => "true".to_string(),
                        Some(_) => "false".to_string(),
                        None => base.clone(),
                    },
                    None => refs.get(&var).map_or_else(|| base.clone(), |f| call(f)),
                };
                body = format!("(ite {cond} {value} {body})");
            }
            let _ = writeln!(out, "  (define-fun {public} ({param_decl}) Bool {body})");
        }
        let _ = writeln!(out, ")");
        out
    }

    /// Renders the model as a *strategy circuit* in ASCII AIGER format:
    /// the universal variables are the circuit inputs and every variable
    /// the model defines is an output computing its Skolem function —
    /// the externally checkable artifact of a satisfiable result (and
    /// the controller of a realizable safety game). `name` maps DIMACS
    /// variables to their surface names; unnamed variables are labeled
    /// with their DIMACS number. Variables the model does not define are
    /// unconstrained (any value satisfies the matrix on every region)
    /// and are not emitted.
    ///
    /// The region structure mirrors [`SkolemModel::evaluate`]: the first
    /// handled region whose cube holds (cubes may test frontier
    /// existentials, read from the final chain) provides the value —
    /// constant responses over the final chain, or a self-contained
    /// snapshot chain — and the final chain covers everything outside
    /// all cubes.
    #[must_use]
    pub fn to_aiger(&self, name: &dyn Fn(i32) -> Option<String>) -> String {
        let mut aig = AigBuilder::new(self.universals.len());
        let inputs: HashMap<Var, u64> =
            self.universals.iter().enumerate().map(|(i, &v)| (v, AigBuilder::input(i))).collect();
        let outputs = self.build_into(&mut aig, &inputs);
        render(&aig, &outputs, &self.universals, name)
    }

    /// Builds this model's functions into an existing AIG over the
    /// given input wires (one per universal variable it reads) and
    /// returns the output wire of every variable it defines. Shared by
    /// [`SkolemModel::to_aiger`] and by the composed strategies of the
    /// alternation front-end, so both use exactly the same encoding.
    pub(crate) fn build_into(
        &self,
        aig: &mut AigBuilder,
        inputs: &HashMap<Var, u64>,
    ) -> Vec<(Var, u64)> {
        let final_wires = build_chain(aig, &self.final_chain, inputs);

        // region selection: the first region whose cube holds wins
        let mut no_earlier = 1u64;
        let mut selected: Vec<u64> = Vec::new();
        let mut region_wires: Vec<Option<HashMap<Var, u64>>> = Vec::new();
        for region in &self.regions {
            let cube: Vec<u64> =
                region.cube().iter().map(|&l| wire(l, &final_wires, inputs)).collect();
            let holds = aig.and_all(&cube);
            selected.push(aig.and(no_earlier, holds));
            no_earlier = aig.and(no_earlier, holds ^ 1);
            region_wires.push(match region {
                Region::Response { .. } => None,
                Region::Closed { chain, .. } => Some(build_chain(aig, chain, inputs)),
            });
        }

        let mut outputs: Vec<(Var, u64)> = Vec::new();
        for var in self.defined_vars() {
            // a region-only variable is unconstrained outside the
            // regions that define it, emitted as constant false there
            let base = final_wires.get(&var).copied().unwrap_or(0);
            let mut terms = vec![aig.and(no_earlier, base)];
            for (region, (&select, wires)) in
                self.regions.iter().zip(selected.iter().zip(&region_wires))
            {
                let value = match region {
                    Region::Response { response, .. } => response
                        .iter()
                        .find(|l| l.var() == var)
                        .map_or(base, |l| u64::from(l.is_positive())),
                    Region::Closed { .. } => {
                        let wires = wires.as_ref().expect("closed regions have chains");
                        wires.get(&var).copied().unwrap_or(base)
                    }
                };
                terms.push(aig.and(select, value));
            }
            outputs.push((var, aig.or_all(&terms)));
        }
        outputs
    }
}

/// Renders an AIG with named outputs as ASCII AIGER.
pub(crate) fn render(
    aig: &AigBuilder,
    outputs: &[(Var, u64)],
    universals: &[Var],
    name: &dyn Fn(i32) -> Option<String>,
) -> String {
    let mut out = String::new();
    let max_var = aig.next_var - 1;
    let _ = writeln!(out, "aag {max_var} {} 0 {} {}", aig.inputs, outputs.len(), aig.ands.len());
    for position in 0..aig.inputs {
        let _ = writeln!(out, "{}", AigBuilder::input(position));
    }
    for (_, lit) in outputs {
        let _ = writeln!(out, "{lit}");
    }
    for (lhs, rhs0, rhs1) in &aig.ands {
        let _ = writeln!(out, "{lhs} {rhs0} {rhs1}");
    }
    let label = |v: Var| name(v.to_dimacs()).unwrap_or_else(|| v.to_dimacs().to_string());
    for (position, &v) in universals.iter().enumerate() {
        let _ = writeln!(out, "i{position} {}", label(v));
    }
    for (position, (v, _)) in outputs.iter().enumerate() {
        let _ = writeln!(out, "o{position} {}", label(*v));
    }
    out
}

fn finish(universals: &[Var], mut values: HashMap<Var, bool>) -> HashMap<i32, bool> {
    for u in universals {
        values.remove(u);
    }
    values.into_iter().map(|(v, b)| (v.to_dimacs(), b)).collect()
}

/// A tiny combinational AIG builder with constant folding; AIGER literal
/// conventions (`0` false, `1` true, variable `v` as literals `2v` and
/// `2v + 1`).
pub(crate) struct AigBuilder {
    inputs: usize,
    ands: Vec<(u64, u64, u64)>,
    next_var: u64,
}

impl AigBuilder {
    pub(crate) fn new(inputs: usize) -> Self {
        Self { inputs, ands: Vec::new(), next_var: inputs as u64 + 1 }
    }

    pub(crate) fn input(position: usize) -> u64 {
        2 * (position as u64 + 1)
    }

    /// The and-gates in definition order, as AIGER `(lhs, rhs0, rhs1)`
    /// triples: `lhs` is always a positive literal of a variable defined
    /// here for the first time, `rhs0` and `rhs1` refer to inputs,
    /// constants, or earlier gates.
    pub(crate) fn gates(&self) -> &[(u64, u64, u64)] {
        &self.ands
    }

    pub(crate) fn and(&mut self, a: u64, b: u64) -> u64 {
        if a == 0 || b == 0 || a == b ^ 1 {
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

    pub(crate) fn and_all(&mut self, lits: &[u64]) -> u64 {
        lits.iter().fold(1, |acc, &l| self.and(acc, l))
    }

    pub(crate) fn or_all(&mut self, lits: &[u64]) -> u64 {
        lits.iter().fold(0, |acc, &l| self.and(acc ^ 1, l ^ 1) ^ 1)
    }
}

/// The AIG literal of `lit` in a chain context: universal variables read
/// the circuit inputs, existential variables the wire of their function
/// (defined earlier in the chain).
fn wire(lit: Lit, wires: &HashMap<Var, u64>, inputs: &HashMap<Var, u64>) -> u64 {
    let base = inputs.get(&lit.var()).copied().unwrap_or_else(|| wires[&lit.var()]);
    if lit.is_positive() {
        base
    } else {
        base ^ 1
    }
}

/// Builds the wires of a function chain in dependency order and returns
/// the wire of every defined variable.
fn build_chain(
    aig: &mut AigBuilder,
    chain: &[(Lit, Function)],
    inputs: &HashMap<Var, u64>,
) -> HashMap<Var, u64> {
    let mut wires: HashMap<Var, u64> = HashMap::new();
    for (lit, function) in chain {
        let value = match function {
            Function::Constant => 1,
            Function::Implications(clauses) => {
                let firing: Vec<u64> = clauses
                    .iter()
                    .map(|clause| {
                        let others: Vec<u64> = clause
                            .iter()
                            .filter(|l| l.var() != lit.var())
                            .map(|&l| wire(!l, &wires, inputs))
                            .collect();
                        aig.and_all(&others)
                    })
                    .collect();
                aig.or_all(&firing)
            }
        };
        wires.insert(lit.var(), if lit.is_positive() { value } else { value ^ 1 });
    }
    wires
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        incdet::{IncDet, Options},
        qcnf::{strategy, QCNF},
        SolverResult,
    };
    use proptest::prelude::*;

    /// Simulates an ASCII AIGER strategy circuit on the given input
    /// values and returns the output values, independent of the emitter:
    /// gates are evaluated in file order (the emitter is topological).
    fn simulate(text: &str, inputs: &[bool]) -> Vec<bool> {
        let mut lines = text.lines();
        let header: Vec<u64> = lines
            .next()
            .unwrap()
            .split_ascii_whitespace()
            .skip(1)
            .map(|f| f.parse().unwrap())
            .collect();
        let (max_var, i, l, o, a) = (header[0], header[1], header[2], header[3], header[4]);
        assert_eq!(l, 0, "strategy circuits are combinational");
        assert_eq!(usize::try_from(i).unwrap(), inputs.len());
        let mut values = vec![false; usize::try_from(max_var).unwrap() + 1];
        for (pos, value) in inputs.iter().enumerate() {
            let line: u64 = lines.next().unwrap().parse().unwrap();
            assert_eq!(line, 2 * (pos as u64 + 1), "inputs are numbered consecutively");
            values[pos + 1] = *value;
        }
        let output_lits: Vec<u64> =
            (0..o).map(|_| lines.next().unwrap().parse().unwrap()).collect();
        let mut gates = Vec::new();
        for _ in 0..a {
            let lits: Vec<u64> = lines
                .next()
                .unwrap()
                .split_ascii_whitespace()
                .map(|f| f.parse().unwrap())
                .collect();
            gates.push((lits[0], lits[1], lits[2]));
        }
        let eval = |values: &[bool], lit: u64| -> bool {
            match lit {
                0 => false,
                1 => true,
                _ => values[usize::try_from(lit / 2).unwrap()] ^ (lit % 2 == 1),
            }
        };
        for (lhs, rhs0, rhs1) in gates {
            values[usize::try_from(lhs / 2).unwrap()] = eval(&values, rhs0) && eval(&values, rhs1);
        }
        output_lits.iter().map(|&lit| eval(&values, lit)).collect()
    }

    /// The output variables of an emitted strategy circuit, by output
    /// position (parsed from the symbol table, which labels unnamed
    /// variables with their DIMACS numbers).
    fn output_vars(text: &str) -> Vec<i32> {
        let mut vars = Vec::new();
        for line in text.lines() {
            if let Some(rest) = line.strip_prefix('o') {
                let (_, name) = rest.split_once(' ').unwrap();
                vars.push(name.parse().unwrap());
            }
        }
        vars
    }

    /// Emits the strategy circuit of a satisfiable result and checks it
    /// against the pointwise model evaluation (which the differential
    /// harness checks against the matrix) on every universal assignment.
    fn check_strategy_circuit(qcnf: &QCNF, options: Options) -> Result<(), TestCaseError> {
        let mut solver = IncDet::from_qcnf_with_options(qcnf, options);
        if solver.solve() != SolverResult::Satisfiable {
            return Ok(());
        }
        prop_assert!(solver.verify_skolem_functions());
        let model = solver.skolem_model();
        let text = model.to_aiger(&|_| None);
        let vars = output_vars(&text);
        let universals = model.universals();
        for point in 0..1u32 << universals.len() {
            let assignment: Vec<i32> = universals
                .iter()
                .enumerate()
                .map(|(i, &v)| if point >> i & 1 == 1 { v } else { -v })
                .collect();
            let expected = model.evaluate(&assignment);
            let inputs: Vec<bool> = (0..universals.len()).map(|i| point >> i & 1 == 1).collect();
            let outputs = simulate(&text, &inputs);
            let circuit: HashMap<i32, bool> = vars.iter().copied().zip(outputs).collect();
            // every variable the model defines at this point must be a
            // circuit output with the same value (the circuit may
            // additionally define region-only variables everywhere)
            for (&var, &value) in &expected {
                let out = circuit.get(&var);
                prop_assert_eq!(
                    out,
                    Some(&value),
                    "circuit disagrees with the model for variable {} at {:?} on:\n{}\n{}",
                    var,
                    &assignment,
                    qcnf,
                    &text
                );
            }
        }
        Ok(())
    }

    /// A CEGAR response can cover a variable the final solver state
    /// leaves unassigned; such region-only variables must still become
    /// circuit outputs (this instance made the emitters drop variable 2).
    #[test]
    fn region_only_variables_are_emitted() {
        use crate::QuantTy;
        let qcnf = QCNF::new(
            &[(QuantTy::Forall, &[3][..]), (QuantTy::Exists, &[1, 2][..])],
            &[&[-2, -1][..], &[2, 3][..], &[2, 1][..]],
        );
        check_strategy_circuit(&qcnf, Options::default()).unwrap();
        let mut solver = IncDet::from_qcnf(&qcnf);
        assert_eq!(solver.solve(), SolverResult::Satisfiable);
        let text = solver.skolem_model().to_aiger(&|_| None);
        assert!(output_vars(&text).contains(&2), "variable 2 is missing from:\n{text}");
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]
        /// Random 2QBF instances, solved with default options and with
        /// aggressive case splitting (so the emitted circuit exercises
        /// the region selection), the circuit simulated on every
        /// universal point against the model evaluation.
        #[test]
        fn strategy_circuit_matches_model(qcnf in strategy::qcnf(2..=2, 2..=8, 4..=24, 2..=6)) {
            check_strategy_circuit(&qcnf, Options::default())?;
            let aggressive = Options { case_split_threshold: 2, ..Options::default() };
            check_strategy_circuit(&qcnf, aggressive)?;
        }
    }
}
