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

        // public definitions for the named existentials, in chain order
        for (lit, _) in &self.final_chain {
            let var = lit.var();
            let fname = &final_refs[&var];
            let Some(public) = name(var.to_dimacs()) else {
                continue;
            };
            let mut body = call(fname);
            for (cond, refs, response) in region_data.iter().rev() {
                let value = match response {
                    Some(response) => match response.iter().find(|l| l.var() == var) {
                        Some(l) if l.is_positive() => "true".to_string(),
                        Some(_) => "false".to_string(),
                        None => call(fname),
                    },
                    None => refs.get(&var).map_or_else(|| call(fname), |f| call(f)),
                };
                body = format!("(ite {cond} {value} {body})");
            }
            let _ = writeln!(out, "  (define-fun {public} ({param_decl}) Bool {body})");
        }
        let _ = writeln!(out, ")");
        out
    }
}

fn finish(universals: &[Var], mut values: HashMap<Var, bool>) -> HashMap<i32, bool> {
    for u in universals {
        values.remove(u);
    }
    values.into_iter().map(|(v, b)| (v.to_dimacs(), b)).collect()
}
