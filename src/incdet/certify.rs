//! Verification of the Skolem functions of a satisfiable result.
//!
//! Every assigned existential variable carries the same function shape: it
//! takes the assigned polarity if and only if one of the implication clauses
//! of that polarity fires (all other literals false), and the opposite
//! polarity otherwise. This holds uniformly for propagated variables (where
//! determinacy makes the two polarities complementary) and for decided
//! variables (where the assigned polarity is the non-default one).
//!
//! The premises of an implication clause are universal variables or
//! existential variables assigned earlier, so the trail provides a
//! topological order in which the functions can be encoded as a circuit
//! over the universal variables.
//!
//! The overall strategy is piecewise over the handled cases: region `k` of
//! [`IncDet::handled_cases`] covers its cube minus the cubes handled before
//! it, and the functions of the final solver state cover everything outside
//! all handled cubes. CEGAR responses are constants and are checked
//! syntactically; closed case splits and the final state are checked by
//! refuting the existence of a universal assignment inside the region that
//! falsifies an original matrix clause under the region's functions.

use crate::{
    incdet::casesplit::{HandledCase, SnapshotFunction},
    incdet::IncDet,
    literal::Lit,
    sat::{varisat::Varisat, LookupSolver, SatSolver},
};
use tracing::debug;

impl IncDet {
    /// Checks the piecewise Skolem functions extracted from a satisfiable
    /// solver state against the matrix. Returns `true` if the certificate
    /// is valid. Must only be called after [`IncDet::solve`] returned
    /// [`crate::SolverResult::Satisfiable`].
    #[must_use]
    pub fn verify_skolem_functions(&self) -> bool {
        for (region, case) in self.handled_cases.iter().enumerate() {
            let valid = match case {
                HandledCase::Response { cube, response } => {
                    // the response constants cover the variables that were
                    // not root-level assigned when the case was recorded;
                    // the (permanent) root-level functions cover the rest,
                    // and the cube constrains their outputs (frontier
                    // literals)
                    let exclude: std::collections::HashSet<crate::literal::Var> =
                        response.iter().map(|l| l.var()).collect();
                    let mut functions = self.snapshot_root_functions(&exclude);
                    functions.extend(response.iter().map(|&lit| SnapshotFunction {
                        lit,
                        constant: true,
                        implications: vec![],
                    }));
                    self.verify_region(&functions, cube, region)
                }
                HandledCase::Closed { cube, functions } => {
                    self.verify_region(functions, cube, region)
                }
            };
            if !valid {
                debug!("verification of handled case {region} failed");
                return false;
            }
        }
        // the final solver state covers everything outside the handled cubes
        let functions = self.snapshot_functions();
        self.verify_region(&functions, &[], self.handled_cases.len())
    }

    /// Checks a handled case against the given clauses (instead of the
    /// full matrix): used by monotone extension to re-verify retained
    /// regions against exactly the added clauses. Variables without a
    /// function in the region are unconstrained in the check, i.e.
    /// treated adversarially, so a pass is robust against whatever
    /// functions the continued search assigns them later.
    pub(crate) fn case_valid_for(&self, region: usize, clauses: &[Vec<Lit>]) -> bool {
        let case = &self.handled_cases[region];
        let functions = match case {
            HandledCase::Response { cube: _, response } => {
                let exclude: std::collections::HashSet<crate::literal::Var> =
                    response.iter().map(|l| l.var()).collect();
                let mut functions = self.snapshot_root_functions(&exclude);
                functions.extend(response.iter().map(|&lit| SnapshotFunction {
                    lit,
                    constant: true,
                    implications: vec![],
                }));
                functions
            }
            HandledCase::Closed { cube: _, functions } => {
                let mut copied = Vec::new();
                for f in functions {
                    copied.push(SnapshotFunction {
                        lit: f.lit,
                        constant: f.constant,
                        implications: f.implications.clone(),
                    });
                }
                copied
            }
        };
        self.region_counterexample(&functions, case.cube(), region, clauses).is_none()
    }

    /// Searches for a universal assignment that extends `cube`, avoids the
    /// cubes of the regions handled before `region`, and falsifies one of
    /// `clauses` under `functions`. Returns the universal part of the
    /// counterexample.
    pub(crate) fn region_counterexample(
        &self,
        functions: &[SnapshotFunction],
        cube: &[Lit],
        region: usize,
        clauses: &[Vec<Lit>],
    ) -> Option<Vec<Lit>> {
        let mut solver = LookupSolver::<Varisat>::default();
        solver.set_var_count(self.vars.get_var_count());

        for &lit in cube {
            let unit = solver.lookup(lit);
            solver.add_clause(&[unit]);
        }
        for case in self.handled_cases.iter().take(region) {
            let excluded: Vec<_> = case.cube().iter().map(|&l| solver.lookup(!l)).collect();
            solver.add_clause(&excluded);
        }
        encode_functions(&mut solver, functions);

        // ask for a universal assignment that falsifies one of the clauses
        let mut some_falsified = Vec::new();
        for clause in clauses {
            let falsified = solver.add_variable();
            for &l in clause {
                let negated = solver.lookup(!l);
                solver.add_clause(&[!falsified, negated]);
            }
            some_falsified.push(falsified);
        }
        solver.add_clause(&some_falsified);

        if !solver.solve().unwrap() {
            return None;
        }
        let model = solver.orig_model().expect("model after sat");
        Some(
            model
                .into_iter()
                .filter(|l| {
                    let data = &self.vars[l.var()];
                    data.scope.is_some() && data.is_universal(&self.prefix)
                })
                .collect(),
        )
    }

    /// Refutes the existence of a universal assignment that extends `cube`,
    /// avoids the cubes of the regions handled before `region`, and
    /// falsifies an original matrix clause under `functions`.
    fn verify_region(&self, functions: &[SnapshotFunction], cube: &[Lit], region: usize) -> bool {
        let mut solver = LookupSolver::<Varisat>::default();
        solver.set_var_count(self.vars.get_var_count());

        for &lit in cube {
            let unit = solver.lookup(lit);
            solver.add_clause(&[unit]);
        }
        for case in self.handled_cases.iter().take(region) {
            let excluded: Vec<_> = case.cube().iter().map(|&l| solver.lookup(!l)).collect();
            solver.add_clause(&excluded);
        }
        encode_functions(&mut solver, functions);

        // ask for a universal assignment that falsifies an original clause
        let mut some_falsified = Vec::new();
        for &cid in &self.originals {
            let clause = &self.allocator[cid];
            let falsified = solver.add_variable();
            for &l in clause.iter() {
                let negated = solver.lookup(!l);
                solver.add_clause(&[!falsified, negated]);
            }
            some_falsified.push(falsified);
        }
        solver.add_clause(&some_falsified);

        let counterexample = solver.solve().unwrap();
        if counterexample {
            debug!("Skolem function verification failed for region {region}");
            if let Some(model) = solver.orig_model() {
                let assignment: std::collections::HashSet<Lit> = model.into_iter().collect();
                for &cid in &self.originals {
                    let clause = &self.allocator[cid];
                    if clause.iter().all(|l| assignment.contains(&!*l)) {
                        debug!("falsified original clause: {clause}");
                        for &l in clause.iter() {
                            let covered = functions.iter().find(|f| f.lit.var() == l.var());
                            debug!(
                                "  var {} dec_lvl={:?} function={:?}",
                                l.var(),
                                self.dec_lvls[l.var()],
                                covered.map(|f| (f.lit, f.constant, f.implications.len()))
                            );
                        }
                    }
                }
                let lits: Vec<String> = assignment.iter().map(ToString::to_string).collect();
                debug!("counterexample assignment: {}", lits.join(" "));
            }
        }
        !counterexample
    }
}

/// Encodes the piecewise functions in trail order: the assigned literal
/// holds iff one of its implication clauses fires (or always, for
/// constants).
fn encode_functions(solver: &mut LookupSolver<Varisat>, functions: &[SnapshotFunction]) {
    for function in functions {
        let lit = function.lit;
        let assigned = solver.lookup(lit);
        if function.constant {
            solver.add_clause(&[assigned]);
            continue;
        }
        // lit holds iff one of its implication clauses fires
        let mut fire_lits = Vec::new();
        for clause in &function.implications {
            let fires = solver.add_variable();
            // fires ↔ ¬l1 ∧ ... ∧ ¬lk
            let mut all_false = vec![fires];
            for &l in clause.iter().filter(|l| l.var() != lit.var()) {
                let negated = solver.lookup(!l);
                solver.add_clause(&[!fires, negated]);
                all_false.push(solver.lookup(l));
            }
            solver.add_clause(&all_false);
            fire_lits.push(fires);
        }
        for &fires in &fire_lits {
            solver.add_clause(&[assigned, !fires]);
        }
        let mut some_fires = vec![!assigned];
        some_fires.extend(fire_lits);
        solver.add_clause(&some_fires);
    }
}
