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
                    // the constant response holds on the full cube: every
                    // original clause needs a support among the cube and
                    // response literals
                    let supports: std::collections::HashSet<Lit> =
                        cube.iter().chain(response.iter()).copied().collect();
                    self.allocator
                        .ids()
                        .take(self.original_clause_count)
                        .all(|cid| self.allocator[cid].iter().any(|l| supports.contains(l)))
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

        // encode the functions in trail order
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

        // ask for a universal assignment that falsifies an original clause
        let mut some_falsified = Vec::new();
        for cid in self.allocator.ids().take(self.original_clause_count) {
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
                for cid in self.allocator.ids().take(self.original_clause_count) {
                    let clause = &self.allocator[cid];
                    if clause.iter().all(|l| assignment.contains(&!*l)) {
                        debug!("falsified original clause: {clause}");
                    }
                }
                let lits: Vec<String> = assignment.iter().map(ToString::to_string).collect();
                debug!("counterexample assignment: {}", lits.join(" "));
            }
        }
        !counterexample
    }
}
