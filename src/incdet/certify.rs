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
//! over the universal variables. Verification then asks a SAT solver
//! whether some universal assignment falsifies an original matrix clause
//! under these functions; unsatisfiability certifies the result.

use crate::{
    incdet::propagation::assignment::Value,
    incdet::IncDet,
    sat::{varisat::Varisat, LookupSolver, SatSolver},
};
use tracing::debug;

impl IncDet {
    /// Checks the Skolem functions extracted from a satisfiable solver
    /// state against the matrix. Returns `true` if the certificate is
    /// valid. Must only be called after [`IncDet::solve`] returned
    /// [`crate::SolverResult::Satisfiable`].
    #[must_use]
    pub fn verify_skolem_functions(&self) -> bool {
        let mut solver = LookupSolver::<Varisat>::default();
        solver.set_var_count(self.vars.get_var_count());

        // encode the function of every assigned variable in trail order
        for &lit in self.trail.iter() {
            let var = lit.var();
            match self.assignment[var].expect("trail variables are assigned") {
                Value::True | Value::False => {
                    let unit = solver.lookup(lit);
                    solver.add_clause(&[unit]);
                }
                Value::PositiveImplications | Value::NegativeImplications => {
                    // lit holds iff one of its implication clauses fires
                    let mut fire_lits = Vec::new();
                    for cid in self.skolem[lit].implications() {
                        let clause = &self.allocator[cid];
                        let fires = solver.add_variable();
                        // ¬l1 ∧ ... ∧ ¬lk ↔ fires
                        let mut all_false = vec![fires];
                        for &l in clause.iter().filter(|l| l.var() != var) {
                            let negated = solver.lookup(!l);
                            solver.add_clause(&[!fires, negated]);
                            all_false.push(solver.lookup(l));
                        }
                        solver.add_clause(&all_false);
                        fire_lits.push(fires);
                    }
                    // lit ↔ (fires_1 ∨ ... ∨ fires_n)
                    let assigned = solver.lookup(lit);
                    for &fires in &fire_lits {
                        solver.add_clause(&[assigned, !fires]);
                    }
                    let mut some_fires = vec![!assigned];
                    some_fires.extend(fire_lits);
                    solver.add_clause(&some_fires);
                }
            }
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
            debug!("Skolem function verification failed");
        }
        !counterexample
    }
}
