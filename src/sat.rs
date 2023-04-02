//! Generic SAT solver interface that supports incremental solving

use derivative::Derivative;

use crate::{
    datastructure::VarVec,
    literal::{Lit, Var},
};

#[cfg(feature = "cryptominisat")]
pub(crate) mod cmsat;
pub(crate) mod varisat;

/// Incremental SAT solver interface.
///
/// We assume variables to be index-based, such that mapping from
/// [`crate::literal::Lit`] to [`SatSolver::Lit`] is cheap.
pub(crate) trait SatSolver: Default {
    type Lit: SatSolverLit;
    type Err: std::error::Error + 'static;

    fn add_variable(&mut self) -> Self::Lit;
    fn add_clause(&mut self, lits: &[Self::Lit]);
    fn solve_with_assumptions(&mut self, assumptions: &[Self::Lit]) -> Result<bool, Self::Err>;
    fn model(&mut self) -> Option<&[Self::Lit]>;
    fn failed_assumptions(&mut self) -> Option<&[Self::Lit]>;

    fn add_variables(&mut self, variables: usize) {
        (0..variables).for_each(|_| {
            self.add_variable();
        });
    }
    fn solve(&mut self) -> Result<bool, Self::Err> {
        self.solve_with_assumptions(&[])
    }
}

pub(crate) trait SatSolverLit: Copy + Eq + std::ops::Not<Output = Self> {}

#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct LookupSolver<S: SatSolver> {
    #[derivative(Debug = "ignore")]
    sat_solver: S,
    #[derivative(Debug = "ignore")]
    var_lookup: VarVec<Option<S::Lit>>,
}

impl<S: SatSolver> Default for LookupSolver<S> {
    fn default() -> Self {
        Self { sat_solver: Default::default(), var_lookup: VarVec::default() }
    }
}

impl<S: SatSolver> LookupSolver<S> {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.var_lookup.set_var_count(count);
    }

    pub(crate) fn forget(&mut self, var: Var) {
        self.var_lookup[var].take();
    }

    pub(crate) fn lookup(&mut self, lit: Lit) -> S::Lit {
        let sat_var =
            *self.var_lookup[lit.var()].get_or_insert_with(|| self.sat_solver.add_variable());
        if lit.is_negative() {
            !sat_var
        } else {
            sat_var
        }
    }

    pub(crate) fn orig_model(&mut self) -> Option<Vec<Lit>> {
        let model = self.sat_solver.model()?;
        Some(
            self.var_lookup
                .iter()
                .filter_map(|(var, &mapped)| {
                    let mapped = mapped?;
                    if model.contains(&mapped) {
                        Some(Lit::positive(var))
                    } else if model.contains(&!mapped) {
                        Some(Lit::negative(var))
                    } else {
                        None
                    }
                })
                .collect(),
        )
    }
}

impl<S: SatSolver> SatSolver for LookupSolver<S> {
    type Lit = S::Lit;
    type Err = S::Err;

    fn add_variable(&mut self) -> Self::Lit {
        self.sat_solver.add_variable()
    }

    fn add_clause(&mut self, lits: &[Self::Lit]) {
        self.sat_solver.add_clause(lits);
    }

    fn solve_with_assumptions(&mut self, assumptions: &[Self::Lit]) -> Result<bool, Self::Err> {
        self.sat_solver.solve_with_assumptions(assumptions)
    }

    fn model(&mut self) -> Option<&[Self::Lit]> {
        self.sat_solver.model()
    }

    fn failed_assumptions(&mut self) -> Option<&[Self::Lit]> {
        self.sat_solver.failed_assumptions()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    pub(crate) fn test_basic<S: SatSolver>() -> Result<(), Box<dyn std::error::Error>> {
        let mut solver = S::default();

        // create variables
        let x = solver.add_variable();
        let y = solver.add_variable();
        let z = solver.add_variable();

        solver.add_clause(&[!x, y]);
        solver.add_clause(&[!y, z]);
        assert!(solver.solve()?);

        solver.add_clause(&[!z, x]);
        assert!(solver.solve()?);

        let model = solver.model().unwrap();
        assert!(
            [x, y, z].into_iter().all(|lit| model.contains(&lit))
                || [!x, !y, !z].into_iter().all(|lit| model.contains(&lit))
        );

        // solve with assumptions
        let ignore_clauses = solver.add_variable();
        solver.add_clause(&[ignore_clauses, !z, !y]);
        solver.add_clause(&[ignore_clauses, z, y]);

        assert!(!solver.solve_with_assumptions(&[!ignore_clauses])?);

        solver.add_clause(&[ignore_clauses]);
        assert!(solver.solve()?);

        Ok(())
    }
}
