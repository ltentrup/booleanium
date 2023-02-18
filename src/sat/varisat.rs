//! Implementation of SAT solver interface for (varisat)[https://crates.io/crates/varisat].

use super::{SatSolver, SatSolverLit};
use crate::literal::{Lit, Var};
use varisat::ExtendFormula;

pub(crate) struct Varisat<'a> {
    solver: varisat::Solver<'a>,
    /// the index of the next variable
    new_lit: usize,
    model: Vec<varisat::Lit>,
}

impl<'a> SatSolver for Varisat<'a> {
    type Lit = varisat::Lit;
    type Err = varisat::solver::SolverError;

    fn add_variables(&mut self, variables: usize) {
        self.new_lit += variables;
    }

    fn add_variable(&mut self) -> Self::Lit {
        let var = Var::from_index(self.new_lit.try_into().unwrap());
        self.new_lit += 1;
        Lit::positive(var).into()
    }

    fn add_clause(&mut self, lits: &[Self::Lit]) {
        self.solver.add_clause(lits);
    }

    fn solve_with_assumptions(&mut self, assumptions: &[Self::Lit]) -> Result<bool, Self::Err> {
        self.solver.assume(assumptions);
        let result = self.solver.solve()?;
        Ok(result)
    }

    fn model(&mut self) -> Option<&[Self::Lit]> {
        self.model = self.solver.model()?;
        Some(&self.model)
    }

    fn failed_assumptions(&mut self) -> Option<&[Self::Lit]> {
        self.solver.failed_core()
    }
}

impl<'a> Default for Varisat<'a> {
    fn default() -> Self {
        Self { solver: varisat::Solver::new(), new_lit: 0, model: Vec::default() }
    }
}

impl SatSolverLit for varisat::Lit {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_basic() -> Result<(), Box<dyn std::error::Error>> {
        crate::sat::test::test_basic::<Varisat>()
    }
}
