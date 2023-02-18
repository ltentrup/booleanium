//! Implementation of SAT solver interface for (cryptominisat)[https://crates.io/crates/cryptominisat].

use std::convert::Infallible;

use cryptominisat::Lbool;

use super::{SatSolver, SatSolverLit};

pub(crate) struct CryptoMiniSat {
    solver: cryptominisat::Solver,
    model: Vec<cryptominisat::Lit>,
}

impl SatSolver for CryptoMiniSat {
    type Lit = cryptominisat::Lit;
    type Err = Infallible;

    fn add_variables(&mut self, variables: usize) {
        self.solver.new_vars(variables)
    }

    fn add_variable(&mut self) -> Self::Lit {
        self.solver.new_var()
    }

    fn add_clause(&mut self, lits: &[Self::Lit]) {
        self.solver.add_clause(lits);
    }

    fn solve_with_assumptions(&mut self, assumptions: &[Self::Lit]) -> Result<bool, Self::Err> {
        let result = self.solver.solve_with_assumptions(assumptions);
        match result {
            Lbool::True => Ok(true),
            Lbool::False => Ok(false),
            Lbool::Undef => todo!(),
        }
    }

    fn model(&mut self) -> Option<&[Self::Lit]> {
        self.model = self
            .solver
            .get_model()
            .iter()
            .enumerate()
            .filter_map(|(idx, &value)| {
                let negated = match value {
                    Lbool::True => false,
                    Lbool::False => true,
                    Lbool::Undef => return None,
                };
                Some(cryptominisat::Lit::new(idx.try_into().unwrap(), negated).unwrap())
            })
            .collect();
        Some(&self.model)
    }

    fn failed_assumptions(&mut self) -> Option<&[Self::Lit]> {
        Some(self.solver.get_conflict())
    }
}

impl Default for CryptoMiniSat {
    fn default() -> Self {
        Self { solver: cryptominisat::Solver::new(), model: Vec::default() }
    }
}

impl SatSolverLit for cryptominisat::Lit {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_basic() -> Result<(), Box<dyn std::error::Error>> {
        crate::sat::test::test_basic::<CryptoMiniSat>()
    }
}
