//! Implementation of the SAT solver interface for [CaDiCaL](https://crates.io/crates/cadical).

use super::{SatSolver, SatSolverLit};

/// A literal in the DIMACS convention: nonzero, the sign is the polarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CadicalLit(i32);

impl std::ops::Not for CadicalLit {
    type Output = Self;

    fn not(self) -> Self {
        Self(-self.0)
    }
}

impl SatSolverLit for CadicalLit {
    fn var_index(self) -> usize {
        self.0.unsigned_abs() as usize - 1
    }

    fn is_positive(self) -> bool {
        self.0 > 0
    }
}

#[derive(Debug, thiserror::Error)]
#[error("CaDiCaL did not finish solving")]
pub(crate) struct CadicalError;

pub(crate) struct Cadical {
    solver: ::cadical::Solver,
    /// the highest variable handed out so far
    max_var: i32,
    model: Vec<CadicalLit>,
}

impl Default for Cadical {
    fn default() -> Self {
        Self { solver: ::cadical::Solver::new(), max_var: 0, model: Vec::default() }
    }
}

impl SatSolver for Cadical {
    type Lit = CadicalLit;
    type Err = CadicalError;

    fn add_variable(&mut self) -> Self::Lit {
        self.max_var += 1;
        CadicalLit(self.max_var)
    }

    fn add_clause(&mut self, lits: &[Self::Lit]) {
        self.solver.add_clause(lits.iter().map(|lit| lit.0));
    }

    fn solve_with_assumptions(&mut self, assumptions: &[Self::Lit]) -> Result<bool, Self::Err> {
        self.solver.solve_with(assumptions.iter().map(|lit| lit.0)).ok_or(CadicalError)
    }

    fn model(&mut self) -> Option<&[Self::Lit]> {
        self.model.clear();
        for var in 1..=self.max_var {
            // unassigned (don't care) variables default to false
            let value = self.solver.value(var).unwrap_or(false);
            self.model.push(CadicalLit(if value { var } else { -var }));
        }
        Some(&self.model)
    }

    fn failed_assumptions(&mut self) -> Option<&[Self::Lit]> {
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_basic() -> Result<(), Box<dyn std::error::Error>> {
        crate::sat::test::test_basic::<Cadical>()
    }
}
