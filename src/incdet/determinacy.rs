//! Determinacy checking.
//!
//! An existential variable is uniquely determined if under every assignment
//! of the remaining variables at least one of its implication clauses fires.
//! This is checked by testing unsatisfiability of the conjunction of all
//! implication clauses with the variable's literals removed.
//!
//! These formulas are tiny (a handful of short clauses) and the check runs
//! very often, so a full SAT solver is not built per check. Instead a
//! budgeted DPLL procedure decides almost all instances directly; only if
//! the budget is exhausted (adversarially large implication sets) the check
//! falls back to a freshly built SAT solver.

use crate::{
    incdet::IncDet,
    literal::{Lit, Var},
    sat::{varisat::Varisat, SatSolver},
};
use tracing::trace;

/// Number of DPLL steps (unit propagations and case splits) before falling
/// back to a real SAT solver.
const DPLL_BUDGET: u32 = 10_000;

/// Result of the determinacy check.
pub(crate) enum Determinacy {
    /// An implication of the literal fires unconditionally: the variable
    /// has the constant Skolem function of the literal's polarity.
    /// Constants cascade — they satisfy and shorten clauses in every
    /// downstream check — so they are propagated as constants instead of
    /// generic deterministic functions.
    Constant(Lit),
    /// The implications force a unique value under every assignment.
    Deterministic,
    /// The variable is not determined by its implications.
    Undetermined,
}

impl IncDet {
    /// Checks whether the implication clauses of `var` force a unique value
    /// under every assignment of the remaining variables.
    pub(crate) fn has_unique_consequence(&mut self, var: Var) -> Determinacy {
        let started = std::time::Instant::now();
        let determinacy = self.unique_consequence(var);
        self.stats.skolem.det_check_time += started.elapsed();
        determinacy
    }

    fn unique_consequence(&mut self, var: Var) -> Determinacy {
        self.stats.skolem.local_det_checks += 1;
        // collect the implication clauses without `var`, simplified by the
        // constant assignments
        let mut clauses = Vec::new();
        for lit in [Lit::positive(var), Lit::negative(var)] {
            for cid in self.skolem[lit].implications() {
                let clause = &self.allocator[cid];
                if clause
                    .iter()
                    .any(|&l| l.var() != var && self.assignment.constant_value(l) == Some(true))
                {
                    // the implication can never fire as the clause is
                    // globally satisfied by a constant
                    continue;
                }
                let simplified: Vec<Lit> = clause
                    .iter()
                    .filter(|l| l.var() != var)
                    .filter(|&&l| self.assignment.constant_value(l) != Some(false))
                    .copied()
                    .collect();
                if simplified.is_empty() {
                    // the implication fires unconditionally
                    return Determinacy::Constant(lit);
                }
                clauses.push(simplified);
            }
        }
        if clauses.is_empty() {
            return Determinacy::Undetermined;
        }
        let mut budget = DPLL_BUDGET;
        let deterministic = if let Some(satisfiable) = dpll(clauses.clone(), &mut budget) {
            !satisfiable
        } else {
            trace!("determinacy check for {var} exceeded the DPLL budget");
            !solve_with_sat_solver::<Varisat>(&clauses)
        };
        if deterministic {
            Determinacy::Deterministic
        } else {
            Determinacy::Undetermined
        }
    }
}

/// Decides satisfiability of the clause set with unit propagation and case
/// splitting, simplifying copies of the clause list. Returns `None` if the
/// budget is exhausted.
fn dpll(mut clauses: Vec<Vec<Lit>>, budget: &mut u32) -> Option<bool> {
    // unit propagation
    loop {
        if clauses.is_empty() {
            return Some(true);
        }
        if clauses.iter().any(Vec::is_empty) {
            return Some(false);
        }
        *budget = budget.checked_sub(1)?;
        let Some(unit) = clauses.iter().find(|clause| clause.len() == 1) else {
            break;
        };
        let lit = unit[0];
        assign(&mut clauses, lit);
    }
    // case split on the first literal of the first clause
    let lit = clauses[0][0];
    let mut positive = clauses.clone();
    assign(&mut positive, lit);
    if dpll(positive, budget)? {
        return Some(true);
    }
    assign(&mut clauses, !lit);
    dpll(clauses, budget)
}

/// Updates the clause set to reflect that `lit` is assigned true: satisfied
/// clauses are removed and falsified literals are deleted.
fn assign(clauses: &mut Vec<Vec<Lit>>, lit: Lit) {
    clauses.retain(|clause| !clause.contains(&lit));
    for clause in clauses {
        clause.retain(|&l| l != !lit);
    }
}

/// Fallback for clause sets too large for the budgeted DPLL.
fn solve_with_sat_solver<S: SatSolver>(clauses: &[Vec<Lit>]) -> bool {
    let mut solver = crate::sat::LookupSolver::<S>::default();
    let var_count = clauses.iter().flatten().map(|l| l.var().as_index() + 1).max().unwrap_or(0);
    solver.set_var_count(var_count);
    for clause in clauses {
        let clause: Vec<S::Lit> = clause.iter().map(|&l| solver.lookup(l)).collect();
        solver.add_clause(&clause);
    }
    solver.solve().unwrap()
}

#[cfg(test)]
mod test {
    use super::*;

    fn lit(l: i32) -> Lit {
        Lit::from_dimacs(l)
    }

    #[test]
    fn dpll_basic() {
        let mut budget = u32::MAX;
        // (1) ∧ (¬1) is unsatisfiable
        assert_eq!(dpll(vec![vec![lit(1)], vec![lit(-1)]], &mut budget), Some(false));
        // (1 ∨ 2) ∧ (¬1 ∨ 2) ∧ (¬2 ∨ 3) is satisfiable
        assert_eq!(
            dpll(
                vec![vec![lit(1), lit(2)], vec![lit(-1), lit(2)], vec![lit(-2), lit(3)]],
                &mut budget
            ),
            Some(true)
        );
        // xor-style covering set: every assignment fires some clause
        assert_eq!(
            dpll(
                vec![
                    vec![lit(1), lit(2)],
                    vec![lit(-1), lit(2)],
                    vec![lit(1), lit(-2)],
                    vec![lit(-1), lit(-2)],
                ],
                &mut budget
            ),
            Some(false)
        );
    }

    #[test]
    fn dpll_budget_exhaustion() {
        let mut budget = 1;
        let clauses = vec![
            vec![lit(1), lit(2)],
            vec![lit(-1), lit(2)],
            vec![lit(1), lit(-2)],
            vec![lit(-1), lit(-2)],
        ];
        assert_eq!(dpll(clauses.clone(), &mut budget), None);
        assert!(!solve_with_sat_solver::<Varisat>(&clauses));
    }
}
