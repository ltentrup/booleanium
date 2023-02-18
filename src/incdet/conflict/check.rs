//! (Incremental) conflict checking

use crate::{
    incdet::IncDet,
    literal::{filter_lit, Lit, Var},
    qcdcl::propagation::trail::DecLvl,
    sat::{cmsat::CryptoMiniSat, varisat::Varisat, LookupSolver, SatSolver},
};
use derivative::Derivative;
use std::collections::{BTreeMap, HashSet};
use tracing::{debug, trace};

#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct ConflictCheck<S: SatSolver> {
    #[derivative(Debug = "ignore")]
    sat_solver: LookupSolver<S>,
    #[derivative(Debug = "ignore")]
    assumptions: BTreeMap<DecLvl, S::Lit>,
}

impl<S: SatSolver> Default for ConflictCheck<S> {
    fn default() -> Self {
        Self { sat_solver: Default::default(), assumptions: BTreeMap::default() }
    }
}

impl<S: SatSolver> ConflictCheck<S> {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.sat_solver.set_var_count(count);
    }

    pub(crate) fn backtrack_to(&mut self, lvl: DecLvl) {
        // backtrackign to `lvl` means that we keep all entries with level <= `lvl`
        self.assumptions.split_off(&lvl.successor()).values().for_each(|&assumption_lit| {
            self.sat_solver.add_clause(&[!assumption_lit]);
        });
    }

    pub(crate) fn forget(&mut self, var: Var) {
        self.sat_solver.forget(var);
    }

    fn add_definition_clause(&mut self, lvl: DecLvl, clause: &[S::Lit]) {
        let assumption_lit =
            *self.assumptions.entry(lvl).or_insert_with(|| self.sat_solver.add_variable());
        self.sat_solver.add_clause(
            &clause.iter().copied().chain(std::iter::once(!assumption_lit)).collect::<Vec<_>>(),
        );
    }

    fn solve(&mut self, incremental_var: S::Lit) -> Option<HashSet<Lit>> {
        if !self
            .sat_solver
            .solve_with_assumptions(
                &self
                    .assumptions
                    .values()
                    .copied()
                    .chain(std::iter::once(incremental_var))
                    .collect::<Vec<_>>(),
            )
            .unwrap()
        {
            return None;
        }
        let model = self.sat_solver.orig_model()?;
        let model = model.into_iter().collect();
        Some(model)
    }
}

impl IncDet {
    pub(crate) fn is_conflicted(
        &mut self,
        var: Var,
        decision: Option<Lit>,
    ) -> Option<HashSet<Lit>> {
        // faster, incomplete check
        trace!("local conflict check");
        self.stats.skolem.local_conflict_checks += 1;
        self._is_conflicted::<Varisat<'static>>(var, decision, false)?;
        // slower, complete check
        trace!("global conflict check");
        self.stats.skolem.global_conflict_checks += 1;
        let assignment = self.is_conflicted_incremental(var, decision)?;
        // let assignment = self._is_conflicted(var, decision, true)
        self.stats.global.conflicts += 1;
        Some(assignment)
    }

    pub(crate) fn add_definition_to_conflict_check(&mut self, lit: Lit, is_decision: bool) {
        let lvl = self.trail.decision_level();
        // add definition from implication clauses
        for cid in [lit, lit.negated()].into_iter().flat_map(|lit| self.skolem[lit].implications())
        {
            let clause = &self.allocator[cid];
            let sat_clause = clause
                .iter()
                .map(|&l| self.conflict_check.sat_solver.lookup(l))
                .collect::<Vec<_>>();
            self.conflict_check.add_definition_clause(lvl, &sat_clause);
        }
        if !is_decision {
            return;
        }
        // add decided skolem functions
        trace!("Constraint for decided literal {lit}");
        let mut build = vec![self.conflict_check.sat_solver.lookup(lit.negated())];
        for cid in self.skolem[lit].implications() {
            let clause = &self.allocator[cid];
            debug_assert!(clause.lits().len() > 1);

            if clause.lits().len() == 2 {
                // there is only one other literal, there is no need to create additional variables
                let l = clause
                    .iter()
                    .find(filter_lit(lit))
                    .expect("there is a unique literal != `lit`");
                let l = self.conflict_check.sat_solver.lookup(l.negated());
                build.push(l);
            } else {
                let arbiter = self.conflict_check.sat_solver.add_variable();
                for l in clause.iter().filter(filter_lit(lit)) {
                    let l = self.conflict_check.sat_solver.lookup(l.negated());
                    self.conflict_check.add_definition_clause(lvl, &[arbiter, l]);
                }
                build.push(!arbiter);
            }
        }
        self.conflict_check.add_definition_clause(lvl, &build);
    }

    fn is_conflicted_incremental(
        &mut self,
        var: Var,
        decision: Option<Lit>,
    ) -> Option<HashSet<Lit>> {
        let incremental_var = self.conflict_check.sat_solver.add_variable();
        for lit in [Lit::positive(var), Lit::negative(var)] {
            let mut build = vec![!incremental_var];
            for cid in self.skolem[lit].implications() {
                let clause = &self.allocator[cid];
                let arbiter = self.conflict_check.sat_solver.add_variable();
                for l in clause.iter().copied().filter(|&l| l != lit) {
                    let l = self.conflict_check.sat_solver.lookup(l.negated());
                    self.conflict_check.sat_solver.add_clause(&[!incremental_var, arbiter, l]);
                }
                build.push(!arbiter);
            }
            match decision {
                Some(decision) if decision == lit.negated() => {
                    let arbiter = self.conflict_check.sat_solver.add_variable();
                    for cid in self.skolem[decision].implications() {
                        let clause = &self.allocator[cid];
                        let lits: Vec<_> = clause
                            .iter()
                            .filter(|l| l.var() != var)
                            .map(|&l| self.conflict_check.sat_solver.lookup(l))
                            .chain(std::iter::once(arbiter))
                            .chain(std::iter::once(!incremental_var))
                            .collect();
                        self.conflict_check.sat_solver.add_clause(&lits);
                    }
                    build.push(!arbiter);
                }
                _ => {}
            }
            self.conflict_check.sat_solver.add_clause(&build);
        }
        // if the formula is satisfiable, there is a conflict
        let result = self.conflict_check.solve(incremental_var)?;
        let assign =
            result.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", ");
        debug!("conflicting assignment: {}", assign);
        Some(result)
    }

    fn _is_conflicted<S: SatSolver>(
        &self,
        var: Var,
        decision: Option<Lit>,
        exact: bool,
    ) -> Option<HashSet<Lit>> {
        let mut solver = LookupSolver::<S>::default();
        solver.set_var_count(self.vars.get_var_count());

        if exact {
            // add already determined skolem functions
            for cid in self.iter_implication_clauses() {
                let clause = &self.allocator[cid];
                let clause = clause.iter().map(|&l| solver.lookup(l)).collect::<Vec<_>>();
                solver.add_clause(&clause);
            }
            // add decided skolem functions
            for &lit in self.trail.iter_decisions() {
                trace!("Constraint for decided literal {lit}");
                let mut build = vec![solver.lookup(lit.negated())];
                for cid in self.skolem[lit].implications() {
                    let clause = &self.allocator[cid];
                    let arbiter = solver.add_variable();
                    for l in clause.iter().filter(filter_lit(lit)) {
                        let lits = [arbiter, solver.lookup(l.negated())];
                        solver.add_clause(&lits);
                    }
                    build.push(!arbiter);
                }
                solver.add_clause(&build);
            }
        }

        for lit in [Lit::positive(var), Lit::negative(var)] {
            let mut build = Vec::new();
            for cid in self.skolem[lit].implications() {
                let clause = &self.allocator[cid];
                let arbiter = solver.add_variable();
                for l in clause.iter().copied().filter(|&l| l != lit) {
                    let lits = [arbiter, solver.lookup(l.negated())];
                    solver.add_clause(&lits);
                }
                build.push(!arbiter);
            }
            match decision {
                Some(decision) if decision == lit.negated() => {
                    let arbiter = solver.add_variable();
                    for cid in self.skolem[decision].implications() {
                        let clause = &self.allocator[cid];
                        let lits: Vec<_> = clause
                            .iter()
                            .filter(|l| l.var() != var)
                            .map(|&l| solver.lookup(l))
                            .chain(std::iter::once(arbiter))
                            .collect();
                        solver.add_clause(&lits);
                    }
                    build.push(!arbiter);
                }
                _ => {}
            }
            solver.add_clause(&build);
        }

        // if the formula is satisfiable, there is a conflict
        if !solver.solve().unwrap() {
            return None;
        }
        let model = solver.orig_model()?;
        let result: HashSet<Lit> = model.into_iter().collect();
        let assign =
            result.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", ");
        debug!("conflicting assignment: {}", assign);
        Some(result)
    }
}
