//! (Incremental) conflict checking
//!
//! A variable is conflicted if there is an assignment of the universal
//! variables — consistent with the Skolem functions determined so far —
//! under which implication clauses of both polarities fire, forcing the
//! variable to both values.
//!
//! The check runs in two stages: a syntactic pre-check tests whether any
//! pair of implication clauses of opposite polarity can fire simultaneously
//! at all (ignoring the global constraints); only if such a pair exists, a
//! complete SAT-based check runs. The SAT-based check either rebuilds a
//! solver per check or reuses a single incremental solver
//! ([`crate::incdet::Options::incremental_conflict_check`]). The incremental
//! solver encodes every clause and every firing condition at most once:
//!
//! * a *clause literal* `r` with `r → C` activates clause `C` of a
//!   determined Skolem function, guarded per decision level,
//! * a *fire arbiter* `a` with `¬a → (all literals of C except the implied
//!   variable are false)` expresses that implication `C` fires,
//! * a *no-fire arbiter* `b` with `¬b → C \ {v}` expresses that `C` is
//!   satisfied without its implied variable, i.e., does not fire.
//!
//! Backtracking needs no cleanup beyond disabling the per-level guards:
//! stale arbiters are simply never referenced again.

use crate::{
    clause::{alloc::ClauseId, Clause},
    incdet::propagation::trail::DecLvl,
    incdet::IncDet,
    literal::{Lit, Var},
    sat::{varisat::Varisat, LookupSolver, SatSolver},
};
use derivative::Derivative;
use std::collections::{BTreeMap, HashMap, HashSet};
use tracing::{debug, trace};

#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct ConflictCheck<S: SatSolver> {
    #[derivative(Debug = "ignore")]
    sat_solver: LookupSolver<S>,
    #[derivative(Debug = "ignore")]
    assumptions: BTreeMap<DecLvl, S::Lit>,
    #[derivative(Debug = "ignore")]
    clause_lits: HashMap<ClauseId, S::Lit>,
    #[derivative(Debug = "ignore")]
    fire_arbiters: HashMap<(ClauseId, Lit), S::Lit>,
}

impl<S: SatSolver> Default for ConflictCheck<S> {
    fn default() -> Self {
        Self {
            sat_solver: LookupSolver::default(),
            assumptions: BTreeMap::default(),
            clause_lits: HashMap::default(),
            fire_arbiters: HashMap::default(),
        }
    }
}

impl<S: SatSolver> ConflictCheck<S> {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.sat_solver.set_var_count(count);
    }

    pub(crate) fn backtrack_to(&mut self, lvl: DecLvl) {
        // backtracking to `lvl` means that we keep all entries with level <= `lvl`
        self.assumptions.split_off(&lvl.successor()).values().for_each(|&assumption_lit| {
            self.sat_solver.add_clause(&[!assumption_lit]);
        });
    }

    fn add_definition_clause(&mut self, lvl: DecLvl, clause: &[S::Lit]) {
        let assumption_lit =
            *self.assumptions.entry(lvl).or_insert_with(|| self.sat_solver.add_variable());
        self.sat_solver.add_clause(
            &clause.iter().copied().chain(std::iter::once(!assumption_lit)).collect::<Vec<_>>(),
        );
    }

    /// Returns the activation literal `r` with `r → C`, encoding the clause
    /// on first use.
    fn clause_lit(&mut self, cid: ClauseId, clause: &Clause) -> S::Lit {
        if let Some(&lit) = self.clause_lits.get(&cid) {
            return lit;
        }
        let activation = self.sat_solver.add_variable();
        let mut encoded: Vec<S::Lit> = clause.iter().map(|&l| self.sat_solver.lookup(l)).collect();
        encoded.push(!activation);
        self.sat_solver.add_clause(&encoded);
        self.clause_lits.insert(cid, activation);
        activation
    }

    /// Returns the fire arbiter `a` with `¬a → (C \ {lit's variable} all
    /// false)`, encoding the condition on first use.
    fn fire_arbiter(&mut self, cid: ClauseId, lit: Lit, clause: &Clause) -> S::Lit {
        if let Some(&arbiter) = self.fire_arbiters.get(&(cid, lit)) {
            return arbiter;
        }
        let arbiter = self.sat_solver.add_variable();
        for &l in clause.iter().filter(|l| l.var() != lit.var()) {
            let negated = self.sat_solver.lookup(!l);
            self.sat_solver.add_clause(&[arbiter, negated]);
        }
        self.fire_arbiters.insert((cid, lit), arbiter);
        arbiter
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
    /// Note that for decisions no special handling is needed: a decided
    /// variable takes a value only if one of its implications fires, so the
    /// default value never creates a conflict by itself and the check
    /// reduces to "both polarities can fire" in all cases.
    pub(crate) fn is_conflicted(&mut self, var: Var) -> Option<HashSet<Lit>> {
        // syntactic, incomplete check
        trace!("local conflict check");
        self.stats.skolem.local_conflict_checks += 1;
        if !self.may_be_conflicted(var) {
            return None;
        }
        // slower, complete check
        trace!("global conflict check");
        self.stats.skolem.global_conflict_checks += 1;
        let mut assignment = if self.options.incremental_conflict_check {
            self.is_conflicted_incremental(var)?
        } else {
            self._is_conflicted::<Varisat>(var, true)?
        };
        // the model contains no meaningful value for the checked variable
        assignment.remove(&Lit::positive(var));
        assignment.remove(&Lit::negative(var));
        self.stats.global.conflicts += 1;
        Some(assignment)
    }

    /// Syntactic over-approximation of the conflict check: ignoring all
    /// global constraints, both polarities can fire simultaneously if and
    /// only if some pair of implication clauses of opposite polarity has no
    /// clashing literals (and neither clause is satisfied by a constant).
    fn may_be_conflicted(&self, var: Var) -> bool {
        let mut premise = HashSet::new();
        for cid_pos in self.skolem[Lit::positive(var)].implications() {
            let pos = &self.allocator[cid_pos];
            if pos
                .iter()
                .any(|&l| l.var() != var && self.assignment.constant_value(l) == Some(true))
            {
                // satisfied by a constant, the implication can never fire
                continue;
            }
            premise.clear();
            premise.extend(pos.iter().filter(|l| l.var() != var).copied());
            for cid_neg in self.skolem[Lit::negative(var)].implications() {
                let neg = &self.allocator[cid_neg];
                let compatible = neg.iter().filter(|l| l.var() != var).all(|&l| {
                    !premise.contains(&!l) && self.assignment.constant_value(l) != Some(true)
                });
                if compatible {
                    return true;
                }
            }
        }
        false
    }

    pub(crate) fn add_definition_to_conflict_check(&mut self, lit: Lit, is_decision: bool) {
        if !self.options.incremental_conflict_check {
            return;
        }
        let lvl = self.trail.decision_level();
        // activate the implication clauses of the assigned variable
        for cid in [lit, lit.negated()].into_iter().flat_map(|lit| self.skolem[lit].implications())
        {
            let activation = self.conflict_check.clause_lit(cid, &self.allocator[cid]);
            self.conflict_check.add_definition_clause(lvl, &[activation]);
        }
        if !is_decision {
            return;
        }
        // a decided variable only takes the decided value if one of its
        // implications fires
        trace!("Constraint for decided literal {lit}");
        let mut build = vec![self.conflict_check.sat_solver.lookup(lit.negated())];
        for cid in self.skolem[lit].implications() {
            let arbiter = self.conflict_check.fire_arbiter(cid, lit, &self.allocator[cid]);
            build.push(!arbiter);
        }
        self.conflict_check.add_definition_clause(lvl, &build);
    }

    fn is_conflicted_incremental(&mut self, var: Var) -> Option<HashSet<Lit>> {
        let incremental_var = self.conflict_check.sat_solver.add_variable();
        for lit in [Lit::positive(var), Lit::negative(var)] {
            let mut build = vec![!incremental_var];
            for cid in self.skolem[lit].implications() {
                let arbiter = self.conflict_check.fire_arbiter(cid, lit, &self.allocator[cid]);
                build.push(!arbiter);
            }
            self.conflict_check.sat_solver.add_clause(&build);
        }
        // if the formula is satisfiable, there is a conflict
        let result = self.conflict_check.solve(incremental_var);
        // permanently retire the per-check clauses
        self.conflict_check.sat_solver.add_clause(&[!incremental_var]);
        let result = result?;
        let assign =
            result.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", ");
        debug!("conflicting assignment: {}", assign);
        Some(result)
    }

    fn _is_conflicted<S: SatSolver>(&self, var: Var, exact: bool) -> Option<HashSet<Lit>> {
        let mut solver = LookupSolver::<S>::default();
        solver.set_var_count(self.vars.get_var_count());

        // constants hold under every universal assignment, add them as
        // unit clauses
        for &lit in self.trail.iter() {
            if self.assignment.constant_value(lit) == Some(true) {
                let unit = solver.lookup(lit);
                solver.add_clause(&[unit]);
            }
        }

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
                    for &l in clause.iter().filter(|l| l.var() != lit.var()) {
                        let lits = [arbiter, solver.lookup(!l)];
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
