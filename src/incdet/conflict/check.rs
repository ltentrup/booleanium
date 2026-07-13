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
    incdet::{ConflictSolver, IncDet},
    literal::{Lit, Var},
    sat::{LookupSolver, SatSolver},
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
    /// Clauses that have been added permanently (root-level definitions).
    #[derivative(Debug = "ignore")]
    permanent_clauses: HashSet<ClauseId>,
}

impl<S: SatSolver> Default for ConflictCheck<S> {
    fn default() -> Self {
        Self {
            sat_solver: LookupSolver::default(),
            assumptions: BTreeMap::default(),
            clause_lits: HashMap::default(),
            fire_arbiters: HashMap::default(),
            permanent_clauses: HashSet::default(),
        }
    }
}

impl<S: SatSolver> ConflictCheck<S> {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.sat_solver.set_var_count(count);
    }

    pub(crate) fn backtrack_to(&mut self, lvl: DecLvl) {
        // Backtracking to `lvl` keeps all entries with level <= `lvl`. The
        // dropped guards are not retired with unit clauses: a re-populated
        // level gets a fresh guard, so the dropped guards are never assumed
        // again and their clauses stay inert until the next solver reboot
        // sheds them (eager units would make the backend re-simplify its
        // whole clause database on every backtrack).
        self.assumptions.split_off(&lvl.successor());
    }

    fn add_definition_clause(&mut self, lvl: DecLvl, clause: &[S::Lit]) {
        let assumption_lit =
            *self.assumptions.entry(lvl).or_insert_with(|| self.sat_solver.add_variable());
        self.sat_solver.add_clause(
            &clause.iter().copied().chain(std::iter::once(!assumption_lit)).collect::<Vec<_>>(),
        );
    }

    /// Adds a root-level definition clause directly, without reification or
    /// guards. Root-level definitions are permanent, and the unmodified
    /// clause enables structural reasoning (e.g. XOR detection) in the
    /// backend solver.
    fn add_permanent_clause(&mut self, cid: ClauseId, clause: &Clause) {
        if !self.permanent_clauses.insert(cid) {
            return;
        }
        let encoded: Vec<S::Lit> = clause.iter().map(|&l| self.sat_solver.lookup(l)).collect();
        self.sat_solver.add_clause(&encoded);
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

    /// Permanently excludes a cube over universal variables from the
    /// conflict search: universal assignments inside the cube are handled
    /// by a recorded CEGAR case.
    pub(crate) fn add_universal_exclusion(&mut self, cube: &[crate::literal::Lit]) {
        let encoded: Vec<S::Lit> = cube.iter().map(|&l| self.sat_solver.lookup(!l)).collect();
        self.sat_solver.add_clause(&encoded);
    }

    fn solve(&mut self, check_assumptions: &[S::Lit]) -> Option<HashSet<Lit>> {
        if !self
            .sat_solver
            .solve_with_assumptions(
                &self
                    .assumptions
                    .values()
                    .copied()
                    .chain(check_assumptions.iter().copied())
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
            self._is_conflicted::<ConflictSolver>(var, true)?
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
        self.add_definition_to_conflict_check_at(lit, is_decision, lvl);
    }

    fn add_definition_to_conflict_check_at(&mut self, lit: Lit, is_decision: bool, lvl: DecLvl) {
        // activate the implication clauses of the assigned variable
        for cid in [lit, lit.negated()].into_iter().flat_map(|lit| self.skolem[lit].implications())
        {
            if lvl.is_root() {
                // Root-level definitions are permanent, so the clause can be
                // added directly without reification. This keeps the clause
                // structure intact, which enables structural reasoning in
                // the SAT solver (e.g. XOR detection).
                self.conflict_check.add_permanent_clause(cid, &self.allocator[cid]);
            } else {
                let activation = self.conflict_check.clause_lit(cid, &self.allocator[cid]);
                self.conflict_check.add_definition_clause(lvl, &[activation]);
            }
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

    /// Rebuilds the incremental conflict-check solver from the live state
    /// by replaying the definitions of the trail. This sheds the retired
    /// clauses of finished checks and backtracked levels, which the
    /// backend solver cannot delete itself and which otherwise slow down
    /// every solving call.
    pub(crate) fn reboot_conflict_check(&mut self) {
        debug!("rebooting the incremental conflict-check solver");
        self.stats.skolem.conflict_check_reboots += 1;
        self.conflict_check = ConflictCheck::default();
        self.conflict_check.set_var_count(self.vars.get_var_count());
        let trail: Vec<Lit> = self.trail.iter().copied().collect();
        for lit in trail {
            let lvl = self.dec_lvls[lit.var()].expect("trail variables have decision levels");
            let data = &self.vars[lit.var()];
            if data.scope.is_some() && data.is_universal(&self.prefix) {
                // an active case assumption
                let unit = self.conflict_check.sat_solver.lookup(lit);
                self.conflict_check.add_definition_clause(lvl, &[unit]);
                continue;
            }
            let is_decision = self.trail.is_decision(lit);
            self.add_definition_to_conflict_check_at(lit, is_decision, lvl);
        }
        for case in &self.handled_cases {
            self.conflict_check.add_universal_exclusion(case.cube());
        }
    }

    /// Excludes a handled case from future conflict checks.
    pub(crate) fn conflict_check_exclude_cube(&mut self, cube: &[Lit]) {
        if self.options.incremental_conflict_check {
            self.conflict_check.add_universal_exclusion(cube);
        }
    }

    /// Adds an active case assumption as a unit clause guarded by the
    /// assumption's decision level.
    pub(crate) fn conflict_check_assume(&mut self, lit: Lit) {
        if !self.options.incremental_conflict_check {
            return;
        }
        let lvl = self.trail.decision_level();
        let unit = self.conflict_check.sat_solver.lookup(lit);
        self.conflict_check.add_definition_clause(lvl, &[unit]);
    }

    /// Checks whether the constant assumption `lit` is violated: a
    /// universal assignment — within the standing exclusions, constants,
    /// and level guards — under which an implication clause of `!lit`
    /// fires, forcing the opposite of the assumed constant. Implication
    /// clauses are only registered on unassigned variables, so the set is
    /// frozen while the assumption is assigned and one check per
    /// (re-)assumption covers it.
    pub(crate) fn is_assumption_conflicted(&mut self, lit: Lit) -> Option<HashSet<Lit>> {
        if self.skolem[!lit].len() == 0 {
            return None;
        }
        // syntactic pre-check: an implication clause satisfied by a
        // constant can never fire
        let fireable = self.skolem[!lit].implications().any(|cid| {
            !self.allocator[cid]
                .iter()
                .any(|&l| l.var() != lit.var() && self.assignment.constant_value(l) == Some(true))
        });
        if !fireable {
            return None;
        }
        self.stats.skolem.global_conflict_checks += 1;
        let arbiters: Vec<_> = self.skolem[!lit]
            .implications()
            .map(|cid| self.conflict_check.fire_arbiter(cid, !lit, &self.allocator[cid]))
            .collect();
        let mut assumptions = Vec::new();
        if let [arbiter] = arbiters[..] {
            assumptions.push(!arbiter);
        } else {
            let guard = self.conflict_check.sat_solver.add_variable();
            let mut build = vec![!guard];
            build.extend(arbiters.into_iter().map(|arbiter| !arbiter));
            self.conflict_check.sat_solver.add_clause(&build);
            assumptions.push(guard);
        }
        let mut result = self.conflict_check.solve(&assumptions)?;
        result.remove(&Lit::positive(lit.var()));
        result.remove(&Lit::negative(lit.var()));
        self.stats.global.conflicts += 1;
        Some(result)
    }

    fn is_conflicted_incremental(&mut self, var: Var) -> Option<HashSet<Lit>> {
        // The check asks for a model where both polarities fire: the firing
        // condition of a polarity is a disjunction over the fire arbiters of
        // its implications. A single arbiter is passed as an assumption
        // directly; a larger disjunction needs a per-check guarded clause.
        // Per-check clauses are *not* retired eagerly — a unit clause per
        // check makes the backend re-simplify its whole clause database on
        // every check — they stay inert behind the never-again-assumed
        // guard until the next solver reboot sheds them.
        let mut assumptions = Vec::new();
        let mut guard = None;
        for lit in [Lit::positive(var), Lit::negative(var)] {
            let arbiters: Vec<_> = self.skolem[lit]
                .implications()
                .map(|cid| self.conflict_check.fire_arbiter(cid, lit, &self.allocator[cid]))
                .collect();
            if let [arbiter] = arbiters[..] {
                assumptions.push(!arbiter);
            } else {
                let guard =
                    *guard.get_or_insert_with(|| self.conflict_check.sat_solver.add_variable());
                let mut build = vec![!guard];
                build.extend(arbiters.into_iter().map(|arbiter| !arbiter));
                self.conflict_check.sat_solver.add_clause(&build);
            }
        }
        assumptions.extend(guard);
        // if the formula is satisfiable, there is a conflict
        let result = self.conflict_check.solve(&assumptions)?;
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

        // universal assignments of handled cases are excluded
        for case in &self.handled_cases {
            let encoded: Vec<S::Lit> = case.cube().iter().map(|&l| solver.lookup(!l)).collect();
            solver.add_clause(&encoded);
        }

        if exact {
            // add already determined skolem functions
            for cid in self.iter_implication_clauses() {
                let clause = &self.allocator[cid];
                trace!("exact check: function clause {clause}");
                let clause = clause.iter().map(|&l| solver.lookup(l)).collect::<Vec<_>>();
                solver.add_clause(&clause);
            }
            // add decided skolem functions
            for &lit in self.trail.iter_decisions() {
                let data = &self.vars[lit.var()];
                if data.scope.is_some() && data.is_universal(&self.prefix) {
                    // case assumptions are added as constants above
                    continue;
                }
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
                trace!("exact check: implication of {lit}: {clause}");
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
