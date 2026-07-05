//! Implementation of the incremental determinization algorithm.

use self::{
    conflict::{analysis::ConflictAnalysis, check::ConflictCheck},
    graph::ImplGraph,
    propagation::{
        assignment::Assignment,
        trail::{DecLvl, Trail},
    },
    skolem::Skolem,
    stats::Statistics,
    vsids::Vsids,
    watch::{Watch, WatchList},
};
use crate::{
    clause::alloc::{Allocator, ClauseId},
    datastructure::{heap::VarHeap, VarVec},
    incdet::graph::Impl,
    literal::{filter_var, Lit, LitSlice, Var},
    qdimacs::FromQdimacs,
    sat::varisat::Varisat,
    QuantTy, SolverResult,
};
use std::{
    collections::{HashSet, VecDeque},
    mem,
    time::Instant,
};
use tracing::{debug, error, info, trace};

pub(crate) mod conflict;
pub(crate) mod determinacy;
pub(crate) mod graph;
pub(crate) mod propagation;
pub(crate) mod skolem;
pub(crate) mod stats;
pub(crate) mod vsids;
pub(crate) mod watch;

#[cfg(test)]
mod test;

/// Configuration of the incremental determinization algorithm.
///
/// The default enables all features; the options mainly exist to make it
/// possible to test and benchmark the features in isolation.
#[derive(Debug, Clone, Copy)]
pub struct Options {
    /// Propagate constant Skolem functions eagerly. Constants admit cheaper
    /// determinacy and conflict checks than general Skolem functions.
    pub constant_propagation: bool,
    /// Reuse a single incremental SAT solver for the global conflict checks
    /// instead of rebuilding a solver for every check.
    pub incremental_conflict_check: bool,
    /// Restart the search (backtrack to the root level, keeping all learnt
    /// clauses and variable activities) on a Luby schedule.
    ///
    /// Disabled by default: unlike in SAT solvers, a restart discards the
    /// level-tagged implication structure whose reconstruction requires
    /// SAT-based determinacy and conflict checks rather than cheap unit
    /// propagation, and this cost outweighed the variance reduction on all
    /// benchmarked instance families.
    pub restarts: bool,
}

impl Default for Options {
    fn default() -> Self {
        Self { constant_propagation: true, incremental_conflict_check: true, restarts: false }
    }
}

/// Number of conflicts of the base Luby restart interval.
const RESTART_INTERVAL: u32 = 100;

/// The Luby sequence (1, 1, 2, 1, 1, 2, 4, ...) for `i >= 1`.
fn luby(mut i: u32) -> u32 {
    loop {
        let bits = 32 - i.leading_zeros();
        if i == (1 << bits) - 1 {
            return 1 << (bits - 1);
        }
        i -= (1 << (bits - 1)) - 1;
    }
}

#[derive(Debug, Default)]
pub struct IncDet {
    options: Options,
    vars: VarVec<VarData>,
    prefix: Vec<Scope>,
    clauses: Vec<ClauseId>,
    allocator: Allocator,
    skolem: Skolem,
    // queue for next propagation tests
    propagation: VarHeap<usize>,
    constant_propagation: VecDeque<Lit>,
    assignment: Assignment,
    trail: Trail,
    watches: WatchList,
    graph: ImplGraph,
    conflict_analysis: ConflictAnalysis,
    conflict_check: ConflictCheck<Varisat>,
    dec_lvls: VarVec<Option<DecLvl>>,
    vsids: Vsids,
    /// set to true if the empty clause was added
    conflicted: bool,
    stats: Statistics,
}

#[derive(Debug, Clone, Default)]
struct VarData {
    scope: Option<ScopeId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ScopeId(usize);

#[derive(Debug, Clone)]
struct Scope {
    id: ScopeId,
    quantifier: QuantTy,
    variables: Vec<Var>,
}

#[derive(Debug, Clone)]
pub(crate) struct Conflict {
    var: Var,
    assignment: HashSet<Lit>,
}

impl FromQdimacs for IncDet {
    fn set_num_variables(&mut self, variables: u32) {
        self.set_var_count(variables.try_into().unwrap());
    }

    fn set_num_clauses(&mut self, clauses: u32) {
        self.allocator.reserve(clauses);
    }

    fn quantify(&mut self, quant: QuantTy, vars: &[Var]) {
        self._quantify(quant, vars);
    }

    fn add_clause(&mut self, lits: &[Lit]) {
        self._add_clause(lits);
    }
}

impl IncDet {
    /// Creates a solver with the provided configuration.
    #[must_use]
    pub fn with_options(options: Options) -> Self {
        Self { options, ..Self::default() }
    }

    #[cfg(test)]
    fn from_qcnf(qcnf: &crate::qcnf::QCNF) -> Self {
        Self::from_qcnf_with_options(qcnf, Options::default())
    }

    /// Creates a solver with the provided configuration and loads the
    /// given formula.
    #[must_use]
    pub fn from_qcnf_with_options(qcnf: &crate::qcnf::QCNF, options: Options) -> Self {
        let mut solver = Self::with_options(options);
        for (qty, vars) in &qcnf.prefix {
            solver._quantify(*qty, vars);
        }
        for clause in &qcnf.matrix {
            solver._add_clause(clause);
        }
        solver
    }

    fn set_var_count(&mut self, count: usize) {
        self.vars.set_var_count(count);
        self.skolem.set_var_count(count);
        self.assignment.set_var_count(count);
        self.watches.set_var_count(count);
        self.graph.set_var_count(count);
        self.dec_lvls.set_var_count(count);
        self.vsids.set_var_count(count);
        self.conflict_check.set_var_count(count);
        self.propagation.set_var_count(count);
    }

    fn _quantify(&mut self, quant: QuantTy, vars: &[Var]) {
        let id = match self.prefix.last_mut() {
            Some(scope) if scope.quantifier == quant => {
                scope.variables.extend_from_slice(vars);
                scope.id
            }
            _ => {
                let id = ScopeId(self.prefix.len());
                let scope = Scope { id, quantifier: quant, variables: vars.into() };
                self.prefix.push(scope);
                id
            }
        };
        for &var in vars {
            if var.as_index() >= self.vars.get_var_count() {
                self.set_var_count(var.as_index() + 1);
            }
            // let var_data = self.vars.get_or_default(var);
            let var_data = &mut self.vars[var];
            let other = var_data.scope.get_or_insert(id);
            if *other != id {
                // variable is bound twice, remove it from outer scope
                self.prefix[other.0].variables.retain(|&other| other != var);
                *other = id;
            }
        }
    }

    fn _add_clause(&mut self, lits: &[Lit]) {
        debug!("Add clause: {}", LitSlice::from(lits));
        assert!(
            lits.iter().all(|&l| self.vars.get(l.var()).map_or(false, |data| data.scope.is_some())),
            "unbound variables are not supported"
        );
        let mut lits = Vec::from(lits);
        lits.sort_unstable();
        lits.dedup();
        if lits.iter().zip(lits.iter().skip(1)).any(|(&left, &right)| left == !right) {
            // Detected tautology clause, do not add to matrix.
            // Note: as literals are deduplicated and sorted by variable index,
            // literals of opposing signs have to be consecutive in the clause.
            return;
        }

        // universal reduction
        if let Some(max_scope) = lits
            .iter()
            .filter(|lit| self.vars[lit.var()].is_existential(&self.prefix))
            .map(|lit| self.vars[lit.var()].scope())
            .max()
        {
            // remove universal literals that are bound after every existential variable
            lits.retain(|lit| self.vars[lit.var()].scope() <= max_scope);
        } else {
            // no existential variables
            tracing::warn!("empty clause was added, instance is unsatisfiable");
            self.conflicted = true;
        }

        let clause_id = self.allocator.add(&lits);

        // check if there is only one existential variable
        let mut singleton = None;
        let mut no_universals = true;
        for lit in &lits {
            if self.vars[lit.var()].is_existential(&self.prefix) {
                match singleton {
                    None => singleton = Some(lit),
                    Some(_) => {
                        // there are two existential variables
                        singleton = None;
                        break;
                    }
                }
            } else {
                no_universals = false;
            }
        }
        if let Some(&lit) = singleton {
            self.skolem[lit].add_implication(clause_id, DecLvl::ROOT);
            if self.options.constant_propagation && no_universals {
                self.constant_propagation.push_back(lit);
            } else {
                self.propagation
                    .add_and_set(lit.var(), self.skolem[lit].len() + self.skolem[!lit].len());
            }
            self.graph[lit].push(Impl { clause: clause_id, dec_lvl: DecLvl::ROOT });
        } else {
            // TODO: handle constant functions
            self.clauses.push(clause_id);
            if self.watches.enabled() {
                let mut unassigned = lits
                    .iter()
                    .filter(|lit| self.vars[lit.var()].is_existential(&self.prefix))
                    .filter(|l| !self.assignment.is_assigned(l.var()));
                let watch1 = *unassigned.next().expect("there is at least one unassigned lit");
                self.watches.add_watch(watch1, Watch { clause: clause_id });
                if let Some(&watch2) = unassigned.next() {
                    self.watches.add_watch(watch2, Watch { clause: clause_id });
                } else {
                    // select an arbitrary existential literal from largest decision level
                    let max_lvl = lits
                        .iter()
                        .filter(filter_var(watch1.var()))
                        .filter(|lit| self.vars[lit.var()].is_existential(&self.prefix))
                        .filter_map(|l| self.dec_lvls[l.var()])
                        .max()
                        .expect("there is at least one assigned existential literal");
                    let watch2 = *lits
                        .iter()
                        .find(|l| self.dec_lvls[l.var()] == Some(max_lvl))
                        .expect("There is a literal with the provided decision level");
                    self.watches.add_watch(watch2, Watch { clause: clause_id });
                    self.skolem[watch1].add_implication(clause_id, max_lvl);
                    self.propagation.add_and_set(
                        watch1.var(),
                        self.skolem[watch1].len() + self.skolem[!watch1].len(),
                    );
                    self.graph[watch1].push(Impl { clause: clause_id, dec_lvl: max_lvl });
                }
            }
        }
    }

    /// Solves the QBF using incremental determinization.
    pub fn solve(&mut self) -> SolverResult {
        let instant = Instant::now();
        let result = self._solve();
        self.stats.global.solve_time = instant.elapsed();
        info!("\n{:#?}", self.stats);
        result
    }

    fn _solve(&mut self) -> SolverResult {
        if self.prefix.len() > 2 {
            error!("Only 2QBF is currently supported");
            return SolverResult::Unknown;
        }
        if self.conflicted {
            return SolverResult::Unsatisfiable;
        }
        self.build_watchlist();
        self.build_vsids_heap();
        let mut initial = Some(());
        let mut conflicts_since_restart = 0;
        let mut restart_number = 1;
        loop {
            if let Some(conflict) = self.propagate() {
                debug!("{conflict:?}");
                if let Some(result) = self.handle_conflict(&conflict) {
                    return result;
                }
                conflicts_since_restart += 1;
                continue;
            }
            if initial.take().is_some() {
                info!("number of initial deterministic vars: {}", self.trail.len());
            }
            if self.options.restarts
                && conflicts_since_restart >= RESTART_INTERVAL * luby(restart_number)
                && !self.trail.decision_level().is_root()
            {
                debug!("restart {restart_number}");
                self.stats.global.restarts += 1;
                restart_number += 1;
                conflicts_since_restart = 0;
                self.backtrack_to(DecLvl::ROOT);
                continue;
            }
            let Some(var) = self.next_decision_variable() else {
                break;
            };
            self.stats.global.decisions += 1;
            assert!(!self.assignment.is_assigned(var));
            let neg_count = self.skolem[Lit::negative(var)].lit_count(&self.allocator);
            let pos_count = self.skolem[Lit::positive(var)].lit_count(&self.allocator);
            let decision =
                if neg_count <= pos_count { Lit::negative(var) } else { Lit::positive(var) };
            trace!(
                "decide {decision} (neg: {}/{}, pos: {}/{})",
                neg_count,
                self.skolem[Lit::negative(var)].len(),
                pos_count,
                self.skolem[Lit::positive(var)].len()
            );
            // check if the decision leads to a conflict
            if let Some(assignment) = self.is_conflicted(var) {
                trace!("{} is conflicted", var);
                if let Some(result) = self.handle_conflict(&Conflict { var, assignment }) {
                    return result;
                }
                conflicts_since_restart += 1;
                continue;
            }
            // TODO: is_constant
            self.assign_and_propagate(decision, true, false);
        }
        SolverResult::Satisfiable
    }

    fn build_watchlist(&mut self) {
        self.watches.clear();
        self.watches.set_enabled();
        for &cid in &self.clauses {
            let clause = &self.allocator[cid];
            let mut iter = clause
                .lits()
                .iter()
                .filter(|lit| self.vars[lit.var()].is_existential(&self.prefix));
            let watch1 = *iter.next().expect("every clause has at least 2 existential variables");
            let watch2 = *iter.next().expect("every clause has at least 2 existential variables");
            self.watches.add_watch(watch1, Watch { clause: cid });
            self.watches.add_watch(watch2, Watch { clause: cid });
        }
    }

    fn build_vsids_heap(&mut self) {
        self.vars
            .iter()
            .filter(|(_, data)| data.is_existential(&self.prefix))
            .for_each(|(var, _)| self.vsids.add(var));
    }

    pub(crate) fn next_decision_variable(&self) -> Option<Var> {
        self.vsids.peek()
    }

    fn propagate(&mut self) -> Option<Conflict> {
        loop {
            // constants are the cheapest propagation, handle them first
            if let Some(lit) = self.constant_propagation.pop_front() {
                if let Some(conflict) = self.propagate_constant(lit) {
                    return Some(conflict);
                }
                continue;
            }
            let Some(var) = self.propagation.pop() else {
                return None;
            };
            if self.assignment.is_assigned(var) {
                continue;
            }
            if !self.has_unique_consequence(var) {
                debug_assert!(!self.propagation.contained(var));
                continue;
            }
            trace!("{} has unique consquence", var);
            if let Some(assignment) = self.is_conflicted(var) {
                trace!("{} is conflicted", var);
                return Some(Conflict { var, assignment });
            }
            trace!("{} is deterministic", var);
            let lit =
                if self.skolem[Lit::positive(var)].len() <= self.skolem[Lit::negative(var)].len() {
                    Lit::positive(var)
                } else {
                    Lit::negative(var)
                };
            self.assign_and_propagate(lit, false, false);
        }
    }

    /// Handles a literal that is forced to be constant true, i.e., its
    /// variable has the constant Skolem function `lit.is_positive()`.
    fn propagate_constant(&mut self, lit: Lit) -> Option<Conflict> {
        let var = lit.var();
        if self.assignment.is_assigned(var) {
            return match self.assignment.constant_value(lit) {
                // already assigned to the same constant
                Some(true) => None,
                // two contradicting constants; the conflict does not depend
                // on any universal assignment
                Some(false) => Some(Conflict { var, assignment: HashSet::new() }),
                None => {
                    // cannot happen: implications are only added to unassigned
                    // variables, so the constant would have been queued before
                    // the variable was assigned a function
                    debug_assert!(false, "constants are queued before functions are assigned");
                    None
                }
            };
        }
        trace!("{lit} is constant");
        self.stats.skolem.constant_propagations += 1;
        if let Some(assignment) = self.is_conflicted(var) {
            trace!("{} is conflicted", var);
            return Some(Conflict { var, assignment });
        }
        self.assign_and_propagate(lit, false, true);
        None
    }

    // update internal representation to reflect that `lit` is assigned.
    pub(crate) fn assign_and_propagate(&mut self, lit: Lit, is_decision: bool, is_constant: bool) {
        if is_decision {
            self.trail.add_decision(lit);
        } else {
            self.trail.push(lit);
        }
        if is_constant {
            self.assignment.assign_constant(lit);
        } else {
            self.assignment.assign_function(lit);
        }
        self.vsids.remove(lit.var());
        self.add_definition_to_conflict_check(lit, is_decision);
        self.propagate_function(lit.var());
    }

    /// Use watchlist to determine more implications
    fn propagate_function(&mut self, var: Var) {
        debug!("propagate function {var}");
        self.stats.skolem.function_propagations += 1;
        self.dec_lvls[var] = Some(self.trail.decision_level());
        for lit in [Lit::positive(var), Lit::negative(var)] {
            let mut watches = mem::take(&mut self.watches[lit]);
            watches.retain(|watch: &Watch| {
                let clause = &self.allocator[watch.clause];
                trace!("Propagate {var} in clause {clause}");
                if clause.iter().any(|&l| self.assignment.constant_value(l) == Some(true)) {
                    // the clause is globally satisfied by a constant
                    // (constants are only assigned at the root level),
                    // no implications can be derived from it
                    return true;
                }
                // iterate over existential literals that are not watched
                let mut iter = clause
                    .lits()
                    .iter()
                    .filter(|l| self.vars[l.var()].is_existential(&self.prefix))
                    .filter(|l| !self.assignment.is_assigned(l.var()))
                    .filter(|l| l.var() != var)
                    .filter(|&&l| self.watches[l].iter().all(|w| w.clause != watch.clause));
                if let Some(&l) = iter.next() {
                    // new watched literal
                    self.watches[l].push(Watch { clause: watch.clause });
                    trace!("New watched lit {l} in clause {}", clause);
                    return false;
                }
                // there is no other existential literal to watch for,
                // thus, this is an implication clause for the remaining variable
                let Some(&lit) = clause
                .lits()
                .iter()
                .filter(|l| self.vars[l.var()].is_existential(&self.prefix))
                .filter(|l| !self.assignment.is_assigned(l.var()))
                .filter(|l| l.var() != var)
                .find(|&&l| self.watches[l].iter().any(|w| w.clause == watch.clause))
                else {
                    // all literals are assigned
                    return true;
                };
                trace!("New implication clause for {}: {}", lit, clause);

                if self.options.constant_propagation
                    && self.trail.decision_level().is_root()
                    && clause
                        .iter()
                        .filter(|&&l| l != lit)
                        .all(|&l| self.assignment.constant_value(l) == Some(false))
                {
                    // all other literals are constant false, so `lit` is
                    // forced to be constant true
                    self.constant_propagation.push_back(lit);
                }
                self.skolem[lit].add_implication(watch.clause, self.trail.decision_level());
                self.propagation
                    .add_and_set(lit.var(), self.skolem[lit].len() + self.skolem[!lit].len());
                // add the propagation reason to implication graph
                self.graph[lit]
                    .push(Impl { clause: watch.clause, dec_lvl: self.trail.decision_level() });
                true
            });
            self.watches[lit] = watches;
        }
    }

    fn iter_implication_clauses(&self) -> impl Iterator<Item = ClauseId> + '_ {
        self.trail.iter().flat_map(|&lit| {
            [lit, lit.negated()].into_iter().flat_map(|lit| self.skolem[lit].implications())
        })
    }

    pub(crate) fn backtrack_to(&mut self, lvl: DecLvl) {
        let mut unassigned = Vec::new();
        self.trail.backtrack_to(lvl, |assigned_lit| {
            self.assignment.unassign(assigned_lit.var());
            self.dec_lvls[assigned_lit.var()] = None;
            self.vsids.add(assigned_lit.var());
            unassigned.push(assigned_lit.var());
        });
        self.skolem.backtrack_to(lvl);
        self.graph.backtrack_to(lvl);
        self.conflict_check.backtrack_to(lvl);
        // Unassigned variables that still have implication clauses may still
        // be uniquely determined, so their determinacy checks are re-queued.
        for var in unassigned {
            self.requeue_determinacy_check(var);
        }
    }

    /// Queues the determinacy check for `var` if there are implication
    /// clauses for one of its literals.
    fn requeue_determinacy_check(&mut self, var: Var) {
        let implications =
            self.skolem[Lit::positive(var)].len() + self.skolem[Lit::negative(var)].len();
        if implications > 0 {
            self.propagation.add_and_set(var, implications);
        }
    }

    pub(crate) fn handle_conflict(&mut self, conflict: &Conflict) -> Option<SolverResult> {
        if self.trail.decision_level().is_root() {
            return Some(SolverResult::Unsatisfiable);
        }
        let Ok(backtrack_to) = self.analyze(conflict) else {
                    return Some( SolverResult::Unsatisfiable);
                };
        debug!("conflict analysis: backtrack to {backtrack_to:?}");
        self.backtrack_to(backtrack_to);
        let clause = self.conflict_analysis.clause().to_owned();
        self._add_clause(&clause);
        self.stats.global.added_clauses += 1;
        assert!(!self.conflicted, "empty clause cannot be added through conflict analysis");
        // the learnt clause constrains the conflicted variable further, so it
        // may have become uniquely determined
        if !self.assignment.is_assigned(conflict.var) {
            self.requeue_determinacy_check(conflict.var);
        }
        None
    }
}

impl From<Lit> for varisat::Lit {
    fn from(lit: Lit) -> Self {
        varisat::Lit::from_dimacs(lit.to_dimacs().try_into().unwrap())
    }
}

impl From<varisat::Lit> for Lit {
    fn from(vlit: varisat::Lit) -> Self {
        Lit::from_dimacs(vlit.to_dimacs().try_into().unwrap())
    }
}

impl VarData {
    fn scope(&self) -> ScopeId {
        self.scope.expect("all variables are bound")
    }

    fn is_existential(&self, prefix: &[Scope]) -> bool {
        let scope = &prefix[self.scope().0];
        scope.quantifier == QuantTy::Exists
    }

    fn is_universal(&self, prefix: &[Scope]) -> bool {
        !self.is_existential(prefix)
    }
}
