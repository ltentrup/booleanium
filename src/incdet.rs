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
    datastructure::{heap::VarHeap, LitVec, VarVec},
    incdet::graph::Impl,
    literal::{filter_var, Lit, LitSlice, Var},
    qdimacs::FromQdimacs,
    QuantTy, SolverResult,
};
use std::{
    collections::{HashSet, VecDeque},
    mem,
    time::Instant,
};
use tracing::{debug, error, info, trace};

pub(crate) mod activity;
pub(crate) mod casesplit;
pub(crate) mod cegar;
pub(crate) mod certify;
pub(crate) mod conflict;
pub(crate) mod determinacy;
pub(crate) mod graph;
pub mod model;
pub(crate) mod propagation;
pub(crate) mod skolem;
pub(crate) mod stats;
pub(crate) mod vsids;
pub(crate) mod watch;

#[cfg(test)]
mod test;

/// The SAT solver used for the global conflict checks; selected by feature
/// flag (`cadical` takes precedence over `cryptominisat`, the default is
/// varisat).
#[cfg(feature = "cadical")]
type ConflictSolver = crate::sat::cadical::Cadical;
#[cfg(all(feature = "cryptominisat", not(feature = "cadical")))]
type ConflictSolver = crate::sat::cmsat::CryptoMiniSat;
#[cfg(not(any(feature = "cadical", feature = "cryptominisat")))]
type ConflictSolver = crate::sat::varisat::Varisat;

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
    /// Periodically delete long learnt clauses that are not registered as
    /// implication clauses, keeping propagation and the determinacy and
    /// conflict checks from slowing down as learnt clauses accumulate.
    pub clause_deletion: bool,
    /// Resolve conflicts by CEGAR rounds while they are effective: check
    /// whether the conflicting universal assignment has an existential
    /// response at all (immediate UNSAT if not) and record generalized,
    /// handled cases instead of learning clauses.
    pub cegar: bool,
    /// Once the search stalls, assume a universal literal (restricting all
    /// checks to the halved domain), solve the case with the full machinery
    /// while keeping all derived state, and exclude the closed case from
    /// the remaining search.
    pub case_splits: bool,
    /// Number of conflicts after which the search counts as stalled and a
    /// case split is attempted.
    pub case_split_threshold: u32,
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
        Self {
            constant_propagation: true,
            incremental_conflict_check: true,
            clause_deletion: true,
            cegar: true,
            case_splits: true,
            case_split_threshold: 5000,
            restarts: false,
        }
    }
}

/// Number of conflicts of the base Luby restart interval.
const RESTART_INTERVAL: u32 = 100;

/// Number of learnt clauses after which the next clause deletion runs.
const REDUCTION_INCREMENT: usize = 2000;

/// Number of global conflict checks after which the incremental
/// conflict-check solver is rebooted from the live state.
const CONFLICT_CHECK_REBOOT_INTERVAL: u32 = 512;

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
    /// activities of learnt clauses for the deletion policy
    clause_activity: activity::ClauseActivity,
    conflict_check: ConflictCheck<ConflictSolver>,
    dec_lvls: VarVec<Option<DecLvl>>,
    vsids: Vsids,
    /// number of matrix clauses present when solving started; clauses
    /// beyond this index are learnt
    original_clause_count: usize,
    /// for every literal, the original clauses containing it (static; used
    /// by the pure-literal rule)
    occurrences: LitVec<Vec<ClauseId>>,
    /// variables whose clauses changed state (an implication was
    /// registered, or a constant satisfied a clause), queued for a
    /// pure-literal check
    pure_queue: VecDeque<Var>,
    pure_queued: HashSet<Var>,
    /// learnt clauses that are candidates for deletion
    learnts: Vec<ClauseId>,
    /// state of the CEGAR extension
    cegar: cegar::Cegar,
    /// state of interleaved case splitting
    casesplits: casesplit::CaseSplits,
    /// handled universal regions (CEGAR responses and closed cases), in the
    /// order they were excluded from the conflict search
    handled_cases: Vec<casesplit::HandledCase>,
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

/// Result of one pure-literal propagation step.
enum PureStep {
    /// No pure literal in the queue.
    Nothing,
    /// A pure literal was assigned.
    Progress,
    /// The pure candidate is conflicted.
    Conflict(Conflict),
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
        self.occurrences.set_var_count(count);
        self.vsids.set_var_count(count);
        self.conflict_check.set_var_count(count);
        self.propagation.set_var_count(count);
    }

    /// Ensures that the outermost scope (index 0) exists. It is always
    /// existential and additionally holds the free variables, following the
    /// QDIMACS convention that free variables are existentially quantified
    /// at the outermost level.
    fn ensure_free_scope(&mut self) {
        if self.prefix.is_empty() {
            self.prefix.push(Scope {
                id: ScopeId(0),
                quantifier: QuantTy::Exists,
                variables: Vec::new(),
            });
        }
    }

    /// Binds a variable that occurs in the matrix but not in the prefix to
    /// the outermost existential scope.
    fn bind_free_variable(&mut self, var: Var) {
        self.ensure_free_scope();
        self.vars[var].scope = Some(ScopeId(0));
        self.prefix[0].variables.push(var);
    }

    fn _quantify(&mut self, quant: QuantTy, vars: &[Var]) {
        self.ensure_free_scope();
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
        // bind free variables to the outermost existential scope
        for lit in lits {
            let var = lit.var();
            if var.as_index() >= self.vars.get_var_count() {
                self.set_var_count(var.as_index() + 1);
            }
            if self.vars[var].scope.is_none() {
                self.bind_free_variable(var);
            }
        }
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
            self.allocator.lock(clause_id);
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
                // clauses added during solving are learnt and may be
                // deleted again
                self.learnts.push(clause_id);
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
                        .filter(|lit| self.vars[lit.var()].is_existential(&self.prefix))
                        .find(|l| self.dec_lvls[l.var()] == Some(max_lvl))
                        .expect("There is a literal with the provided decision level");
                    self.watches.add_watch(watch2, Watch { clause: clause_id });
                    self.skolem[watch1].add_implication(clause_id, max_lvl);
                    self.allocator.lock(clause_id);
                    self.propagation.add_and_set(
                        watch1.var(),
                        self.skolem[watch1].len() + self.skolem[!watch1].len(),
                    );
                    self.graph[watch1].push(Impl { clause: clause_id, dec_lvl: max_lvl });
                }
            }
        }
    }

    /// The clauses learnt during solving, in DIMACS numbering. Learnt
    /// clauses are resolvents of the matrix, so they remain valid for any
    /// extension of the matrix (used by the incremental solver to carry
    /// learning across solves).
    #[must_use]
    pub fn learnt_clauses(&self) -> Vec<Vec<i32>> {
        self.learnts
            .iter()
            .map(|&cid| self.allocator[cid].lits().iter().map(|l| l.to_dimacs()).collect())
            .collect()
    }

    /// Solves the QBF using incremental determinization.
    pub fn solve(&mut self) -> SolverResult {
        let instant = Instant::now();
        let result = self._solve();
        self.stats.global.solve_time = instant.elapsed();
        info!("\n{:#?}", self.stats);
        result
    }

    // the main solver loop reads best as one piece
    #[allow(clippy::too_many_lines)]
    fn _solve(&mut self) -> SolverResult {
        self.original_clause_count = self.allocator.len();
        for cid in self.allocator.ids().take(self.original_clause_count) {
            for &lit in self.allocator[cid].iter() {
                self.occurrences[lit].push(cid);
            }
        }
        let candidates: Vec<Var> = self
            .vars
            .iter()
            .filter(|(_, data)| data.scope.is_some() && data.is_existential(&self.prefix))
            .map(|(var, _)| var)
            .collect();
        for var in candidates {
            self.queue_pure_check(var);
        }
        // the outermost scope may be an empty placeholder for free variables
        let blocks = self.prefix.iter().filter(|scope| !scope.variables.is_empty()).count();
        if blocks > 2 {
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
        let mut next_reduction = REDUCTION_INCREMENT;
        let mut last_reboot = 0;
        let mut conflicts_at_last_case = 0;
        loop {
            if let Some(conflict) = self.propagate() {
                debug!("{conflict:?}");
                if let Some(result) = self.resolve_conflict(&conflict) {
                    return result;
                }
                conflicts_since_restart += 1;
                continue;
            }
            if initial.take().is_some() {
                info!("number of initial deterministic vars: {}", self.trail.len());
            }
            if self.options.case_splits && self.reassume_cases() {
                continue;
            }
            if self.options.clause_deletion && self.learnts.len() >= next_reduction {
                self.reduce_learnts();
                next_reduction += REDUCTION_INCREMENT;
            }
            if self.options.incremental_conflict_check
                && self.stats.skolem.global_conflict_checks - last_reboot
                    >= CONFLICT_CHECK_REBOOT_INTERVAL
            {
                self.reboot_conflict_check();
                last_reboot = self.stats.skolem.global_conflict_checks;
            }
            if self.options.case_splits
                && self.stats.global.conflicts - conflicts_at_last_case
                    >= self.options.case_split_threshold
            {
                conflicts_at_last_case = self.stats.global.conflicts;
                match self.open_case() {
                    casesplit::CaseAction::Assumed => continue,
                    casesplit::CaseAction::DomainEmpty => return SolverResult::Satisfiable,
                    casesplit::CaseAction::NoUniversals => self.options.case_splits = false,
                }
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
            // Pure literals are assigned before decisions: their minimal
            // function is optimal, so assigning it loses nothing (see
            // `pure_literal`).
            match self.pure_literal_step() {
                PureStep::Progress => continue,
                PureStep::Conflict(conflict) => {
                    if let Some(result) = self.resolve_conflict(&conflict) {
                        return result;
                    }
                    conflicts_since_restart += 1;
                    continue;
                }
                PureStep::Nothing => {}
            }
            let Some(var) = self.next_decision_variable() else {
                if self.casesplits_active() {
                    // all existential variables are assigned within the
                    // active case: close it and continue on the rest
                    self.close_cases();
                    continue;
                }
                break;
            };
            self.stats.global.decisions += 1;
            assert!(!self.assignment.is_assigned(var));

            // Note: deciding the polarity with the *non-empty* implication
            // set when the other side is empty (a "one-sided function rule"
            // yielding the natural gate function of one-sidedly encoded
            // circuits) was benchmarked and rejected: it did not help the
            // circuit instances and slowed random instances by an order of
            // magnitude.
            // Phase choice: follow the most recently recorded CEGAR
            // response where it assigns the variable (the response is a
            // winning move for the current search region, so deciding
            // consistently with it avoids re-conflicting there), and
            // default the variable to true otherwise. The trail literal is
            // the *negation* of the intended default: a decided literal
            // holds only when one of its implications fires. Measured
            // alternatives (each worse in suite aggregate): the structural
            // rule alone (assign the side with fewer implication literals
            // — the previous default, 1.6x slower), the structural rule as
            // the fallback instead of default-true, default-true alone,
            // and gating the response phase on implication counts.
            let decision = match self.cegar.response_phase(var) {
                Some(false) => Lit::positive(var),
                Some(true) | None => Lit::negative(var),
            };
            trace!("decide {decision}");
            // check if the decision leads to a conflict
            if let Some(assignment) = self.is_conflicted(var) {
                trace!("{} is conflicted", var);
                if let Some(result) = self.resolve_conflict(&Conflict { var, assignment }) {
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
            // variables that occur neither in the prefix nor in the matrix
            // remain unbound and are ignored
            .filter(|(_, data)| data.scope.is_some() && data.is_existential(&self.prefix))
            .for_each(|(var, _)| self.vsids.add(var));
    }

    pub(crate) fn next_decision_variable(&self) -> Option<Var> {
        self.vsids.peek()
    }

    fn queue_pure_check(&mut self, var: Var) {
        if self.pure_queued.insert(var) {
            self.pure_queue.push_back(var);
        }
    }

    /// Pops pure-check candidates until one is pure, returning its pure
    /// literal.
    fn pop_pure_literal(&mut self) -> Option<(Var, Lit)> {
        while let Some(var) = self.pure_queue.pop_front() {
            self.pure_queued.remove(&var);
            if self.assignment.is_assigned(var) {
                continue;
            }
            let data = &self.vars[var];
            debug_assert!(data.scope.is_some() && data.is_existential(&self.prefix));
            if data.scope.is_none() || data.is_universal(&self.prefix) {
                continue;
            }
            if let Some(lit) = self.pure_literal(var) {
                return Some((var, lit));
            }
        }
        None
    }

    /// Assigns the next pure literal from the queue, if any.
    fn pure_literal_step(&mut self) -> PureStep {
        let Some((var, lit)) = self.pop_pure_literal() else {
            return PureStep::Nothing;
        };
        self.stats.skolem.pure_vars += 1;
        if self.skolem[lit].len() == 0 {
            // no implications at all: the function is the constant ¬lit
            // (the classic pure-literal rule), which cascades through the
            // constant propagation
            match self.propagate_constant(!lit) {
                Some(conflict) => PureStep::Conflict(conflict),
                None => PureStep::Progress,
            }
        } else if let Some(assignment) = self.is_conflicted(var) {
            trace!("pure {} is conflicted", var);
            PureStep::Conflict(Conflict { var, assignment })
        } else {
            trace!("assigning pure literal {lit}");
            self.assign_and_propagate(lit, true, false);
            PureStep::Progress
        }
    }

    /// The pure-literal rule: `lit` is pure if every original clause
    /// containing it is either registered as an implication clause for
    /// `lit` or satisfied by a constant. The variable can then take the
    /// minimal function "lit iff one of its implications fires" without
    /// loss: the clauses containing `lit` are satisfied by construction,
    /// every other clause profits from `¬lit` holding as often as
    /// possible, and clauses without the variable are unaffected — any
    /// winning strategy can be rewritten to this function.
    fn pure_literal(&self, var: Var) -> Option<Lit> {
        for lit in [Lit::positive(var), Lit::negative(var)] {
            let implications: HashSet<ClauseId> = self.skolem[lit].implications().collect();
            let pure = self.occurrences[lit].iter().all(|&cid| {
                implications.contains(&cid)
                    || self.allocator[cid]
                        .iter()
                        .any(|&l| self.assignment.constant_value(l) == Some(true))
            });
            if pure {
                return Some(lit);
            }
        }
        None
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
            match self.has_unique_consequence(var) {
                determinacy::Determinacy::Undetermined => {
                    debug_assert!(!self.propagation.contained(var));
                    continue;
                }
                determinacy::Determinacy::Constant(lit) => {
                    trace!("{} is forced constant", var);
                    if let Some(conflict) = self.propagate_constant(lit) {
                        return Some(conflict);
                    }
                    continue;
                }
                determinacy::Determinacy::Deterministic => {}
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
        // the clauses satisfied by the constant no longer block purity of
        // their other variables
        for idx in 0..self.occurrences[lit].len() {
            let cid = self.occurrences[lit][idx];
            for i in 0..self.allocator[cid].lits().len() {
                let other = self.allocator[cid].lits()[i].var();
                let data = &self.vars[other];
                if data.scope.is_some()
                    && data.is_existential(&self.prefix)
                    && !self.assignment.is_assigned(other)
                    && self.pure_queued.insert(other)
                {
                    self.pure_queue.push_back(other);
                }
            }
        }
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
        // clauses to lock in the allocator (the closure below already
        // borrows the allocator immutably)
        let mut locked = Vec::new();
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
                if self.pure_queued.insert(lit.var()) {
                    self.pure_queue.push_back(lit.var());
                }
                locked.push(watch.clause);
                self.propagation
                    .add_and_set(lit.var(), self.skolem[lit].len() + self.skolem[!lit].len());
                // add the propagation reason to implication graph
                self.graph[lit]
                    .push(Impl { clause: watch.clause, dec_lvl: self.trail.decision_level() });
                true
            });
            self.watches[lit] = watches;
        }
        for cid in locked {
            self.allocator.lock(cid);
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
            let var = assigned_lit.var();
            self.assignment.unassign(var);
            self.dec_lvls[var] = None;
            if self.vars[var].scope.is_some() && self.vars[var].is_existential(&self.prefix) {
                self.vsids.add(var);
            }
            unassigned.push(var);
        });
        self.prune_cases_on_backtrack(lvl);
        self.skolem.backtrack_to(lvl, |cid| self.allocator.unlock(cid));
        self.graph.backtrack_to(lvl);
        self.conflict_check.backtrack_to(lvl);
        // Unassigned variables that still have implication clauses may still
        // be uniquely determined, so their determinacy checks are re-queued;
        // they are also pure-literal candidates again.
        for var in unassigned {
            self.requeue_determinacy_check(var);
            let data = &self.vars[var];
            if data.scope.is_some() && data.is_existential(&self.prefix) {
                self.queue_pure_check(var);
            }
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

    /// Deletes the less active half of the learnt clauses that are neither
    /// registered as implication clauses nor binary (activity ties are
    /// broken towards deleting longer clauses).
    fn reduce_learnts(&mut self) {
        let mut candidates: Vec<(f64, usize, ClauseId)> = self
            .learnts
            .iter()
            .copied()
            .filter(|&cid| !self.allocator.is_locked(cid) && self.allocator[cid].lits().len() > 2)
            .map(|cid| (self.clause_activity.get(cid), self.allocator[cid].lits().len(), cid))
            .collect();
        candidates.sort_by(|(a1, len1, _), (a2, len2, _)| a1.total_cmp(a2).then(len2.cmp(len1)));
        candidates.truncate(candidates.len() / 2);
        if candidates.is_empty() {
            return;
        }
        let deleted: HashSet<ClauseId> = candidates.into_iter().map(|(_, _, cid)| cid).collect();
        for &cid in &deleted {
            self.allocator.delete(cid);
            self.clause_activity.remove(cid);
        }
        self.learnts.retain(|cid| !deleted.contains(cid));
        self.clauses.retain(|cid| !deleted.contains(cid));
        self.watches.remove_clauses(&deleted);
        self.stats.global.deleted_clauses += u32::try_from(deleted.len()).unwrap();
        debug!("deleted {} learnt clauses", deleted.len());
    }

    pub(crate) fn handle_conflict(&mut self, conflict: &Conflict) -> Option<SolverResult> {
        if self.stats.global.conflicts % 1024 == 0 {
            info!(
                "progress: {} conflicts, {} decisions, {} learnt clauses, {} determinacy checks, {} cegar cases",
                self.stats.global.conflicts,
                self.stats.global.decisions,
                self.stats.global.added_clauses,
                self.stats.skolem.local_det_checks,
                self.stats.cegar.cases,
            );
        }
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
        if self.conflicted {
            // the learnt clause contained only universal literals (e.g. the
            // negation of a case assumption) and reduced to the empty clause
            return Some(SolverResult::Unsatisfiable);
        }
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
