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

/// Number of handled cases beyond which a monotone extension gives up on
/// re-verifying the retained regions (a rebuild is cheaper than the SAT
/// calls).
const MAX_REVERIFIED_CASES: usize = 64;

/// Number of assumption-violation CEGAR rounds per query before the query
/// aborts to the throwaway fallback (violations make exclusion-only
/// progress; the fallback's full machinery learns clauses instead).
const QUERY_VIOLATION_BUDGET: u32 = 8;

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
    /// the matrix clauses (as opposed to learnt resolvents): the clauses
    /// present when solving started plus every clause added by a monotone
    /// extension ([`IncDet::extend_and_resolve`]) — an explicit list, since
    /// extension clauses arrive after learnt clauses in the allocator
    originals: Vec<ClauseId>,
    /// for every literal, the original clauses containing it (static; used
    /// by the pure-literal rule)
    occurrences: LitVec<Vec<ClauseId>>,
    /// variables whose clauses changed state (an implication was
    /// registered, or a constant satisfied a clause), queued for a
    /// pure-literal check
    pure_queue: VecDeque<Var>,
    pure_queued: HashSet<Var>,
    /// pure literals assigned at the root level. Root assignments are
    /// permanent, and pure assignments are winnability-preserving
    /// *choices* w.r.t. the matrix at assignment time — a later monotone
    /// extension stays sound only while no added clause contains one of
    /// these literals (see [`IncDet::extend_and_resolve`])
    root_pure_lits: Vec<Lit>,
    /// the existential constant assumptions of the active query
    /// ([`IncDet::resolve_with_assumptions`]); sticky like committed case
    /// assumptions: re-assumed after every backtrack below their level
    query_assumptions: Vec<Lit>,
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
    /// a winning move for the universal player, recorded when
    /// unsatisfiability is concluded: a partial universal assignment such
    /// that no extension has an existential response (valid for prefixes
    /// with the universal block first)
    unsat_witness: Option<Vec<Lit>>,
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

/// Result of one query-assumption (re-)assumption step.
enum QueryStep {
    /// All query assumptions hold (assumed or satisfied by constants).
    Nothing,
    /// An assumption was assumed; propagation must run before the next.
    Assumed,
    /// Assuming the constant is violated by a firing implication clause
    /// of the opposite polarity.
    Conflict(Conflict),
    /// The assumption variable is forced to the opposite constant at the
    /// root: no strategy with the assumed constant exists.
    Unsat,
    /// The fast path cannot attribute the state (the assumption variable
    /// acquired a function or a choice-based constant mid-query); the
    /// caller falls back to a fresh throwaway query.
    Abort,
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

    /// Normalizes a clause for the matrix: binds free variables to the
    /// outermost existential scope, sorts, deduplicates, drops tautologies
    /// (`None`), and applies universal reduction. A clause without
    /// existential literals concludes unsatisfiability (`conflicted` set,
    /// witness recorded) and is returned as-is.
    fn preprocess_clause(&mut self, lits: &[Lit]) -> Option<Vec<Lit>> {
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
            return None;
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
            // No existential variables: the clause consists of universal
            // literals only (possibly none), so the universal player wins
            // by falsifying it. The clause is matrix-implied (an original
            // clause or a learnt resolvent), so this is a winning move.
            tracing::warn!("clause without existential literals, instance is unsatisfiable");
            self.conflicted = true;
            self.unsat_witness = Some(lits.iter().map(|&l| !l).collect());
        }
        Some(lits)
    }

    fn _add_clause(&mut self, lits: &[Lit]) {
        debug!("Add clause: {}", LitSlice::from(lits));
        let Some(lits) = self.preprocess_clause(lits) else {
            return;
        };
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

    /// Records the universal part of a conflicting assignment as the
    /// winning move of the universal player.
    pub(crate) fn record_unsat_witness(&mut self, conflicting: &HashSet<Lit>) {
        let witness = conflicting
            .iter()
            .filter(|l| {
                let data = &self.vars[l.var()];
                data.scope.is_some() && data.is_universal(&self.prefix)
            })
            .copied()
            .collect();
        self.unsat_witness = Some(witness);
    }

    /// A winning move for the universal player of an unsatisfiable
    /// instance: a partial assignment of the universal variables (DIMACS
    /// literals) such that no extension admits an existential response.
    /// Only meaningful for prefixes with the universal block first (for
    /// ∃∀ prefixes the universal player needs a strategy, not a move).
    /// After an assumption query ([`IncDet::resolve_with_assumptions`])
    /// the move refutes the instance *under the query assumptions*.
    ///
    /// The recorded candidate is heuristic — pure-literal assignments are
    /// winnability-preserving *choices* rather than pointwise-forced
    /// values, so a conflict derived through them proves
    /// unsatisfiability without its assignment necessarily being
    /// unanswerable — and is therefore verified with one SAT call before
    /// being exposed.
    #[must_use]
    pub fn unsat_witness(&self) -> Option<Vec<i32>> {
        use crate::sat::{LookupSolver, SatSolver};
        let witness = self.unsat_witness.as_ref()?;
        let mut solver = LookupSolver::<crate::sat::varisat::Varisat>::default();
        solver.set_var_count(self.vars.get_var_count());
        for &cid in &self.originals {
            let clause: Vec<_> = self.allocator[cid].iter().map(|&l| solver.lookup(l)).collect();
            solver.add_clause(&clause);
        }
        for &lit in &self.query_assumptions {
            let unit = solver.lookup(lit);
            solver.add_clause(&[unit]);
        }
        let assumptions: Vec<_> = witness.iter().map(|&l| solver.lookup(l)).collect();
        if solver.solve_with_assumptions(&assumptions).unwrap() {
            debug!("recorded universal witness is answerable, discarding");
            return None;
        }
        Some(witness.iter().map(|l| l.to_dimacs()).collect())
    }

    /// Extends the loaded instance *in place* after a completed solve —
    /// new variables in the existing scopes and new matrix clauses — and
    /// re-solves. This is the monotone continuation of the incremental
    /// API: root-level functions, learnt clauses, handled cases, variable
    /// activities, and the incremental conflict-check state are all kept.
    ///
    /// What is kept stays sound under a matrix extension: root-level
    /// functions and constants are implied by their implication clauses
    /// (which remain part of the matrix), and learnt clauses are
    /// resolvents. The two exceptions are re-checked explicitly and cause
    /// a `None` return, upon which the caller must fall back to a fresh
    /// solver:
    ///
    /// * root-level *pure-constant* assignments are winnability-preserving
    ///   choices w.r.t. the matrix at assignment time; an added clause
    ///   containing such a literal invalidates the choice,
    /// * handled cases (CEGAR responses and closed case splits) promise
    ///   that their recorded functions satisfy the matrix on their
    ///   region; every retained case must also satisfy the added clauses,
    ///   checked per case with the yet-unassigned variables treated
    ///   adversarially (so later function assignments cannot break a
    ///   passed check).
    ///
    /// `None` is also returned for prefix reshapes the in-place path does
    /// not support (a first universal variable, a re-mentioned free
    /// variable now declared, or more than two blocks); the fresh solver
    /// handles those uniformly.
    pub fn extend_and_resolve(
        &mut self,
        new_universals: &[u32],
        new_existentials: &[u32],
        clauses: &[Vec<i32>],
    ) -> Option<SolverResult> {
        if self.conflicted {
            // adding clauses and variables keeps an unsatisfiable instance
            // unsatisfiable, and the recorded winning move stays winning
            return Some(SolverResult::Unsatisfiable);
        }
        // retract any lazily kept query state
        self.query_assumptions.clear();
        self.extend_declarations(new_universals, new_existentials)?;

        // normalize the clauses; this may bind further free variables to
        // the outermost existential scope
        let free_before = self.prefix.first().map_or(0, |s| s.variables.len());
        let mut processed: Vec<Vec<Lit>> = Vec::new();
        for clause in clauses {
            let lits: Vec<Lit> = clause.iter().map(|&l| Lit::from_dimacs(l)).collect();
            let Some(lits) = self.preprocess_clause(&lits) else {
                continue;
            };
            if self.conflicted {
                // all-universal clause: the witness was recorded by the
                // preprocessing; keep the clause for witness verification
                let cid = self.allocator.add(&lits);
                self.originals.push(cid);
                return Some(SolverResult::Unsatisfiable);
            }
            processed.push(lits);
        }
        let new_frees: Vec<Var> = self.prefix[0].variables[free_before..].to_vec();
        for var in new_frees {
            self.vsids.add(var);
            self.queue_pure_check(var);
        }
        let blocks = self.prefix.iter().filter(|scope| !scope.variables.is_empty()).count();
        if blocks > 2 {
            return None;
        }

        if !self.trail.decision_level().is_root() {
            self.backtrack_to(DecLvl::ROOT);
        }
        self.casesplits.clear_committed();

        // Both the pure gate and the per-case checks below are SAT calls
        // whose encodings include the handled-case exclusions, so give up
        // early on states with many recorded cases rather than spend
        // longer checking than a rebuild costs.
        if !processed.is_empty() && self.handled_cases.len() > MAX_REVERIFIED_CASES {
            debug!(
                "monotone extension: {} handled cases exceed the re-verification budget",
                self.handled_cases.len()
            );
            return None;
        }

        // The pure gate: root-level pure-constant assignments are
        // winnability-preserving choices, and an added clause containing
        // such a literal invalidates the rewrite argument behind them —
        // unless the root functions entail the clause outright (with the
        // yet-unassigned variables adversarial): then any winning
        // strategy can still be rewritten onto the root functions without
        // falsifying the clause. (Inside the handled regions the per-case
        // re-verification below covers these clauses like any other.)
        let pure: HashSet<Lit> = self.root_pure_lits.iter().copied().collect();
        let touching: Vec<Vec<Lit>> = processed
            .iter()
            .filter(|lits| lits.iter().any(|l| pure.contains(l)))
            .cloned()
            .collect();
        if !touching.is_empty() {
            let functions = self.snapshot_functions();
            if self
                .region_counterexample(&functions, &[], self.handled_cases.len(), &touching)
                .is_some()
            {
                debug!(
                    "monotone extension: a new clause re-introduces a root pure literal \
                     and is not entailed by the root functions"
                );
                return None;
            }
        }

        // every retained region must satisfy the added clauses
        if !processed.is_empty() {
            for region in 0..self.handled_cases.len() {
                if !self.case_valid_for(region, &processed) {
                    debug!("monotone extension: handled case {region} fails on a new clause");
                    return None;
                }
            }
        }

        for lits in &processed {
            if let Some(result) = self.integrate_clause(lits) {
                return Some(result);
            }
        }

        // both hold matrix-derived state and are rebuilt lazily
        self.cegar.invalidate_solver();
        self.casesplits.invalidate_domain();
        self.stats.global.extensions += 1;
        debug!("monotone extension: continuing in place");
        Some(self.search())
    }

    /// Solves the loaded instance under temporary existential constant
    /// assumptions, reusing the live solver state. Assumptions are
    /// assigned as constants at fresh decision levels (the existential
    /// analog of universal case assumptions), sticky across backtracks;
    /// conflict analysis keeps their negations in every resolvent (they
    /// have no implication clauses to resolve on), so everything learnt
    /// or recorded during the query — learnt clauses, handled cases, root
    /// assignments — is matrix-valid and persists after retraction.
    ///
    /// On `Some(Satisfiable)` the solver is *left in the assumed state*
    /// so models and certificates reflect the query; the next solve or
    /// extension retracts it by backtracking. On `Some(Unsatisfiable)`,
    /// [`IncDet::unsat_witness`] (verified under the query assumptions)
    /// may expose a winning universal move for the query.
    ///
    /// Returns `None` when the fast path cannot answer soundly and the
    /// caller must fall back to a fresh throwaway query: handled cases
    /// were recorded before the query (their strategies need not respect
    /// the assumptions, so region coverage cannot be trusted), the
    /// incremental conflict check is disabled, an assumption variable is
    /// universal or unknown, the opposite constant was a root pure
    /// *choice* (revisable, so no verdict follows), or the search runs
    /// into a state it cannot attribute.
    pub fn resolve_with_assumptions(&mut self, assumptions: &[i32]) -> Option<SolverResult> {
        self.query_assumptions.clear();
        if self.conflicted {
            return Some(SolverResult::Unsatisfiable);
        }
        if !self.fast_query_available() {
            return None;
        }
        if !self.trail.decision_level().is_root() {
            self.backtrack_to(DecLvl::ROOT);
        }
        self.casesplits.clear_committed();
        let mut to_assume: Vec<Lit> = Vec::new();
        for &raw in assumptions {
            let lit = Lit::from_dimacs(raw);
            let var = lit.var();
            if var.as_index() >= self.vars.get_var_count() || self.vars[var].scope.is_none() {
                return None;
            }
            if self.vars[var].is_universal(&self.prefix) {
                return None;
            }
            if to_assume.contains(&!lit) {
                return Some(SolverResult::Unsatisfiable);
            }
            if to_assume.contains(&lit) {
                continue;
            }
            if self.assignment.is_assigned(var) {
                match self.assignment.constant_value(lit) {
                    Some(true) => {}
                    Some(false) => {
                        if self.root_pure_lits.contains(&lit) {
                            // the opposite constant is a winnability
                            // choice, not forced: no verdict follows
                            return None;
                        }
                        return Some(SolverResult::Unsatisfiable);
                    }
                    None => {
                        // root functions are implied, so the assumption
                        // holds iff the function is constantly the
                        // assumed polarity; a counterexample is a winning
                        // universal move for the query
                        let functions = self.snapshot_functions();
                        if let Some(witness) =
                            self.region_counterexample(&functions, &[], 0, &[vec![lit]])
                        {
                            // keep the assumptions for the witness
                            // verification context
                            self.query_assumptions = to_assume;
                            self.query_assumptions.push(lit);
                            self.unsat_witness = Some(witness);
                            return Some(SolverResult::Unsatisfiable);
                        }
                    }
                }
                continue;
            }
            to_assume.push(lit);
        }
        self.query_assumptions = to_assume;
        match self.search() {
            SolverResult::Satisfiable => Some(SolverResult::Satisfiable),
            SolverResult::Unsatisfiable => {
                if !self.trail.decision_level().is_root() {
                    self.backtrack_to(DecLvl::ROOT);
                }
                Some(SolverResult::Unsatisfiable)
            }
            SolverResult::Unknown => {
                // the search aborted the query; retract and fall back
                self.query_assumptions.clear();
                if !self.trail.decision_level().is_root() {
                    self.backtrack_to(DecLvl::ROOT);
                }
                None
            }
        }
    }

    /// Whether the in-place assumption query path is available: it
    /// declines outright when recorded cases predate the query (their
    /// strategies need not respect the assumptions) or the incremental
    /// conflict check is disabled. Callers can pre-check this to know
    /// whether an attempt may mutate the solver state.
    #[must_use]
    pub fn fast_query_available(&self) -> bool {
        self.options.incremental_conflict_check && self.handled_cases.is_empty()
    }

    /// Establishes the next query assumption that is not yet in force.
    fn reassume_query_step(&mut self) -> QueryStep {
        for i in 0..self.query_assumptions.len() {
            let lit = self.query_assumptions[i];
            let var = lit.var();
            if self.assignment.is_assigned(var) {
                match self.assignment.constant_value(lit) {
                    Some(true) => continue,
                    Some(false) => {
                        if self.dec_lvls[var] == Some(DecLvl::ROOT)
                            && !self.root_pure_lits.contains(&lit)
                        {
                            return QueryStep::Unsat;
                        }
                        return QueryStep::Abort;
                    }
                    None => return QueryStep::Abort,
                }
            }
            if let Some(assignment) = self.is_assumption_conflicted(lit) {
                return QueryStep::Conflict(Conflict { var, assignment });
            }
            self.assume_existential(lit);
            return QueryStep::Assumed;
        }
        QueryStep::Nothing
    }

    /// Assumes an existential literal as a constant at a fresh decision
    /// level: the query-scoped analog of a universal case assumption. The
    /// constant is communicated to the conflict check as a level-guarded
    /// unit; no implication clause justifies it, so conflict analysis
    /// keeps its negation in every resolvent.
    fn assume_existential(&mut self, lit: Lit) {
        debug!("query: assuming {lit}");
        self.trail.add_decision(lit);
        self.assignment.assign_constant(lit);
        self.dec_lvls[lit.var()] = Some(self.trail.decision_level());
        self.vsids.remove(lit.var());
        self.conflict_check_assume(lit);
        self.propagate_function(lit.var());
        self.requeue_mentioning(lit.var());
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
    }

    /// Declares new variables in the existing scopes for a monotone
    /// extension: universals join the existing universal scope,
    /// existentials the innermost existential scope. `None` when the
    /// prefix cannot be extended in place (no universal scope exists yet,
    /// or a variable is already bound).
    fn extend_declarations(
        &mut self,
        new_universals: &[u32],
        new_existentials: &[u32],
    ) -> Option<()> {
        let forall = self.prefix.iter().position(|s| s.quantifier == QuantTy::Forall);
        if !new_universals.is_empty() && forall.is_none() {
            return None;
        }
        let to_var =
            |v: u32| -> Option<Var> { Some(Lit::from_dimacs(i32::try_from(v).ok()?).var()) };
        let mut universal_vars = Vec::with_capacity(new_universals.len());
        for &v in new_universals {
            universal_vars.push(to_var(v)?);
        }
        let mut existential_vars = Vec::with_capacity(new_existentials.len());
        for &v in new_existentials {
            existential_vars.push(to_var(v)?);
        }
        for &var in universal_vars.iter().chain(&existential_vars) {
            if var.as_index() < self.vars.get_var_count() && self.vars[var].scope.is_some() {
                // already bound (e.g. mentioned in an earlier clause and
                // bound as free): the quantifier cannot change in place
                return None;
            }
        }
        for &var in &universal_vars {
            if var.as_index() >= self.vars.get_var_count() {
                self.set_var_count(var.as_index() + 1);
            }
            let scope = forall.expect("checked above");
            self.vars[var].scope = Some(ScopeId(scope));
            self.prefix[scope].variables.push(var);
        }
        if !existential_vars.is_empty() {
            self._quantify(QuantTy::Exists, &existential_vars);
        }
        for &var in &existential_vars {
            self.vsids.add(var);
            self.queue_pure_check(var);
        }
        Some(())
    }

    /// Integrates a normalized matrix clause into the live root-level
    /// state, mirroring the load and propagation paths. Concludes
    /// unsatisfiability if every existential literal of the clause is
    /// (permanently) root-assigned and the root functions do not entail
    /// the clause outside the handled regions.
    fn integrate_clause(&mut self, lits: &[Lit]) -> Option<SolverResult> {
        debug_assert!(self.trail.decision_level().is_root());
        let cid = self.allocator.add(lits);
        self.originals.push(cid);
        for &lit in lits {
            self.occurrences[lit].push(cid);
        }
        if lits.iter().any(|&l| self.assignment.constant_value(l) == Some(true)) {
            // satisfied by a root constant: globally satisfied, inert
            return None;
        }
        let unassigned: Vec<Lit> = lits
            .iter()
            .filter(|l| {
                self.vars[l.var()].is_existential(&self.prefix)
                    && !self.assignment.is_assigned(l.var())
            })
            .copied()
            .collect();
        match unassigned[..] {
            [] => {
                // every existential literal is root-assigned and those
                // functions are permanent: the clause must be entailed by
                // them outside the handled regions (inside, the per-case
                // re-verification has already checked it)
                let functions = self.snapshot_functions();
                let clauses = vec![lits.to_vec()];
                if let Some(witness) =
                    self.region_counterexample(&functions, &[], self.handled_cases.len(), &clauses)
                {
                    self.unsat_witness = Some(witness);
                    return Some(SolverResult::Unsatisfiable);
                }
            }
            [lit] => {
                // one unassigned existential left: the clause is an
                // implication clause for it, as on the propagation path
                self.skolem[lit].add_implication(cid, DecLvl::ROOT);
                self.allocator.lock(cid);
                self.graph[lit].push(Impl { clause: cid, dec_lvl: DecLvl::ROOT });
                if self.options.constant_propagation
                    && lits
                        .iter()
                        .filter(|&&l| l != lit)
                        .all(|&l| self.assignment.constant_value(l) == Some(false))
                {
                    self.constant_propagation.push_back(lit);
                }
                self.propagation
                    .add_and_set(lit.var(), self.skolem[lit].len() + self.skolem[!lit].len());
                self.queue_pure_check(lit.var());
            }
            _ => {
                self.clauses.push(cid);
                self.watches.add_watch(unassigned[0], Watch { clause: cid });
                self.watches.add_watch(unassigned[1], Watch { clause: cid });
            }
        }
        None
    }

    /// Number of completed in-place monotone extensions.
    pub(crate) fn extension_count(&self) -> u32 {
        self.stats.global.extensions
    }

    /// Solves the QBF using incremental determinization.
    pub fn solve(&mut self) -> SolverResult {
        let instant = Instant::now();
        let result = self._solve();
        self.stats.global.solve_time = instant.elapsed();
        info!("\n{:#?}", self.stats);
        result
    }

    /// Loads the initial state and runs the search. Must only be called
    /// once per solver; continuations after monotone extensions go through
    /// [`IncDet::extend_and_resolve`].
    fn _solve(&mut self) -> SolverResult {
        self.originals = self.allocator.ids().take(self.allocator.len()).collect();
        for &cid in &self.originals {
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
            // witness recorded when the offending clause was added
            debug_assert!(self.unsat_witness.is_some());
            return SolverResult::Unsatisfiable;
        }
        self.build_watchlist();
        self.build_vsids_heap();
        self.search()
    }

    // the main solver loop reads best as one piece
    #[allow(clippy::too_many_lines)]
    fn search(&mut self) -> SolverResult {
        let mut initial = Some(());
        let mut violation_rounds = 0;
        let mut conflicts_since_restart = 0;
        let mut restart_number = 1;
        let mut next_reduction = self.learnts.len() + REDUCTION_INCREMENT;
        let mut last_reboot = self.stats.skolem.global_conflict_checks;
        let mut conflicts_at_last_case = self.stats.global.conflicts;
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
            if !self.query_assumptions.is_empty() {
                match self.reassume_query_step() {
                    QueryStep::Nothing => {}
                    QueryStep::Assumed => continue,
                    QueryStep::Conflict(conflict) => {
                        // Assumption violations resolve by CEGAR rounds
                        // only: clause learning would attribute the
                        // conflict to the assumption variable and lose the
                        // assumption literal from the resolvent. Each
                        // round either answers the query or excludes a
                        // cube around the violation — exclusion-only
                        // progress, so recurring violations degenerate
                        // into cube enumeration; a small budget hands
                        // those queries to the throwaway fallback, whose
                        // full machinery learns clauses instead.
                        violation_rounds += 1;
                        if violation_rounds > QUERY_VIOLATION_BUDGET {
                            debug!("query: violation budget exhausted, aborting");
                            return SolverResult::Unknown;
                        }
                        match self.cegar_round(&conflict.assignment) {
                            cegar::CegarOutcome::Unsatisfiable => {
                                self.record_unsat_witness(&conflict.assignment);
                                return SolverResult::Unsatisfiable;
                            }
                            cegar::CegarOutcome::Satisfiable => {
                                return SolverResult::Satisfiable;
                            }
                            cegar::CegarOutcome::CaseRecorded => {
                                conflicts_since_restart += 1;
                                continue;
                            }
                        }
                    }
                    QueryStep::Unsat => return SolverResult::Unsatisfiable,
                    QueryStep::Abort => return SolverResult::Unknown,
                }
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
            if self.trail.decision_level().is_root() {
                self.root_pure_lits.push(lit);
            }
            match self.propagate_constant(!lit) {
                Some(conflict) => PureStep::Conflict(conflict),
                None => PureStep::Progress,
            }
        } else if let Some(assignment) = self.is_conflicted(var) {
            trace!("pure {} is conflicted", var);
            PureStep::Conflict(Conflict { var, assignment })
        } else {
            // assigned as a decision (a fresh level), so unlike the
            // constant case this choice is unwound by backtracking and
            // needs no extension gate
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
            // at the root all functions are forced, so the conflicting
            // assignment is a winning universal move
            self.record_unsat_witness(&conflict.assignment);
            return Some(SolverResult::Unsatisfiable);
        }
        let Ok(backtrack_to) = self.analyze(conflict) else {
            // The analysis clause is matrix-implied and all its existential
            // literals are falsified by the (forced) root-level functions,
            // so any universal assignment falsifying its universal literals
            // is a winning move.
            let witness = self
                .conflict_analysis
                .clause()
                .iter()
                .filter(|l| {
                    let data = &self.vars[l.var()];
                    data.scope.is_some() && data.is_universal(&self.prefix)
                })
                .map(|&l| !l)
                .collect();
            self.unsat_witness = Some(witness);
            return Some(SolverResult::Unsatisfiable);
        };
        debug!("conflict analysis: backtrack to {backtrack_to:?}");
        self.backtrack_to(backtrack_to);
        let clause = self.conflict_analysis.clause().to_owned();
        self._add_clause(&clause);
        self.stats.global.added_clauses += 1;
        if self.conflicted {
            // the learnt clause contained only universal literals (e.g. the
            // negation of a case assumption); the witness falsifying it was
            // recorded when the clause was added
            debug_assert!(self.unsat_witness.is_some());
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
