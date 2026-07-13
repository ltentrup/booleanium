//! CEGAR extension of incremental determinization, following
//! "Understanding and Extending Incremental Determinization for 2QBF"
//! (Rabe, Tentrup, Rasmussen, Seshia, CAV 2018) and its reference
//! implementation in CADET.
//!
//! When a conflict check returns a conflicting assignment, a second SAT
//! solver checks whether the existential player has any response to it.
//! The key to making the recorded cases general is to phrase everything in
//! terms of the deterministic *frontier* instead of the universal inputs:
//!
//! * A clause is *settled* if it is an implication clause of a root-level
//!   assigned variable (or satisfied by a root-level constant): the derived
//!   functions satisfy it under every universal assignment, so responses
//!   never need to consider it.
//! * The *frontier* (interface) consists of the universal variables and the
//!   root-level assigned existential variables occurring in the unsettled
//!   clauses.
//!
//! The response solver holds the full matrix and is first queried under
//! the universal part of the conflicting assignment. No response means the
//! formula is unsatisfiable. A response is generalized to a *universal*
//! cube (over the universal variables, with the full model as the
//! response): a fat box in the input space, the best shape on unstructured
//! instances. Only when that cube degenerates — the response depends on
//! the inputs through derived signals, as with carry chains — the query is
//! re-solved with the conflicting assignment's frontier values pinned (so
//! the model's frontier matches the actual function outputs, again
//! unsatisfiability means the formula is unsatisfiable, since the frontier
//! values are produced by the forced root-level functions), and the result
//! is generalized to a *frontier* cube: the response then only covers the
//! non-frontier variables, the root-level functions are recorded
//! implicitly, and a cube over derived signals covers exponentially many
//! universal inputs at once. Either cube is recorded as a handled case and
//! excluded from all future conflict checks; an empty cube means the
//! response works everywhere and the formula is satisfiable.
//!
//! Whether CEGAR rounds run is controlled by an exponential moving average
//! of the recorded cube sizes: when cubes degenerate towards full
//! assignments (excluding a single assignment per round), the rounds stop
//! paying off and conflicts fall back to clause learning.

use crate::{
    incdet::propagation::trail::DecLvl,
    incdet::{Conflict, IncDet},
    literal::{Lit, Var},
    sat::{varisat::Varisat, LookupSolver, SatSolver},
    SolverResult,
};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use tracing::{debug, info};

/// Weight of the newest cube size in the exponential moving average.
const CUBE_SIZE_EMA_WEIGHT: f64 = 0.1;

/// CEGAR rounds run while the average cube size stays below this fraction
/// of the number of universal variables.
const EFFECTIVENESS_THRESHOLD: f64 = 0.8;

/// Number of initial rounds that run regardless of effectiveness.
const BOOTSTRAP_ROUNDS: u32 = 8;

/// Number of new root-level assignments after which the response solver is
/// rebuilt to move the frontier.
const REBUILD_ROOT_GROWTH: usize = 32;

#[derive(Debug, Default)]
pub(crate) struct Cegar {
    /// SAT solver over the unsettled clauses, asking for existential
    /// responses to assumed frontier assignments. Rebuilt when the
    /// root-level trail grows (the frontier moves).
    solver: Option<ExistsSolver>,
    /// Exponential moving average of the recorded cube sizes.
    cube_size_ema: f64,
    rounds: u32,
    /// The most recently recorded response: a winning move for the current
    /// search region, used as the decision phase. Replaced wholesale each
    /// round — accumulating stale phases from older regions misguides
    /// refutation searches.
    latest_response: HashMap<Var, bool>,
}

impl Cegar {
    /// The polarity the latest recorded response assigned to `var`.
    pub(crate) fn response_phase(&self, var: Var) -> Option<bool> {
        self.latest_response.get(&var).copied()
    }

    /// Drops the response solver so the next round rebuilds it. Used by
    /// monotone extension: the solver holds the full matrix and the
    /// occurrence indices of the original clause list, both of which the
    /// extension changes.
    pub(crate) fn invalidate_solver(&mut self) {
        self.solver = None;
    }
}

struct ExistsSolver {
    /// SAT solver over the full original matrix.
    solver: LookupSolver<Varisat>,
    /// The original clauses that are not settled by the root-level
    /// functions.
    unsettled: Vec<crate::clause::alloc::ClauseId>,
    /// For every literal, the indices (into `unsettled`) of the unsettled
    /// clauses containing it (for frontier-cube minimization).
    occurrences: HashMap<Lit, Vec<usize>>,
    /// For every universal literal, the indices (into the original clause
    /// list) of the clauses containing it (for universal-cube
    /// minimization). Ordered, so cube composition is deterministic across
    /// runs.
    universal_occurrences: BTreeMap<Lit, Vec<usize>>,
    /// The frontier: universal and root-level assigned existential
    /// variables occurring in the unsettled clauses.
    interface: Vec<Var>,
    /// The variables that were root-level assigned when the solver was
    /// built. A frontier-cube response must cover exactly the variables
    /// outside this set: root-level functions are recorded implicitly —
    /// including those of settled-only variables outside the interface,
    /// whose functions still carry their settled clauses — while a
    /// variable root-assigned after the last rebuild is treated as a
    /// response variable whose constant overrides its later function.
    root_vars: HashSet<Var>,
    /// Number of root-level assignments when the solver was built; the
    /// solver is rebuilt when the root level has grown substantially since
    /// (root assignments are permanent, so it never shrinks). Rebuilding
    /// on every growth is wasted work on instances that backtrack to the
    /// root frequently; a stale frontier stays sound via `root_vars`.
    root_assignments: usize,
    /// Number of universal variables of the instance.
    universal_count: usize,
}

impl std::fmt::Debug for ExistsSolver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExistsSolver").finish()
    }
}

pub(crate) enum CegarOutcome {
    /// The conflicting frontier assignment has no existential response.
    Unsatisfiable,
    /// The recorded response covers every universal assignment.
    Satisfiable,
    /// A case was recorded and excluded from future conflict checks.
    CaseRecorded,
}

impl IncDet {
    /// Resolves a conflict either by a CEGAR round or by clause learning.
    /// Carving several cases per conflict before learning (as CADET does,
    /// up to 50 rounds per learnt clause) was tried and made everything
    /// worse by an order of magnitude — without the interleaved learning,
    /// near-identical cubes flood the conflict check with exclusion
    /// clauses.
    pub(crate) fn resolve_conflict(&mut self, conflict: &Conflict) -> Option<SolverResult> {
        if self.options.cegar && self.cegar_worthwhile() {
            match self.cegar_round(&conflict.assignment) {
                CegarOutcome::Unsatisfiable => {
                    info!("CEGAR: conflicting frontier assignment has no response");
                    self.record_unsat_witness(&conflict.assignment);
                    return Some(SolverResult::Unsatisfiable);
                }
                CegarOutcome::Satisfiable => {
                    info!("CEGAR: response covers all universal assignments");
                    return Some(SolverResult::Satisfiable);
                }
                CegarOutcome::CaseRecorded => {
                    // The recorded case excludes a whole cube of universal
                    // assignments, but on unsatisfiable instances with large
                    // universal spaces case-carving alone diverges; clause
                    // learning below keeps refutation progress. A conflict
                    // at the root level would have been unanswerable, so the
                    // case is only recorded on higher levels where learning
                    // is possible.
                    if self.trail.decision_level().is_root() {
                        if !self.assignment.is_assigned(conflict.var) {
                            self.requeue_determinacy_check(conflict.var);
                        }
                        return None;
                    }
                }
            }
        }
        self.handle_conflict(conflict)
    }

    fn cegar_worthwhile(&self) -> bool {
        if self.cegar.rounds < BOOTSTRAP_ROUNDS {
            return true;
        }
        let universals = match &self.cegar.solver {
            Some(solver) => solver.universal_count,
            None => return true,
        };
        #[allow(clippy::cast_precision_loss)]
        let threshold = EFFECTIVENESS_THRESHOLD * universals as f64;
        self.cegar.cube_size_ema < threshold
    }

    /// Runs one CEGAR round for the conflicting assignment.
    pub(crate) fn cegar_round(&mut self, conflicting: &HashSet<Lit>) -> CegarOutcome {
        self.stats.cegar.rounds += 1;
        self.cegar.rounds += 1;
        if self.stats.cegar.rounds % 1024 == 0 {
            info!(
                "cegar progress: {} rounds, {} cases, cube size average {:.1}",
                self.stats.cegar.rounds, self.stats.cegar.cases, self.cegar.cube_size_ema
            );
        }
        self.ensure_exists_solver();
        let exists = self.cegar.solver.as_mut().expect("solver was just created");

        // ask for an existential response to the universal part of the
        // conflicting assignment (sorted: the backend's search is sensitive
        // to the assumption order, and the conflicting assignment is an
        // unordered set)
        let mut universal_part: Vec<Lit> = conflicting
            .iter()
            .filter(|l| {
                let data = &self.vars[l.var()];
                data.scope.is_some() && data.is_universal(&self.prefix)
            })
            .copied()
            .collect();
        universal_part.sort_unstable();
        // query assumptions constrain every response, so recorded cases
        // respect them (and stay matrix-valid: a response satisfying
        // matrix ∧ assumptions satisfies the matrix)
        let assumptions: Vec<_> = universal_part
            .iter()
            .chain(self.query_assumptions.iter())
            .map(|&l| exists.solver.lookup(l))
            .collect();
        if !exists.solver.solve_with_assumptions(&assumptions).unwrap() {
            return CegarOutcome::Unsatisfiable;
        }
        let model: HashSet<Lit> =
            exists.solver.orig_model().expect("model after sat").into_iter().collect();

        let mut frontier = false;
        let mut cube = self.minimize_universal_cube(&model);
        let mut model = model;
        #[allow(clippy::cast_precision_loss)]
        let degenerate = {
            let exists = self.cegar.solver.as_ref().expect("solver exists during round");
            cube.len() as f64 > EFFECTIVENESS_THRESHOLD * exists.universal_count as f64
        };
        if degenerate {
            // The universal cube barely generalizes: the response depends
            // on the inputs only through derived signals (e.g. carry
            // chains). Re-solve with the whole frontier of the conflicting
            // assignment pinned — so that the frontier values of the model
            // match the actual function outputs — and generalize over the
            // frontier instead.
            let query = self.query_assumptions.clone();
            let exists = self.cegar.solver.as_mut().expect("solver exists during round");
            let assumptions: Vec<_> = exists
                .interface
                .iter()
                .map(|&var| {
                    if conflicting.contains(&Lit::negative(var)) {
                        Lit::negative(var)
                    } else {
                        Lit::positive(var)
                    }
                })
                .chain(query)
                .map(|lit| exists.solver.lookup(lit))
                .collect();
            if !exists.solver.solve_with_assumptions(&assumptions).unwrap() {
                return CegarOutcome::Unsatisfiable;
            }
            model = exists.solver.orig_model().expect("model after sat").into_iter().collect();
            let universal_cube = self.minimize_universal_cube(&model);
            let frontier_cube = self.minimize_frontier_cube(&model);
            frontier = frontier_cube.len() < universal_cube.len();
            cube = if frontier { frontier_cube } else { universal_cube };
        }
        debug!(
            "CEGAR {} cube: {:?}",
            if frontier { "frontier" } else { "universal" },
            cube.iter().map(ToString::to_string).collect::<Vec<_>>()
        );

        #[allow(clippy::cast_precision_loss)]
        let size = cube.len() as f64;
        self.cegar.cube_size_ema =
            CUBE_SIZE_EMA_WEIGHT * size + (1.0 - CUBE_SIZE_EMA_WEIGHT) * self.cegar.cube_size_ema;

        // The response covers the variables whose root-level functions are
        // not recorded implicitly: for a frontier cube these are exactly
        // the non-frontier variables; a universal cube also relies on the
        // model values of the frontier variables, so the full model is the
        // response.
        let exists = self.cegar.solver.as_ref().expect("solver exists during round");
        let response: Vec<Lit> = model
            .iter()
            .filter(|l| {
                let data = &self.vars[l.var()];
                data.scope.is_some()
                    && data.is_existential(&self.prefix)
                    && (!frontier || !exists.root_vars.contains(&l.var()))
            })
            .copied()
            .collect();
        self.cegar.latest_response = response.iter().map(|l| (l.var(), l.is_positive())).collect();
        let satisfiable = cube.is_empty();
        self.stats.cegar.cases += 1;
        self.exclude_cube(&cube);
        self.handled_cases.push(crate::incdet::casesplit::HandledCase::Response { cube, response });
        if satisfiable {
            CegarOutcome::Satisfiable
        } else {
            CegarOutcome::CaseRecorded
        }
    }

    /// Minimizes the frontier part of the model to a cube such that the
    /// model's response satisfies every unsettled clause under every
    /// extension of the cube. A frontier literal is dropped if every
    /// unsettled clause it satisfies keeps another support: a model-true
    /// response literal, or a model-true frontier literal that has not been
    /// dropped itself.
    fn minimize_frontier_cube(&self, model: &HashSet<Lit>) -> Vec<Lit> {
        let exists = self.cegar.solver.as_ref().expect("solver exists during round");
        let mut dropped: HashSet<Var> = HashSet::new();
        let mut cube = Vec::new();
        for &var in &exists.interface {
            let lit = if model.contains(&Lit::negative(var)) {
                Lit::negative(var)
            } else {
                Lit::positive(var)
            };
            let needed = exists.occurrences.get(&lit).is_some_and(|occs| {
                occs.iter().any(|&idx| {
                    let cid = exists.unsettled[idx];
                    let satisfied_without = self.allocator[cid].iter().any(|&other| {
                        other.var() != var
                            && model.contains(&other)
                            && !dropped.contains(&other.var())
                    });
                    !satisfied_without
                })
            });
            if needed {
                cube.push(lit);
            } else {
                dropped.insert(var);
            }
        }
        cube
    }

    /// Minimizes the universal part of the model to a cube such that the
    /// model's existential part satisfies every original clause under every
    /// extension of the cube: every clause keeps a support that is either
    /// an existential literal of the model or a universal literal of the
    /// cube.
    fn minimize_universal_cube(&self, model: &HashSet<Lit>) -> Vec<Lit> {
        let exists = self.cegar.solver.as_ref().expect("solver exists during round");
        // per original clause: whether an existential literal supports it,
        // and how many universal candidate literals support it
        let mut existential_support = vec![false; self.originals.len()];
        let mut universal_supports = vec![0u32; self.originals.len()];
        for (idx, &cid) in self.originals.iter().enumerate() {
            for &l in self.allocator[cid].iter() {
                if !model.contains(&l) {
                    continue;
                }
                let data = &self.vars[l.var()];
                if data.scope.is_none() {
                    continue;
                }
                if data.is_universal(&self.prefix) {
                    universal_supports[idx] += 1;
                } else {
                    existential_support[idx] = true;
                }
            }
        }
        let mut cube = Vec::new();
        for (&lit, occurrences) in &exists.universal_occurrences {
            if !model.contains(&lit) {
                continue;
            }
            let droppable = occurrences
                .iter()
                .all(|&idx| existential_support[idx] || universal_supports[idx] >= 2);
            if droppable {
                for &idx in occurrences {
                    universal_supports[idx] -= 1;
                }
            } else {
                cube.push(lit);
            }
        }
        cube
    }

    /// Builds (or rebuilds after root-level progress) the SAT solver over
    /// the full matrix, together with the frontier and the occurrence
    /// lists used for cube minimization.
    fn ensure_exists_solver(&mut self) {
        let root_vars: HashSet<Var> = self
            .trail
            .iter()
            .filter(|l| self.dec_lvls[l.var()] == Some(DecLvl::ROOT))
            .map(|l| l.var())
            .collect();
        let root_assignments = root_vars.len();
        if let Some(exists) = &self.cegar.solver {
            if root_assignments < exists.root_assignments + REBUILD_ROOT_GROWTH {
                return;
            }
        }
        // implication clauses of root-level assigned variables are settled:
        // the root-level functions satisfy them under every universal
        // assignment
        let mut settled: HashSet<crate::clause::alloc::ClauseId> = HashSet::new();
        for &lit in self.trail.iter() {
            if self.dec_lvls[lit.var()] != Some(DecLvl::ROOT) {
                continue;
            }
            for l in [lit, !lit] {
                settled.extend(self.skolem[l].implications());
            }
        }
        let mut solver = LookupSolver::<Varisat>::default();
        solver.set_var_count(self.vars.get_var_count());
        let mut unsettled = Vec::new();
        let mut occurrences: HashMap<Lit, Vec<usize>> = HashMap::new();
        let mut universal_occurrences: BTreeMap<Lit, Vec<usize>> = BTreeMap::new();
        let mut interface: BTreeSet<Var> = BTreeSet::new();
        for (orig_idx, &cid) in self.originals.iter().enumerate() {
            let clause = &self.allocator[cid];
            let encoded: Vec<_> = clause.iter().map(|&l| solver.lookup(l)).collect();
            solver.add_clause(&encoded);
            for &l in clause.iter() {
                let data = &self.vars[l.var()];
                if data.scope.is_some() && data.is_universal(&self.prefix) {
                    universal_occurrences.entry(l).or_default().push(orig_idx);
                }
            }
            let by_root_constant = clause.iter().any(|&l| {
                self.assignment.constant_value(l) == Some(true)
                    && self.dec_lvls[l.var()] == Some(DecLvl::ROOT)
            });
            if by_root_constant || settled.contains(&cid) {
                continue;
            }
            let idx = unsettled.len();
            for &l in clause.iter() {
                let data = &self.vars[l.var()];
                if data.scope.is_none() {
                    continue;
                }
                occurrences.entry(l).or_default().push(idx);
                if data.is_universal(&self.prefix) || self.dec_lvls[l.var()] == Some(DecLvl::ROOT) {
                    interface.insert(l.var());
                }
            }
            unsettled.push(cid);
        }
        let universal_count = self
            .prefix
            .iter()
            .filter(|scope| scope.quantifier == crate::QuantTy::Forall)
            .map(|scope| scope.variables.len())
            .sum();
        debug!(
            "CEGAR frontier: {} interface variables, {} of {} clauses unsettled",
            interface.len(),
            unsettled.len(),
            self.originals.len()
        );
        self.cegar.solver = Some(ExistsSolver {
            solver,
            unsettled,
            occurrences,
            universal_occurrences,
            interface: interface.into_iter().collect(),
            root_vars,
            root_assignments,
            universal_count,
        });
    }
}
