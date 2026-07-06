//! CEGAR extension of incremental determinization, following
//! "Understanding and Extending Incremental Determinization for 2QBF"
//! (Rabe, Tentrup, Rasmussen, Seshia, CAV 2018).
//!
//! When a conflict check returns a conflicting universal assignment α, a
//! second SAT solver over the *original matrix* checks whether the
//! existential player has any response to α at all:
//!
//! * If not, α is a winning move for the universal player and the formula
//!   is unsatisfiable — regardless of the current solver state.
//! * If there is a response, the conflict only reflects the current partial
//!   Skolem functions. The response is then generalized: α is minimized to
//!   a cube such that the response satisfies every original clause under
//!   *every* extension of the cube. The cube is recorded as a handled case
//!   with the response as its constant Skolem function, and excluded from
//!   all future conflict checks. If the cube is empty, the response works
//!   for every universal assignment and the formula is satisfiable.
//!
//! Whether CEGAR rounds run is controlled by an exponential moving average
//! of the recorded cube sizes: when cubes degenerate towards full
//! assignments (excluding a single α per round), the rounds stop paying off
//! and conflicts fall back to clause learning.

use crate::{
    incdet::{Conflict, IncDet},
    literal::Lit,
    sat::{varisat::Varisat, LookupSolver, SatSolver},
    SolverResult,
};
use std::collections::{HashMap, HashSet};
use tracing::{debug, info, trace};

/// Weight of the newest cube size in the exponential moving average.
const CUBE_SIZE_EMA_WEIGHT: f64 = 0.1;

/// CEGAR rounds run while the average cube size stays below this fraction
/// of the number of universal variables.
const EFFECTIVENESS_THRESHOLD: f64 = 0.8;

/// Number of initial rounds that run regardless of effectiveness.
const BOOTSTRAP_ROUNDS: u32 = 8;

#[derive(Debug, Default)]
pub(crate) struct Cegar {
    /// SAT solver over the original matrix, asking for existential
    /// responses to assumed universal assignments. Built on first use.
    solver: Option<ExistsSolver>,
    /// The handled cases.
    pub(crate) cases: Vec<Case>,
    /// Exponential moving average of the recorded cube sizes.
    cube_size_ema: f64,
    rounds: u32,
}

/// A handled case: for every universal assignment extending `cube`, the
/// constant existential assignment `response` satisfies the matrix.
#[derive(Debug)]
pub(crate) struct Case {
    pub(crate) cube: Vec<Lit>,
    pub(crate) response: Vec<Lit>,
}

struct ExistsSolver {
    solver: LookupSolver<Varisat>,
    /// For every universal literal, the indices (into the original clause
    /// list) of the clauses containing it.
    occurrences: HashMap<Lit, Vec<usize>>,
    /// Number of universal variables of the instance.
    universal_count: usize,
}

impl std::fmt::Debug for ExistsSolver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExistsSolver").finish()
    }
}

pub(crate) enum CegarOutcome {
    /// The conflicting universal assignment has no existential response.
    Unsatisfiable,
    /// The recorded response covers every universal assignment.
    Satisfiable,
    /// A case was recorded and excluded from future conflict checks.
    CaseRecorded,
}

impl IncDet {
    /// Resolves a conflict either by a CEGAR round or by clause learning.
    pub(crate) fn resolve_conflict(&mut self, conflict: &Conflict) -> Option<SolverResult> {
        if self.options.cegar && self.cegar_worthwhile() {
            match self.cegar_round(&conflict.assignment) {
                CegarOutcome::Unsatisfiable => {
                    info!("CEGAR: conflicting universal assignment has no response");
                    return Some(SolverResult::Unsatisfiable);
                }
                CegarOutcome::Satisfiable => {
                    info!("CEGAR: response covers all universal assignments");
                    return Some(SolverResult::Satisfiable);
                }
                CegarOutcome::CaseRecorded => {
                    // the conflict is resolved without clause learning; the
                    // variable may have become decidable or deterministic
                    if !self.assignment.is_assigned(conflict.var) {
                        self.requeue_determinacy_check(conflict.var);
                    }
                    return None;
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
    fn cegar_round(&mut self, conflicting: &HashSet<Lit>) -> CegarOutcome {
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
        // conflicting assignment
        let assumptions: Vec<_> = conflicting
            .iter()
            .filter(|l| {
                let data = &self.vars[l.var()];
                data.scope.is_some() && data.is_universal(&self.prefix)
            })
            .map(|&l| exists.solver.lookup(l))
            .collect();
        if !exists.solver.solve_with_assumptions(&assumptions).unwrap() {
            return CegarOutcome::Unsatisfiable;
        }
        let model: HashSet<Lit> =
            exists.solver.orig_model().expect("model after sat").into_iter().collect();

        let cube = self.minimize_cube(&model);
        trace!("CEGAR cube: {:?}", cube.iter().map(ToString::to_string).collect::<Vec<_>>());

        #[allow(clippy::cast_precision_loss)]
        let size = cube.len() as f64;
        self.cegar.cube_size_ema =
            CUBE_SIZE_EMA_WEIGHT * size + (1.0 - CUBE_SIZE_EMA_WEIGHT) * self.cegar.cube_size_ema;

        let response: Vec<Lit> = model
            .iter()
            .filter(|l| {
                let data = &self.vars[l.var()];
                data.scope.is_some() && data.is_existential(&self.prefix)
            })
            .copied()
            .collect();
        let satisfiable = cube.is_empty();
        self.stats.cegar.cases += 1;
        self.conflict_check_exclude_cube(&cube);
        self.cegar.cases.push(Case { cube, response });
        if satisfiable {
            CegarOutcome::Satisfiable
        } else {
            CegarOutcome::CaseRecorded
        }
    }

    /// Minimizes the universal part of the model to a cube such that the
    /// model's existential part satisfies every original clause under every
    /// extension of the cube: every clause keeps a support that is either
    /// an existential literal of the model or a universal literal of the
    /// cube.
    fn minimize_cube(&self, model: &HashSet<Lit>) -> Vec<Lit> {
        let exists = self.cegar.solver.as_ref().expect("solver exists during round");
        // per original clause: whether an existential literal supports it,
        // and how many universal candidate literals support it
        let mut existential_support = vec![false; self.original_clause_count];
        let mut universal_supports = vec![0u32; self.original_clause_count];
        for (idx, cid) in self.allocator.ids().take(self.original_clause_count).enumerate() {
            for &l in self.allocator[cid].iter() {
                if !model.contains(&l) {
                    continue;
                }
                let data = &self.vars[l.var()];
                if data.scope.is_some() && data.is_universal(&self.prefix) {
                    universal_supports[idx] += 1;
                } else {
                    existential_support[idx] = true;
                }
            }
        }
        let mut cube = Vec::new();
        for (&lit, occurrences) in &exists.occurrences {
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

    /// Builds the SAT solver over the original matrix and the occurrence
    /// lists used for cube minimization.
    fn ensure_exists_solver(&mut self) {
        if self.cegar.solver.is_some() {
            return;
        }
        debug!("building the CEGAR existential-response solver");
        let mut solver = LookupSolver::<Varisat>::default();
        solver.set_var_count(self.vars.get_var_count());
        let mut occurrences: HashMap<Lit, Vec<usize>> = HashMap::new();
        for (idx, cid) in self.allocator.ids().take(self.original_clause_count).enumerate() {
            let clause = &self.allocator[cid];
            let encoded: Vec<_> = clause.iter().map(|&l| solver.lookup(l)).collect();
            solver.add_clause(&encoded);
            for &l in clause.iter() {
                let data = &self.vars[l.var()];
                if data.scope.is_some() && data.is_universal(&self.prefix) {
                    occurrences.entry(l).or_default().push(idx);
                }
            }
        }
        let universal_count = self
            .prefix
            .iter()
            .filter(|scope| scope.quantifier == crate::QuantTy::Forall)
            .map(|scope| scope.variables.len())
            .sum();
        self.cegar.solver = Some(ExistsSolver { solver, occurrences, universal_count });
    }
}
