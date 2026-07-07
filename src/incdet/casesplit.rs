//! Interleaved case splits, following "Understanding and Extending
//! Incremental Determinization for 2QBF" (Rabe, Tentrup, Rasmussen,
//! Seshia, CAV 2018).
//!
//! Once the search stalls, a universal literal is *assumed*: the variable
//! is assigned as a constant at a fresh decision level, which restricts all
//! determinacy and conflict checks to the halved universal domain. The
//! search continues with the full machinery inside the case, and crucially
//! keeps all derived state — learnt clauses are resolvents of
//! matrix-implied clauses and therefore valid across cases.
//!
//! When every existential variable is assigned while case assumptions are
//! active, the case is *closed*: the current Skolem functions are
//! snapshotted for certification, the assumption cube is recorded as a
//! handled case and permanently excluded from future conflict checks (its
//! universal assignments are covered), and the solver backtracks below the
//! assumptions and continues on the remaining domain.
//!
//! A small *domain solver* over the universal variables holds the negation
//! of every handled cube. Its models witness the remaining domain and
//! provide the polarity of the next assumption; unsatisfiability means the
//! whole domain is covered and the formula is satisfiable.

use crate::{
    incdet::propagation::assignment::Value,
    incdet::propagation::trail::DecLvl,
    incdet::IncDet,
    literal::{Lit, Var},
    sat::{varisat::Varisat, LookupSolver, SatSolver},
};
use std::collections::HashMap;
use tracing::{debug, info};

/// A universal assignment region that is fully handled, together with the
/// data to certify it. Region `k` of the list is valid on its cube minus
/// the cubes of the regions `0..k` handled before it (their exclusions were
/// active while this region was solved); the current solver state covers
/// everything outside all handled cubes.
#[derive(Debug)]
pub(crate) enum HandledCase {
    /// A CEGAR case: the constant `response` satisfies the matrix under
    /// every extension of `cube`.
    Response { cube: Vec<Lit>, response: Vec<Lit> },
    /// A closed case split: the snapshotted Skolem functions satisfy the
    /// matrix on the region of `cube`.
    Closed { cube: Vec<Lit>, functions: Vec<SnapshotFunction> },
}

impl HandledCase {
    pub(crate) fn cube(&self) -> &[Lit] {
        match self {
            HandledCase::Response { cube, .. } | HandledCase::Closed { cube, .. } => cube,
        }
    }
}

/// The Skolem function of one variable, in trail order: the assigned
/// literal holds iff one of the implication clauses fires (or always, for
/// constants).
#[derive(Debug)]
pub(crate) struct SnapshotFunction {
    pub(crate) lit: Lit,
    pub(crate) constant: bool,
    pub(crate) implications: Vec<Vec<Lit>>,
}

/// State of interleaved case splitting.
#[derive(Debug, Default)]
pub(crate) struct CaseSplits {
    /// The active case assumptions with the decision level *below* each
    /// assumption (the level to backtrack to when closing).
    active: Vec<(Lit, DecLvl)>,
    /// The assumptions committed until their case closes. Conflicts may
    /// backtrack below an assumption and prune it from `active`; committed
    /// assumptions are re-assumed once propagation settles, so cases stay
    /// open across conflicts (they cannot be abandoned anyway: the
    /// universal player chooses the case, so every case must be won).
    committed: Vec<Lit>,
    /// SAT solver over the universal variables holding the negation of
    /// every handled cube; models witness the remaining domain.
    domain: Option<DomainSolver>,
    /// Occurrence counts of universal variables in the original matrix.
    occurrences: Option<HashMap<Var, usize>>,
}

struct DomainSolver(LookupSolver<Varisat>);

impl std::fmt::Debug for DomainSolver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DomainSolver").finish()
    }
}

pub(crate) enum CaseAction {
    /// A new case assumption was made, the search continues inside it.
    Assumed,
    /// The remaining universal domain is empty.
    DomainEmpty,
    /// There is no universal variable to split on.
    NoUniversals,
}

impl IncDet {
    /// Whether case assumptions are currently active.
    pub(crate) fn casesplits_active(&self) -> bool {
        !self.casesplits.active.is_empty()
    }

    /// Called when the search stalls: assume a universal literal from the
    /// remaining domain, or detect that the domain is fully handled.
    pub(crate) fn open_case(&mut self) -> CaseAction {
        self.ensure_domain_solver();
        // the next assumption must lie in the remaining domain, and inside
        // the active case
        let active: Vec<Lit> = self.casesplits.active.iter().map(|&(lit, _)| lit).collect();
        let domain = self.casesplits.domain.as_mut().expect("domain solver was just created");
        let assumptions: Vec<_> = active.iter().map(|&l| domain.0.lookup(l)).collect();
        if !domain.0.solve_with_assumptions(&assumptions).unwrap() {
            if self.casesplits.active.is_empty() {
                return CaseAction::DomainEmpty;
            }
            // the active case has no remaining domain, close it
            self.close_cases();
            return CaseAction::Assumed;
        }
        let model: HashMap<Var, bool> = domain
            .0
            .orig_model()
            .expect("model after sat")
            .into_iter()
            .map(|l| (l.var(), l.is_positive()))
            .collect();
        // pick the most frequent universal variable that is not active yet
        let occurrences = self.casesplits.occurrences.as_ref().expect("counted with the solver");
        let candidate = occurrences
            .iter()
            .filter(|(var, _)| !self.assignment.is_assigned(**var))
            .max_by_key(|(var, count)| (**count, **var))
            .map(|(&var, _)| var);
        let Some(var) = candidate else {
            return CaseAction::NoUniversals;
        };
        // default to the positive polarity if the variable is unconstrained
        // in the domain model
        let value = model.get(&var).copied().unwrap_or(true);
        let lit = if value { Lit::positive(var) } else { Lit::negative(var) };
        self.casesplits.committed.push(lit);
        self.assume_universal(lit);
        CaseAction::Assumed
    }

    /// Re-establishes the next committed case assumption that a conflict
    /// backtrack pruned from the active list. Returns `true` if an
    /// assumption was re-assumed (propagation must run before the next
    /// one).
    pub(crate) fn reassume_cases(&mut self) -> bool {
        let Some(&lit) = self.casesplits.committed.get(self.casesplits.active.len()) else {
            return false;
        };
        debug_assert!(!self.assignment.is_assigned(lit.var()));
        self.stats.cases.reassumed += 1;
        self.assume_universal(lit);
        true
    }

    /// Assumes a universal literal: the variable becomes a constant at a
    /// fresh decision level, restricting all checks to the halved domain.
    fn assume_universal(&mut self, lit: Lit) {
        info!(
            "case split: assuming {lit} at depth {} after {} conflicts",
            self.casesplits.active.len(),
            self.stats.global.conflicts
        );
        self.stats.cases.assumptions += 1;
        let below = self.trail.decision_level();
        self.trail.add_decision(lit);
        self.assignment.assign_constant(lit);
        self.dec_lvls[lit.var()] = Some(self.trail.decision_level());
        self.conflict_check_assume(lit);
        self.casesplits.active.push((lit, below));
        // Determinacy may improve within the restricted domain, but the
        // determinacy check is local to a variable's implication clauses
        // (simplified by constants), so only variables whose implications
        // mention the assumed variable can change.
        for (var, data) in self.vars.iter() {
            if data.scope.is_some()
                && data.is_existential(&self.prefix)
                && !self.assignment.is_assigned(var)
            {
                let mentions_assumption = |l: Lit| {
                    self.skolem[l]
                        .implications()
                        .any(|cid| self.allocator[cid].iter().any(|c| c.var() == lit.var()))
                };
                if mentions_assumption(Lit::positive(var))
                    || mentions_assumption(Lit::negative(var))
                {
                    let implications = self.skolem[Lit::positive(var)].len()
                        + self.skolem[Lit::negative(var)].len();
                    self.propagation.add_and_set(var, implications);
                }
            }
        }
    }

    /// Closes all active cases: every existential variable is assigned (or
    /// the case domain is empty), so the current functions cover the cube
    /// of the active assumptions. Records the case, excludes the cube, and
    /// backtracks below the assumptions.
    pub(crate) fn close_cases(&mut self) {
        let cube: Vec<Lit> = self.casesplits.active.iter().map(|&(lit, _)| lit).collect();
        let below = self.casesplits.active.first().expect("a case is active").1;
        info!(
            "closing case {:?} with {} handled cases",
            cube.iter().map(ToString::to_string).collect::<Vec<_>>(),
            self.handled_cases.len()
        );
        self.stats.cases.closed += 1;
        let functions = self.snapshot_functions();
        self.exclude_cube(&cube);
        self.handled_cases.push(HandledCase::Closed { cube, functions });
        self.casesplits.committed.clear();
        self.backtrack_to(below);
        debug_assert!(self.casesplits.active.is_empty());
    }

    /// Snapshots the Skolem functions of the assigned existential variables
    /// in trail order (case assumptions are skipped; they form the cube).
    pub(crate) fn snapshot_functions(&self) -> Vec<SnapshotFunction> {
        let mut functions = Vec::new();
        for &lit in self.trail.iter() {
            let var = lit.var();
            let data = &self.vars[var];
            if data.scope.is_some() && data.is_universal(&self.prefix) {
                continue;
            }
            match self.assignment[var].expect("trail variables are assigned") {
                Value::True | Value::False => {
                    functions.push(SnapshotFunction { lit, constant: true, implications: vec![] });
                }
                Value::PositiveImplications | Value::NegativeImplications => {
                    let implications = self.skolem[lit]
                        .implications()
                        .map(|cid| self.allocator[cid].lits().to_vec())
                        .collect();
                    functions.push(SnapshotFunction { lit, constant: false, implications });
                }
            }
        }
        functions
    }

    /// Snapshots the Skolem functions of the root-level assigned
    /// existential variables in trail order, excluding `exclude`. Used to
    /// certify CEGAR responses: the response constants cover exactly the
    /// variables that were not root-level assigned when the case was
    /// recorded, and they override any function those variables acquired
    /// later.
    pub(crate) fn snapshot_root_functions(
        &self,
        exclude: &std::collections::HashSet<Var>,
    ) -> Vec<SnapshotFunction> {
        let mut functions = Vec::new();
        for &lit in self.trail.iter() {
            let var = lit.var();
            if self.dec_lvls[var] != Some(DecLvl::ROOT) || exclude.contains(&var) {
                continue;
            }
            let data = &self.vars[var];
            if data.scope.is_some() && data.is_universal(&self.prefix) {
                continue;
            }
            match self.assignment[var].expect("trail variables are assigned") {
                Value::True | Value::False => {
                    functions.push(SnapshotFunction { lit, constant: true, implications: vec![] });
                }
                Value::PositiveImplications | Value::NegativeImplications => {
                    let implications = self.skolem[lit]
                        .implications()
                        .map(|cid| self.allocator[cid].lits().to_vec())
                        .collect();
                    functions.push(SnapshotFunction { lit, constant: false, implications });
                }
            }
        }
        functions
    }

    /// Records a cube as handled in every conflict-search structure. The
    /// domain solver has no function definitions, so only all-universal
    /// cubes are added there; skipping frontier cubes is conservative (the
    /// domain solver then under-approximates the covered domain).
    pub(crate) fn exclude_cube(&mut self, cube: &[Lit]) {
        self.conflict_check_exclude_cube(cube);
        if !self.cube_is_universal(cube) {
            return;
        }
        if let Some(domain) = &mut self.casesplits.domain {
            let excluded: Vec<_> = cube.iter().map(|&l| domain.0.lookup(!l)).collect();
            domain.0.add_clause(&excluded);
        }
    }

    fn cube_is_universal(&self, cube: &[Lit]) -> bool {
        cube.iter().all(|l| {
            let data = &self.vars[l.var()];
            data.scope.is_some() && data.is_universal(&self.prefix)
        })
    }

    fn ensure_domain_solver(&mut self) {
        if self.casesplits.domain.is_some() {
            return;
        }
        debug!("building the case-split domain solver");
        let mut domain = LookupSolver::<Varisat>::default();
        domain.set_var_count(self.vars.get_var_count());
        for case in &self.handled_cases {
            if !self.cube_is_universal(case.cube()) {
                continue;
            }
            let excluded: Vec<_> = case.cube().iter().map(|&l| domain.lookup(!l)).collect();
            domain.add_clause(&excluded);
        }
        self.casesplits.domain = Some(DomainSolver(domain));
        let mut occurrences: HashMap<Var, usize> = HashMap::new();
        for cid in self.allocator.ids().take(self.original_clause_count) {
            for l in self.allocator[cid].iter() {
                let data = &self.vars[l.var()];
                if data.scope.is_some() && data.is_universal(&self.prefix) {
                    *occurrences.entry(l.var()).or_default() += 1;
                }
            }
        }
        self.casesplits.occurrences = Some(occurrences);
    }

    /// Removes case assumptions whose decision levels were unwound.
    pub(crate) fn prune_cases_on_backtrack(&mut self, lvl: DecLvl) {
        // an assumption made at level `below + 1` survives iff that level
        // is kept
        self.casesplits.active.retain(|&(_, below)| below.successor() <= lvl);
    }
}
