//! QRAT proof emission for unsatisfiable results (see [`crate::qrat`]
//! for the rules and the checker).
//!
//! The incremental hooks (learnt clauses, root constants, deletions) log
//! from the paths that produce them; this module finishes a refutation
//! at the two sites that declare unsatisfiability from a *pointwise*
//! conflict: a conflict at the root level, and a conflict analysis whose
//! clause contains no existential literal above the root. In both cases
//! the offending assignment fires one implication per existential
//! literal, so continuing the resolution along the trail eliminates
//! every existential literal and leaves a clause of universal literals,
//! which universal reduction empties.

use crate::{
    incdet::{Conflict, IncDet},
    literal::Lit,
};
use std::collections::HashSet;

impl IncDet {
    /// The emitted QRAT refutation of an unsatisfiable run, if proof
    /// logging is enabled ([`crate::incdet::Options::proof`]) and the run
    /// stayed within the proof rules. Must only be called after
    /// [`IncDet::solve`] returned
    /// [`crate::SolverResult::Unsatisfiable`].
    #[must_use]
    pub fn qrat_proof(&self) -> Option<String> {
        self.proof_log.as_ref().and_then(crate::qrat::ProofLog::render)
    }

    /// Logs the refutation of a root-level conflict: the nucleus
    /// resolvent of the conflicting variable, completed to a clause
    /// without existential literals.
    pub(crate) fn log_root_refutation(&mut self, conflict: &Conflict) {
        if self.proof_log.is_none() {
            return;
        }
        let mut seed = Vec::new();
        for lit in [conflict.var.negative(), conflict.var.positive()] {
            let mut found = false;
            for implication in &self.graph[lit] {
                let other = &self.allocator[implication.clause];
                if other.iter().any(|l| conflict.assignment.contains(l)) {
                    continue;
                }
                for &l in other.iter() {
                    if l.var() != conflict.var && !seed.contains(&l) {
                        seed.push(l);
                    }
                }
                found = true;
                break;
            }
            if !found && self.assignment.constant_value(lit) != Some(true) {
                // no firing implication and no constant for this
                // polarity: the conflict shape is outside the proof rules
                self.poison_proof();
                return;
            }
        }
        self.log_completed_refutation(&conflict.assignment, seed);
    }

    /// Logs the refutation of an analysis clause whose existential
    /// literals are all root-level (the analysis aborts with
    /// unsatisfiability there): completes it along the trail and emits
    /// the resulting universal clause plus the empty clause.
    pub(crate) fn log_seed_refutation(&mut self, conflict: &Conflict, seed: Vec<Lit>) {
        if self.proof_log.is_none() {
            return;
        }
        self.log_completed_refutation(&conflict.assignment, seed);
    }

    /// Resolves every existential literal out of `seed` using the
    /// implications that fire under `assignment` (constants drop their
    /// falsified literals — their units are proof lines), then logs the
    /// universal remainder and the empty clause.
    fn log_completed_refutation(&mut self, assignment: &HashSet<Lit>, seed: Vec<Lit>) {
        let mut clause = seed;
        let trail: Vec<Lit> = self.trail.iter().copied().collect();
        for tlit in trail.into_iter().rev() {
            let var = tlit.var();
            let Some(&present) = clause.iter().find(|l| l.var() == var) else {
                continue;
            };
            let data = &self.vars[var];
            if data.scope.is_some() && data.is_universal(&self.prefix) {
                continue;
            }
            match self.assignment.constant_value(present) {
                Some(false) => {
                    // falsified by a constant whose unit is a proof line
                    clause.retain(|l| l.var() != var);
                    continue;
                }
                Some(true) => {
                    // the clause is satisfied at the point — not a
                    // refutation shape the rules cover
                    self.poison_proof();
                    return;
                }
                None => {}
            }
            let forced = !present;
            let mut resolved = false;
            for implication in &self.graph[forced] {
                let reason = implication.reason(&self.allocator);
                if !reason.is_implied(forced, assignment) {
                    continue;
                }
                let premises: Vec<Lit> =
                    reason.iter().copied().filter(|l| l.var() != var).collect();
                clause.retain(|l| l.var() != var);
                for l in premises {
                    if !clause.contains(&l) {
                        clause.push(l);
                    }
                }
                resolved = true;
                break;
            }
            if !resolved {
                self.poison_proof();
                return;
            }
        }
        let existential_left = clause.iter().any(|l| {
            let data = &self.vars[l.var()];
            data.scope.is_none() || data.is_existential(&self.prefix)
        });
        if existential_left {
            self.poison_proof();
            return;
        }
        if let Some(log) = &mut self.proof_log {
            log.add(&clause);
            log.add(&[]);
        }
    }

    fn poison_proof(&mut self) {
        if let Some(log) = &mut self.proof_log {
            tracing::debug!("proof logging: refutation outside the proof rules, dropping proof");
            log.poisoned = true;
        }
    }
}
