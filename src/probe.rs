//! Process-global measurement counters (feature `probe`).
//!
//! [`crate::incdet::stats`] is per-solver, and a solve creates throwaway
//! query solvers whose stats dumps are easy to double-count when a
//! measurement is aggregated out of the log — a mistake that once
//! produced a published figure that was wrong by a factor of five. These
//! counters are process-global and additive, so every event is counted
//! exactly once however many solvers a run builds.
//!
//! Nothing here is on a path that ships: the module exists only under
//! the `probe` feature, and the call sites are `#[cfg]`-gated too.

use std::sync::atomic::{AtomicU64, Ordering};

/// Complete (SAT-backed) conflict checks the cone was measured for.
pub static CONE_SAMPLES: AtomicU64 = AtomicU64::new(0);
/// Implication clauses in the cone of influence of the checked variable.
pub static CONE_CLAUSES: AtomicU64 = AtomicU64::new(0);
/// Variables in that cone.
pub static CONE_VARS: AtomicU64 = AtomicU64::new(0);
/// Of the cone clauses, those belonging to root-level variables — the
/// ones the incremental check solver holds permanently.
pub static CONE_ROOT_CLAUSES: AtomicU64 = AtomicU64::new(0);
/// Implication clauses of the whole determinized formula, i.e. what the
/// check solver carries.
pub static DETERMINIZED_CLAUSES: AtomicU64 = AtomicU64::new(0);
/// Assigned variables at the time of the check.
pub static DETERMINIZED_VARS: AtomicU64 = AtomicU64::new(0);

/// Complete checks that tried a remembered conflicting universal
/// assignment as an assumption before searching freely, how many of
/// those found the conflict that way, and what the tries cost (in
/// nanoseconds).
pub static HINT_TRIES: AtomicU64 = AtomicU64::new(0);
pub static HINT_HITS: AtomicU64 = AtomicU64::new(0);
pub static HINT_NANOS: AtomicU64 = AtomicU64::new(0);

pub(crate) fn add(counter: &AtomicU64, by: u64) {
    counter.fetch_add(by, Ordering::Relaxed);
}

fn get(counter: &AtomicU64) -> u64 {
    counter.load(Ordering::Relaxed)
}

/// Resets every counter, so a driver can measure one instance at a time.
pub fn reset() {
    for counter in [
        &CONE_SAMPLES,
        &CONE_CLAUSES,
        &CONE_VARS,
        &CONE_ROOT_CLAUSES,
        &DETERMINIZED_CLAUSES,
        &DETERMINIZED_VARS,
        &HINT_TRIES,
        &HINT_HITS,
        &HINT_NANOS,
    ] {
        counter.store(0, Ordering::Relaxed);
    }
}

/// How well the conflict hint pays: how often a remembered conflicting
/// universal assignment, tried as an assumption, already answers the
/// check — and what the tries cost in total.
#[must_use]
pub fn hint_report() -> Option<String> {
    let tries = get(&HINT_TRIES);
    if tries == 0 {
        return None;
    }
    let hits = get(&HINT_HITS);
    #[allow(clippy::cast_precision_loss)]
    let rate = 100.0 * hits as f64 / tries as f64;
    let spent = std::time::Duration::from_nanos(get(&HINT_NANOS));
    Some(format!("{hits}/{tries} hints hit ({rate:.0}%), {spent:.3?} spent trying"))
}

/// How much of the determinized formula a complete conflict check
/// actually depends on, averaged over the checks — `None` when no
/// complete check ran.
#[must_use]
pub fn cone_report() -> Option<String> {
    let samples = get(&CONE_SAMPLES);
    if samples == 0 {
        return None;
    }
    #[allow(clippy::cast_precision_loss)]
    let mean = |counter: &AtomicU64| get(counter) as f64 / samples as f64;
    let (clauses, all_clauses) = (mean(&CONE_CLAUSES), mean(&DETERMINIZED_CLAUSES));
    let (vars, all_vars) = (mean(&CONE_VARS), mean(&DETERMINIZED_VARS));
    let share = |part: f64, whole: f64| if whole == 0.0 { 0.0 } else { 100.0 * part / whole };
    Some(format!(
        "{samples} checks: cone {clauses:.0}/{all_clauses:.0} clauses ({:.0}%), \
         {vars:.0}/{all_vars:.0} vars ({:.0}%), {:.0}% of the cone at root",
        share(clauses, all_clauses),
        share(vars, all_vars),
        share(mean(&CONE_ROOT_CLAUSES), clauses),
    ))
}
