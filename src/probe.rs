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

/// Propagation waves (calls to `IncDet::propagate`), the complete
/// conflict checks inside them, and how many waves ended on a conflict.
///
/// The batching factor for a *batched* conflict check: one query per
/// wave asking whether any variable determinized in it is conflicted,
/// instead of one query per variable. Checks per wave is what such a
/// query would replace; waves that end on a conflict are the ones where
/// the batch would have to be re-run after the repair.
pub static WAVES: AtomicU64 = AtomicU64::new(0);
pub static WAVES_CONFLICTED: AtomicU64 = AtomicU64::new(0);
pub static COMPLETE_CHECKS: AtomicU64 = AtomicU64::new(0);
/// Decisions, the next coarser boundary a batched check could sit on.
pub static DECISIONS: AtomicU64 = AtomicU64::new(0);

/// Sampled conflict-check states whose Skolem functions were built as
/// BDDs over the universals, how many fit inside the node budget, and
/// the largest single function seen among those that fit.
///
/// The feasibility question for a BDD-backed conflict check: the check
/// itself becomes a pointer comparison, so the only thing that can
/// sink it is whether the functions fit.
pub static BDD_SAMPLES: AtomicU64 = AtomicU64::new(0);
pub static BDD_FITS: AtomicU64 = AtomicU64::new(0);
pub static BDD_PEAK_TOTAL: AtomicU64 = AtomicU64::new(0);

/// Records the largest value seen.
pub(crate) fn observe_max(counter: &AtomicU64, value: u64) {
    counter.fetch_max(value, Ordering::Relaxed);
}

/// Whether to measure the cone of influence, which costs a traversal of
/// the determinized formula per check and so distorts everything else.
/// Set `BOOLEANIUM_PROBE_CONE` to enable.
/// Node budget for the sampled conflict-check BDDs: past this the
/// answer is "it does not fit", which is the answer that matters.
pub const BDD_LIMIT: usize = 1_000_000;

/// Whether to sample conflict-check states as BDDs, which costs a
/// trail walk per sample. Set `BOOLEANIUM_PROBE_BDD` to enable.
pub(crate) fn bdd_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("BOOLEANIUM_PROBE_BDD").is_ok())
}

pub(crate) fn cone_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("BOOLEANIUM_PROBE_CONE").is_ok())
}

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
        &WAVES,
        &WAVES_CONFLICTED,
        &COMPLETE_CHECKS,
        &DECISIONS,
        &BDD_SAMPLES,
        &BDD_FITS,
        &BDD_PEAK_TOTAL,
    ] {
        counter.store(0, Ordering::Relaxed);
    }
}

/// What a batched conflict check — one query per propagation wave
/// instead of one per determinized variable — would replace.
#[must_use]
pub fn wave_report() -> Option<String> {
    let waves = get(&WAVES);
    if waves == 0 {
        return None;
    }
    let (checks, conflicted) = (get(&COMPLETE_CHECKS), get(&WAVES_CONFLICTED));
    #[allow(clippy::cast_precision_loss)]
    let per_wave = checks as f64 / waves as f64;
    #[allow(clippy::cast_precision_loss)]
    let rate = 100.0 * conflicted as f64 / waves as f64;
    let decisions = get(&DECISIONS);
    #[allow(clippy::cast_precision_loss)]
    let per_decision = if decisions == 0 { 0.0 } else { checks as f64 / decisions as f64 };
    Some(format!(
        "{waves} waves, {checks} complete checks ({per_wave:.1} per wave, \
         {per_decision:.1} per decision), {conflicted} waves conflicted ({rate:.0}%)"
    ))
}

/// Whether the conflict-check state fits in BDDs over the universals.
#[must_use]
pub fn bdd_report() -> Option<String> {
    let samples = get(&BDD_SAMPLES);
    if samples == 0 {
        return None;
    }
    let fits = get(&BDD_FITS);
    #[allow(clippy::cast_precision_loss)]
    let rate = 100.0 * fits as f64 / samples as f64;
    Some(format!(
        "{fits}/{samples} sampled states fit as BDDs ({rate:.0}%), \
         peak package {} nodes",
        get(&BDD_PEAK_TOTAL),
    ))
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
