use std::time::Duration;

#[derive(Debug, Default)]
pub(crate) struct Statistics {
    pub(crate) global: GlobalStats,
    pub(crate) skolem: SkolemStats,
    pub(crate) cegar: CegarStats,
    pub(crate) cases: CaseStats,
}

#[derive(Debug, Default)]
pub(crate) struct CegarStats {
    pub(crate) rounds: u32,
    pub(crate) cases: u32,
}

#[derive(Debug, Default)]
pub(crate) struct CaseStats {
    pub(crate) assumptions: u32,
    pub(crate) reassumed: u32,
    pub(crate) closed: u32,
}

#[derive(Debug, Default)]
pub(crate) struct GlobalStats {
    pub(crate) decisions: u32,
    /// trail length at the first propagation fixpoint of the search:
    /// how many variables the input structure determinizes up front
    pub(crate) initial_deterministic: usize,
    pub(crate) conflicts: u32,
    pub(crate) restarts: u32,
    pub(crate) added_clauses: u32,
    pub(crate) deleted_clauses: u32,
    /// completed in-place monotone extensions
    pub(crate) extensions: u32,
    pub(crate) solve_time: Duration,
}

#[derive(Debug, Default)]
pub(crate) struct SkolemStats {
    pub(crate) pure_vars: u32,
    pub(crate) local_det_checks: u32,
    pub(crate) local_conflict_checks: u32,
    pub(crate) global_conflict_checks: u32,
    /// wall time inside the determinacy check and inside the complete
    /// (SAT-backed) conflict check — the two candidates for where a
    /// long search actually spends itself
    pub(crate) det_check_time: Duration,
    pub(crate) global_check_time: Duration,
    /// of that, the time spent on checks that find *no* conflict — the
    /// ones a stronger filter in front of the solver could skip
    pub(crate) global_check_negative_time: Duration,
    /// level guards passed as assumptions, summed over the complete
    /// checks: one per live decision level, so it grows with search
    /// depth and is paid on every call
    pub(crate) check_assumptions: u64,
    pub(crate) conflict_check_reboots: u32,
    pub(crate) function_propagations: u32,
    pub(crate) constant_propagations: u32,
}
