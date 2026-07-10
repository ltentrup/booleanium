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
    pub(crate) conflicts: u32,
    pub(crate) restarts: u32,
    pub(crate) added_clauses: u32,
    pub(crate) deleted_clauses: u32,
    pub(crate) solve_time: Duration,
}

#[derive(Debug, Default)]
pub(crate) struct SkolemStats {
    pub(crate) pure_vars: u32,
    pub(crate) local_det_checks: u32,
    pub(crate) local_conflict_checks: u32,
    pub(crate) global_conflict_checks: u32,
    pub(crate) conflict_check_reboots: u32,
    pub(crate) function_propagations: u32,
    pub(crate) constant_propagations: u32,
}
