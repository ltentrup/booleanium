use std::time::Duration;

#[derive(Debug, Default)]
pub(crate) struct Statistics {
    pub(crate) global: GlobalStats,
    pub(crate) skolem: SkolemStats,
}

#[derive(Debug, Default)]
pub(crate) struct GlobalStats {
    pub(crate) decisions: u32,
    pub(crate) conflicts: u32,
    pub(crate) added_clauses: u32,
    pub(crate) solve_time: Duration,
}

#[derive(Debug, Default)]
pub(crate) struct SkolemStats {
    pub(crate) local_det_checks: u32,
    pub(crate) local_conflict_checks: u32,
    pub(crate) global_conflict_checks: u32,
    pub(crate) function_propagations: u32,
    pub(crate) constant_propagations: u32,
}
