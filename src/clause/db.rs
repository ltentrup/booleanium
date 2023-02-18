//! Clause database

use super::alloc::ClauseId;

#[derive(Debug, Clone, Default)]
pub(crate) struct ClauseDatabase {
    clauses: Vec<ClauseId>,
}

impl ClauseDatabase {
    pub(crate) fn set_num_clauses(&mut self, num_clauses: u32) {
        self.clauses.reserve(usize::try_from(num_clauses).unwrap())
    }

    pub(crate) fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = ClauseId> + '_ {
        self.clauses.iter().copied()
    }

    pub(crate) fn add(&mut self, clause: ClauseId) {
        self.clauses.push(clause);
    }
}
