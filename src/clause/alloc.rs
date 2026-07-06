//! Clause allocator

use super::Clause;
use crate::literal::Lit;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ClauseId(usize);

#[derive(Debug, Clone, Default)]
pub(crate) struct Allocator {
    clauses: Vec<Clause>,
    /// Reference count of registrations as implication clause. Locked
    /// clauses act as reasons on the trail and must not be deleted.
    locks: Vec<u32>,
}

impl Allocator {
    pub(crate) fn reserve(&mut self, num_clauses: u32) {
        self.clauses.reserve(usize::try_from(num_clauses).unwrap());
    }

    pub(crate) fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Iterates over the ids of all allocated clauses in allocation order.
    pub(crate) fn ids(&self) -> impl Iterator<Item = ClauseId> {
        (0..self.clauses.len()).map(ClauseId)
    }

    pub(crate) fn add(&mut self, clause: &[Lit]) -> ClauseId {
        let clause = Clause::new(clause);
        let idx = self.clauses.len();
        self.clauses.push(clause);
        self.locks.push(0);
        ClauseId(idx)
    }

    /// Marks the clause as registered implication clause.
    pub(crate) fn lock(&mut self, cid: ClauseId) {
        self.locks[cid.0] += 1;
    }

    /// Removes one implication registration of the clause.
    pub(crate) fn unlock(&mut self, cid: ClauseId) {
        debug_assert!(self.locks[cid.0] > 0);
        self.locks[cid.0] -= 1;
    }

    /// Whether the clause is currently registered as an implication clause.
    pub(crate) fn is_locked(&self, cid: ClauseId) -> bool {
        self.locks[cid.0] > 0
    }

    /// Deletes the clause, freeing its literal storage. The id stays valid
    /// but must not be referenced anymore.
    pub(crate) fn delete(&mut self, cid: ClauseId) {
        debug_assert!(!self.is_locked(cid));
        self.clauses[cid.0] = Clause::new(&[]);
    }
}

impl std::ops::Index<ClauseId> for Allocator {
    type Output = Clause;

    fn index(&self, index: ClauseId) -> &Self::Output {
        &self.clauses[index.0]
    }
}

impl std::ops::IndexMut<ClauseId> for Allocator {
    fn index_mut(&mut self, index: ClauseId) -> &mut Self::Output {
        &mut self.clauses[index.0]
    }
}
