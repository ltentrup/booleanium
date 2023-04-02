//! Clause allocator

use super::Clause;
use crate::literal::Lit;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ClauseId(usize);

#[derive(Debug, Clone, Default)]
pub(crate) struct Allocator {
    clauses: Vec<Clause>,
}

impl Allocator {
    pub(crate) fn reserve(&mut self, num_clauses: u32) {
        self.clauses.reserve(usize::try_from(num_clauses).unwrap());
    }

    #[allow(unused)]
    pub(crate) fn len(&self) -> usize {
        self.clauses.len()
    }

    pub(crate) fn add(&mut self, clause: &[Lit]) -> ClauseId {
        let clause = Clause::new(clause);
        let idx = self.clauses.len();
        self.clauses.push(clause);
        ClauseId(idx)
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
