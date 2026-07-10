use crate::{clause::alloc::ClauseId, datastructure::LitVec, incdet::propagation::trail::DecLvl};
use std::collections::BTreeMap;

pub(crate) type Skolem = LitVec<Implications>;

/// Representation of a (partial) Skolem function as implication clauses.
#[derive(Debug, Clone, Default)]
pub(crate) struct Implications {
    implications: BTreeMap<DecLvl, Vec<ClauseId>>,
    /// Total number of implication clauses across all levels.
    count: usize,
}

impl Implications {
    pub(crate) fn add_implication(&mut self, clause_id: ClauseId, lvl: DecLvl) {
        self.implications.entry(lvl).or_default().push(clause_id);
        self.count += 1;
    }

    pub(crate) fn implications(&self) -> impl Iterator<Item = ClauseId> + '_ {
        self.implications.values().flat_map(IntoIterator::into_iter).copied()
    }

    pub(crate) fn len(&self) -> usize {
        self.count
    }

    fn backtrack_to<F>(&mut self, lvl: DecLvl, removed_callback: &mut F)
    where
        F: FnMut(ClauseId),
    {
        // backtracking to `lvl` means that we keep all entries with level <= `lvl`
        let removed = self.implications.split_off(&lvl.successor());
        for cid in removed.values().flatten() {
            self.count -= 1;
            removed_callback(*cid);
        }
    }
}

impl Skolem {
    /// Removes all implications above `lvl`, reporting every removed clause
    /// to the callback (used to unlock the clauses in the allocator).
    pub(crate) fn backtrack_to<F>(&mut self, lvl: DecLvl, mut removed_callback: F)
    where
        F: FnMut(ClauseId),
    {
        self.iter_mut().for_each(|imp| imp.backtrack_to(lvl, &mut removed_callback));
    }
}
