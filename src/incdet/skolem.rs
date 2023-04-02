use crate::{
    clause::alloc::{Allocator, ClauseId},
    datastructure::LitVec,
    incdet::propagation::trail::DecLvl,
};
use std::collections::BTreeMap;

pub(crate) type Skolem = LitVec<Implications>;

/// Representation of a (partial) Skolem function as implication clauses.
#[derive(Debug, Clone, Default)]
pub(crate) struct Implications {
    implications: BTreeMap<DecLvl, Vec<ClauseId>>,
}

impl Implications {
    pub(crate) fn add_implication(&mut self, clause_id: ClauseId, lvl: DecLvl) {
        self.implications.entry(lvl).or_default().push(clause_id);
    }

    pub(crate) fn implications(&self) -> impl Iterator<Item = ClauseId> + '_ {
        self.implications.values().flat_map(IntoIterator::into_iter).copied()
    }

    pub(crate) fn len(&self) -> usize {
        self.implications.values().map(Vec::len).sum()
    }

    pub(crate) fn lit_count(&self, alloc: &Allocator) -> usize {
        self.implications().map(|c| alloc[c].lits().len()).sum()
    }

    fn backtrack_to(&mut self, lvl: DecLvl) {
        // backtrackign to `lvl` means that we keep all entries with level <= `lvl`
        self.implications.split_off(&lvl.successor());
    }
}

impl Skolem {
    pub(crate) fn backtrack_to(&mut self, lvl: DecLvl) {
        self.iter_mut().for_each(|imp| imp.backtrack_to(lvl));
    }
}
