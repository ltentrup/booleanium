use crate::{clause::alloc::ClauseId, datastructure::LitVec, literal::Lit};

#[derive(Debug, Clone, Copy)]
pub struct Watch {
    /// A reference to a clause where the watched literal is contained.
    pub(crate) clause: ClauseId,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct WatchList {
    enabled: bool,
    watches: LitVec<Vec<Watch>>,
}

impl WatchList {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.watches.set_var_count(count);
    }

    pub(crate) fn clear(&mut self) {
        self.enabled = false;
        self.watches.clear();
    }

    pub(super) fn add_watch(&mut self, lit: Lit, watch: Watch) {
        self.watches[lit].push(watch);
    }

    pub(crate) fn enabled(&self) -> bool {
        self.enabled
    }

    pub(crate) fn set_enabled(&mut self) {
        self.enabled = true;
    }

    /// Removes all watches that refer to one of the given clauses.
    pub(crate) fn remove_clauses(&mut self, deleted: &std::collections::HashSet<ClauseId>) {
        self.watches.iter_mut().for_each(|list| list.retain(|w| !deleted.contains(&w.clause)));
    }
}

impl std::ops::Index<Lit> for WatchList {
    type Output = Vec<Watch>;

    fn index(&self, lit: Lit) -> &Self::Output {
        &self.watches[lit]
    }
}

impl std::ops::IndexMut<Lit> for WatchList {
    fn index_mut(&mut self, lit: Lit) -> &mut Self::Output {
        &mut self.watches[lit]
    }
}
