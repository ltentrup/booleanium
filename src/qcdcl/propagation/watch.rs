use crate::{
    clause::{alloc::ClauseId, Clauses},
    datastructure::LitVec,
    literal::Lit,
};

#[derive(Debug, Clone, Copy)]
pub struct Watch {
    /// A reference to a clause where the watched literals
    /// are in the first and second position.
    pub(crate) clause: ClauseId,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct WatchList {
    watches: LitVec<Vec<Watch>>,
    enabled: bool,
}

impl WatchList {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.watches.set_var_count(count);
    }

    pub(crate) fn is_enabled(&self) -> bool {
        self.enabled
    }

    pub(crate) fn enable(&mut self, clauses: &Clauses) {
        if self.enabled {
            return;
        }
        self.enabled = true;
        self.watches.clear();
        for clause_id in clauses.long.iter() {
            let lits = clauses.alloc[clause_id].lits();
            self.watch_clause(clause_id, [lits[0], lits[1]]);
        }
    }

    fn watch_clause(&mut self, clause_id: ClauseId, lits: [Lit; 2]) {
        if !self.enabled {
            return;
        }

        for lit in lits {
            self.add_watch(lit, Watch { clause: clause_id });
        }
    }

    pub(super) fn add_watch(&mut self, lit: Lit, watch: Watch) {
        self.watches[!lit].push(watch);
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
