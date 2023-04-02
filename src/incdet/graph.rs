//! Implication graph

use crate::{
    clause::alloc::ClauseId, datastructure::LitVec, incdet::propagation::trail::DecLvl,
    literal::Lit,
};

pub(crate) type ImplGraph = LitVec<Vec<Impl>>;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Impl {
    pub(crate) lit: Lit,
    pub(crate) clause: ClauseId,
    pub(crate) dec_lvl: DecLvl,
}

impl ImplGraph {
    pub(crate) fn backtrack_to(&mut self, lvl: DecLvl) {
        self.iter_mut().for_each(|imps| {
            imps.retain(|imp| imp.dec_lvl <= lvl);
        });
    }
}
