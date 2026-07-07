//! Clause activities for the learnt-clause deletion policy.
//!
//! Every learnt clause used as a reason during conflict analysis is bumped;
//! the bump grows geometrically per conflict (equivalent to decaying all
//! activities), so recently useful clauses survive
//! [`crate::incdet::IncDet::reduce_learnts`].

use crate::clause::alloc::ClauseId;
use std::collections::HashMap;

#[derive(Debug)]
pub(crate) struct ClauseActivity {
    activity: HashMap<ClauseId, f64>,
    increment: f64,
}

impl Default for ClauseActivity {
    fn default() -> Self {
        Self { activity: HashMap::new(), increment: 1.0 }
    }
}

/// Per-conflict decay factor of clause activities.
const DECAY: f64 = 0.999;

/// Rescale threshold to keep the geometric bump within `f64` range.
const RESCALE_LIMIT: f64 = 1e100;

impl ClauseActivity {
    pub(crate) fn bump(&mut self, cid: ClauseId) {
        let activity = self.activity.entry(cid).or_insert(0.0);
        *activity += self.increment;
        if *activity > RESCALE_LIMIT {
            for activity in self.activity.values_mut() {
                *activity /= RESCALE_LIMIT;
            }
            self.increment /= RESCALE_LIMIT;
        }
    }

    pub(crate) fn decay(&mut self) {
        self.increment /= DECAY;
    }

    pub(crate) fn get(&self, cid: ClauseId) -> f64 {
        self.activity.get(&cid).copied().unwrap_or(0.0)
    }

    pub(crate) fn remove(&mut self, cid: ClauseId) {
        self.activity.remove(&cid);
    }
}
