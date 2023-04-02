//! VSIDS branching heuristics

use crate::{datastructure::heap::VarHeap, literal::Var};
use ordered_float::NotNan;

const BUMP_INITIAL: f64 = 1.0;
const DECAY_INITIAL: f64 = 0.95;
const RESCALE_LIMIT: f64 = f64::MAX / 16.0;

#[derive(Debug, Clone)]
pub(crate) struct Vsids {
    heap: VarHeap<NotNan<f64>>,
    /// the value used for bumping activity values
    bump: NotNan<f64>,
    /// The decay factor
    decay: NotNan<f64>,
}

impl Default for Vsids {
    fn default() -> Self {
        Self {
            heap: VarHeap::default(),
            bump: NotNan::new(BUMP_INITIAL).unwrap(),
            decay: NotNan::new(DECAY_INITIAL).unwrap(),
        }
    }
}

impl Vsids {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.heap.set_var_count(count);
    }

    /// Returns the variable with the highest activity score.
    pub(crate) fn peek(&self) -> Option<Var> {
        self.heap.peek()
    }

    /// Increase activity score for the provided variable.
    pub(crate) fn bump(&mut self, var: Var) {
        let new_value = self.heap.update_value(var, |old| old + self.bump);
        if *new_value >= RESCALE_LIMIT {
            self.rescale();
        }
    }

    /// Decay all variable activities.
    pub(crate) fn decay(&mut self) {
        self.bump /= self.decay;
        if *self.bump >= RESCALE_LIMIT {
            self.rescale();
        }
    }

    /// Rescale activities to prevent overflow
    fn rescale(&mut self) {
        let rescale_factor = RESCALE_LIMIT.recip();
        self.heap.rescale(NotNan::new(rescale_factor).unwrap());
        self.bump *= rescale_factor;
    }

    /// Adds the provided variable to the heap.
    pub(crate) fn add(&mut self, var: Var) {
        self.heap.add(var);
    }

    /// Removes the provided variable from the heap.
    pub(crate) fn remove(&mut self, var: Var) {
        self.heap.remove(var);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn heap() {
        let mut vsids = Vsids::default();
        vsids.set_var_count(4);
        let vars: Vec<_> = (0..4).map(Var::from_index).collect();
        for &var in &vars {
            vsids.add(var);
        }

        vsids.bump(vars[2]);
        vsids.bump(vars[1]);
        vsids.bump(vars[1]);

        assert_eq!(vsids.peek(), Some(vars[1]));
        vsids.remove(vars[1]);

        assert_eq!(vsids.peek(), Some(vars[2]));

        vsids.add(vars[1]);
        assert_eq!(vsids.peek(), Some(vars[1]));
    }

    #[test]
    fn decay() {
        let mut vsids = Vsids::default();
        vsids.set_var_count(4);
        let vars: Vec<_> = (0..4).map(Var::from_index).collect();
        for &var in &vars {
            vsids.add(var);
        }

        for &var in &vars {
            vsids.bump(var);
            vsids.decay();
        }

        for (&left, &right) in vars.iter().zip(vars.iter().skip(1)) {
            assert!(vsids.heap.get_value(left) < vsids.heap.get_value(right));
        }

        vsids.bump(vars[0]);
        assert_eq!(vsids.peek(), Some(vars[0]));
    }
}
