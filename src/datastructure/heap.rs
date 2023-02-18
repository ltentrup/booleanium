//! A priority heap for variables.

use super::VarVec;
use crate::literal::Var;

#[derive(Debug, Default, Clone)]
pub(crate) struct VarHeap<T> {
    /// The value for each variable
    values: VarVec<T>,
    /// The binary max-heap containing the variables
    heap: Vec<Var>,
    /// The positions of the variables in the heap
    positions: VarVec<Option<usize>>,
}

impl<T> VarHeap<T>
where
    T: Default + Copy + Ord,
{
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.values.set_var_count(count);
        self.positions.set_var_count(count);
    }

    /// Returns the variable with the highest value.
    pub(crate) fn peek(&self) -> Option<Var> {
        self.heap.first().copied()
    }

    pub(crate) fn pop(&mut self) -> Option<Var> {
        let var = *self.heap.first()?;
        self.remove(var);
        Some(var)
    }

    pub(crate) fn update_value<F>(&mut self, var: Var, update_fn: F) -> T
    where
        F: FnOnce(T) -> T,
    {
        let value = &mut self.values[var];
        let orig_value = *value;
        *value = update_fn(orig_value);
        let new_value = *value;
        if let Some(pos) = self.positions[var] {
            if new_value >= orig_value {
                self.sift_up(pos);
            } else {
                self.sift_down(pos);
            }
        }
        new_value
    }

    #[allow(dead_code)]
    pub(crate) fn get_value(&self, var: Var) -> T {
        self.values[var]
    }

    /// Adds the provided variable to the heap.
    pub(crate) fn add(&mut self, var: Var) {
        if self.positions[var].is_some() {
            // already contained in heap
            return;
        }
        // add var at the end and sift upwards
        let idx = self.heap.len();
        self.heap.push(var);
        self.positions[var] = Some(idx);
        self.sift_up(idx);
    }

    pub(crate) fn add_and_set(&mut self, var: Var, value: T) {
        if self.positions[var].is_some() {
            self.update_value(var, |_| value);
        } else {
            self.values[var] = value;
            self.add(var);
        }
    }

    /// Removes the provided variable from the heap.
    pub(crate) fn remove(&mut self, var: Var) {
        let Some(pos) = self.positions[var].take() else {
			return;
		};
        // swap it with the last element and sift it down afterwards
        self.heap.swap_remove(pos);
        if pos >= self.heap.len() {
            // we removed a child element from the heap
            return;
        }
        // update the moved variable
        let moved_var = self.heap[pos];
        self.positions[moved_var] = Some(pos);
        // move the variable back down if needed
        self.sift_down(pos);
    }

    pub(crate) fn contained(&self, var: Var) -> bool {
        self.positions[var].is_some()
    }

    pub(crate) fn clear(&mut self) {
        self.values.values_mut().for_each(|val| *val = T::default());
        self.heap.clear();
        self.positions.values_mut().for_each(|pos| *pos = None);
    }

    fn sift_up(&mut self, pos: usize) {
        let var = self.heap[pos];
        let Some(parent) = self.parent(pos) else {
			return;
		};
        let parent_var = self.heap[parent];
        if self.values[var] > self.values[parent_var] {
            self.swap(pos, parent);
            self.sift_up(parent);
        }
    }

    fn sift_down(&mut self, pos: usize) {
        let mut largest_idx = pos;

        if let Some(left_idx) = self
            .left(pos)
            .filter(|&idx| self.values[self.heap[idx]] > self.values[self.heap[largest_idx]])
        {
            largest_idx = left_idx;
        }

        if let Some(right_idx) = self
            .right(pos)
            .filter(|&idx| self.values[self.heap[idx]] > self.values[self.heap[largest_idx]])
        {
            largest_idx = right_idx;
        }

        if largest_idx != pos {
            // swap with largest child
            self.swap(pos, largest_idx);
            // continue recursively
            self.sift_down(largest_idx);
        }
    }

    fn swap(&mut self, a: usize, b: usize) {
        let var_a = self.heap[a];
        let var_b = self.heap[b];
        self.heap.swap(a, b);
        self.positions[var_a] = Some(b);
        self.positions[var_b] = Some(a);
    }

    /// Return the left child position, if it is in the heap
    fn left(&self, pos: usize) -> Option<usize> {
        let child_pos = 2 * pos + 1;
        Some(child_pos).filter(|&pos| pos < self.heap.len())
    }

    /// Return the right child position, if it is in the heap
    fn right(&self, pos: usize) -> Option<usize> {
        let child_pos = 2 * pos + 2;
        Some(child_pos).filter(|&pos| pos < self.heap.len())
    }

    /// Return the parent position, if it is in the heap
    fn parent(&self, pos: usize) -> Option<usize> {
        if pos == 0 {
            return None;
        }
        let parent_pos = (pos - 1) / 2;
        Some(parent_pos)
    }
}

impl<T> VarHeap<T>
where
    T: Default + Copy + Ord + std::ops::MulAssign,
{
    /// Rescaling values does not change the relative order in the heap.
    pub(crate) fn rescale(&mut self, rescale_factor: T) {
        self.values.values_mut().for_each(|value| {
            *value *= rescale_factor;
        });
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn heap() {
        let mut heap = VarHeap::<i32>::default();
        heap.set_var_count(4);
        let vars: Vec<_> = (0..4).map(Var::from_index).collect();
        for &var in &vars {
            heap.add(var);
        }

        heap.update_value(vars[2], |_| 2);
        heap.update_value(vars[1], |_| 6);

        assert_eq!(heap.peek(), Some(vars[1]));
        heap.remove(vars[1]);

        assert_eq!(heap.peek(), Some(vars[2]));

        heap.add(vars[1]);
        assert_eq!(heap.peek(), Some(vars[1]));
    }
}
