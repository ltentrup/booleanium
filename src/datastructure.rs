use crate::literal::{Lit, Var};
use std::ops::{Index, IndexMut};

pub(crate) mod heap;

/// Wrapper around a `Vec` that is indexed by [`Var`].
#[derive(Debug, Clone)]
pub(crate) struct VarVec<T>(Vec<T>);

impl<T: Default> VarVec<T> {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.0.resize_with(count, Default::default);
    }

    pub(crate) fn get_var_count(&self) -> usize {
        self.0.len()
    }
}

impl<T> Default for VarVec<T> {
    fn default() -> Self {
        Self(Vec::default())
    }
}

impl<T> VarVec<Vec<T>> {
    pub(crate) fn clear(&mut self) {
        self.0.iter_mut().for_each(Vec::clear);
    }
}

impl<T> VarVec<T> {
    pub(crate) fn iter(&self) -> impl Iterator<Item = (Var, &T)> {
        self.0
            .iter()
            .enumerate()
            .map(|(idx, value)| (Var::from_index(idx.try_into().unwrap()), value))
    }

    pub(crate) fn values_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut()
    }

    pub(crate) fn get(&self, index: Var) -> Option<&T> {
        self.0.get(index.as_index())
    }
}

impl<T> Index<Var> for VarVec<T> {
    type Output = T;

    fn index(&self, index: Var) -> &Self::Output {
        &self.0[index.as_index()]
    }
}

impl<T> IndexMut<Var> for VarVec<T> {
    fn index_mut(&mut self, index: Var) -> &mut Self::Output {
        &mut self.0[index.as_index()]
    }
}

/// Wrapper around a `Vec` that is indexed by [`Lit`].
#[derive(Debug, Clone)]
pub(crate) struct LitVec<T>(Vec<T>);

impl<T: Default> LitVec<T> {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.0.resize_with(count * 2, Default::default);
    }
}

impl<T> Default for LitVec<T> {
    fn default() -> Self {
        Self(Vec::default())
    }
}

impl<T> LitVec<Vec<T>> {
    pub(crate) fn clear(&mut self) {
        self.0.iter_mut().for_each(Vec::clear);
    }
}

impl<T> LitVec<T> {
    pub(crate) fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut()
    }
}

impl<T> Index<Lit> for LitVec<T> {
    type Output = T;

    fn index(&self, index: Lit) -> &Self::Output {
        &self.0[index.as_index()]
    }
}

impl<T> IndexMut<Lit> for LitVec<T> {
    fn index_mut(&mut self, index: Lit) -> &mut Self::Output {
        &mut self.0[index.as_index()]
    }
}
