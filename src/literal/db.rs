//! Variable database

use super::{Lit, Var};
use crate::quantifier::{ScopeId, ScopeTy};

#[derive(Debug, Clone, Default)]
pub(crate) struct VariableDatabase {
    variables: Vec<VariableData>,
}

#[derive(Debug, Clone, Default)]
pub struct VariableData {
    pub(crate) scope: Option<ScopeId>,
    pub(crate) ty: ScopeTy,
}

impl VariableDatabase {
    pub(crate) fn new_variables(&mut self, num_variables: u32) -> impl Iterator<Item = Var> {
        let first_var = self.next_variable();
        self.variables.resize_with(
            self.variables.len() + usize::try_from(num_variables).unwrap(),
            Default::default,
        );
        let end_var = self.next_variable();
        (first_var.index..end_var.index).map(Var::from_index)
    }

    pub(crate) fn next_variable(&self) -> Var {
        Var::from_index(u32::try_from(self.variables.len()).unwrap())
    }

    pub(crate) fn var_count(&self) -> usize {
        self.variables.len()
    }
}

impl VariableData {
    pub(crate) fn existential(&self) -> bool {
        matches!(self.ty, ScopeTy::Existential)
    }

    pub(crate) fn unbound(&self) -> bool {
        matches!(self.ty, ScopeTy::Unbound)
    }

    pub(crate) fn existential_or_unbound(&self) -> bool {
        matches!(self.ty, ScopeTy::Existential | ScopeTy::Unbound)
    }

    pub(crate) fn universal(&self) -> bool {
        matches!(self.ty, ScopeTy::Universal)
    }
}

impl std::ops::Index<Var> for VariableDatabase {
    type Output = VariableData;

    fn index(&self, index: Var) -> &Self::Output {
        &self.variables[index.as_index()]
    }
}

impl std::ops::IndexMut<Var> for VariableDatabase {
    fn index_mut(&mut self, index: Var) -> &mut Self::Output {
        &mut self.variables[index.as_index()]
    }
}

impl std::ops::Index<Lit> for VariableDatabase {
    type Output = VariableData;

    fn index(&self, index: Lit) -> &Self::Output {
        &self[index.var()]
    }
}

impl std::ops::IndexMut<Lit> for VariableDatabase {
    fn index_mut(&mut self, index: Lit) -> &mut Self::Output {
        &mut self[index.var()]
    }
}
