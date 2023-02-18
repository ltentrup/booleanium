use crate::{
    datastructure::VarVec,
    literal::{Lit, Var},
};

#[derive(Debug, Clone, Default)]
pub(crate) struct Assignment {
    assignment: VarVec<Option<Value>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum Value {
    True,
    False,
    PositiveImplications,
    NegativeImplications,
}

impl Assignment {
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.assignment.set_var_count(count);
    }

    pub(crate) fn assign_constant(&mut self, lit: Lit) {
        self.assignment[lit.var()] =
            Some(if lit.is_positive() { Value::True } else { Value::False });
    }

    pub(crate) fn assign_function(&mut self, lit: Lit) {
        self.assignment[lit.var()] = Some(if lit.is_positive() {
            Value::PositiveImplications
        } else {
            Value::NegativeImplications
        });
    }

    pub(crate) fn unassign(&mut self, var: Var) {
        let old_value = self.assignment[var].take();
        assert!(old_value.is_some());
    }

    pub(crate) fn is_assigned(&self, var: Var) -> bool {
        self.assignment[var].is_some()
    }

    pub(crate) fn lit_is_true(&self, lit: Lit) -> bool {
        todo!();
        // self[lit] == Some(true)
    }

    pub(crate) fn lit_is_false(&self, lit: Lit) -> bool {
        todo!();
        // self[lit] == Some(false)
    }
}

impl std::ops::Index<Var> for Assignment {
    type Output = Option<Value>;

    fn index(&self, index: Var) -> &Self::Output {
        &self.assignment[index]
    }
}

impl std::ops::IndexMut<Var> for Assignment {
    fn index_mut(&mut self, index: Var) -> &mut Self::Output {
        &mut self.assignment[index]
    }
}

// impl std::ops::Index<Lit> for Assignment {
//     type Output = Option<Value>;

//     fn index(&self, index: Lit) -> &Self::Output {
//         if let Some(val) = self[index.var()] {
//             if index.is_negative() {}
//             if index.value_from_var(val) {
//                 &Some(true)
//             } else {
//                 &Some(false)
//             }
//         } else {
//             &None
//         }
//     }
// }

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn assignment() {
        let mut assignment = Assignment::default();
        assignment.set_var_count(10);
        let var1 = Var::from_dimacs(1);
        let lit1 = Lit::positive(var1);
        assert_eq!(assignment[var1], None);
        // assert_eq!(assignment[lit1], None);
        *assignment[var1].get_or_insert(Value::False) = Value::True;
    }
}
