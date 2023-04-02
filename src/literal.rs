use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var {
    index: u32,
}

impl Var {
    pub(crate) const MAX_VAR: Var = Var { index: (u32::MAX >> 1) - 1 };

    pub fn from_index(index: u32) -> Self {
        assert!(index <= Self::MAX_VAR.index);
        Self { index }
    }

    pub fn from_dimacs(var: i32) -> Self {
        assert!(var > 0);
        Self::from_index((var - 1).try_into().expect("var - 1 is greater or equal to 0"))
    }

    pub fn to_dimacs(self) -> i32 {
        (self.index + 1).try_into().expect("index + 1 should always be smaller than i32::MAX")
    }

    pub(crate) fn as_index(self) -> usize {
        usize::try_from(self.index).unwrap()
    }

    pub(crate) fn positive(self) -> Lit {
        Lit::positive(self)
    }

    pub(crate) fn negative(self) -> Lit {
        Lit::negative(self)
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_dimacs())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit {
    /// internal representation of a literal
    repr: u32,
}

#[cfg(not(kani))]
const _: () = assert!(std::mem::size_of::<Lit>() == 4);

impl Lit {
    pub(crate) const MIN_LIT: Lit = Lit::negative(Var::MAX_VAR);
    pub(crate) const MAX_LIT: Lit = Lit::positive(Var::MAX_VAR);

    const fn from_var(variable: Var, polarity: bool) -> Self {
        #[cfg(not(kani))]
        assert!(variable.index <= Var::MAX_VAR.index);
        Self { repr: (variable.index << 1) | (!polarity as u32) }
    }

    pub(crate) const fn positive(variable: Var) -> Self {
        Self::from_var(variable, true)
    }

    pub(crate) const fn negative(variable: Var) -> Self {
        Self::from_var(variable, false)
    }

    pub(crate) fn var(self) -> Var {
        Var { index: self.repr >> 1 }
    }

    pub(crate) fn is_negative(self) -> bool {
        (self.repr & 1) == 1
    }

    pub(crate) fn is_positive(self) -> bool {
        !self.is_negative()
    }

    pub(crate) fn negated(self) -> Self {
        Self { repr: self.repr ^ 1 }
    }

    pub fn from_dimacs(lit: i32) -> Self {
        Self::from_var(Var::from_dimacs(lit.abs()), lit > 0)
    }

    pub fn to_dimacs(self) -> i32 {
        if self.is_negative() {
            -self.var().to_dimacs()
        } else {
            self.var().to_dimacs()
        }
    }

    pub(crate) fn as_index(self) -> usize {
        self.repr as usize
    }

    #[allow(dead_code)]
    pub(crate) fn from_index(idx: usize) -> Lit {
        Lit { repr: idx.try_into().expect("index should be smaller than u32::MAX") }
    }
}

impl Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_dimacs())
    }
}

impl std::ops::Not for Lit {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self { repr: self.repr ^ 1 }
    }
}

/// Helper function to remove `var` from a [`Lit`] iterator
pub(crate) fn filter_var(var: Var) -> impl Fn(&&Lit) -> bool {
    move |l| l.var() != var
}

/// Helper function to remove `lit` from a [`Lit`] iterator
pub(crate) fn filter_lit(lit: Lit) -> impl Fn(&&Lit) -> bool {
    move |&&l| l != lit
}

/// Helper struct which implements [`Display`] for [`Lit`] slices
#[derive(Debug, Clone, Copy)]
pub(crate) struct LitSlice<'a>(&'a [Lit]);

impl<'a> From<&'a [Lit]> for LitSlice<'a> {
    fn from(slice: &'a [Lit]) -> Self {
        Self(slice)
    }
}

impl<'a> Display for LitSlice<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "(")?;
        for (idx, lit) in self.0.iter().enumerate() {
            if idx > 0 {
                write!(f, " ")?;
            }
            write!(f, "{lit}")?;
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn negation() {
        let a = Var::from_dimacs(1);
        let l = Lit::positive(a);
        let neg_l = !l;
        assert_ne!(l, neg_l);
        assert_eq!(neg_l, Lit::negative(a));
        assert_eq!(l, !neg_l);
    }

    #[test]
    fn max_var() {
        let _max = Var::from_index(Var::MAX_VAR.index);
    }

    #[test]
    #[should_panic]
    fn larger_than_max_var() {
        let _max = Var::from_index(Var::MAX_VAR.index + 1);
    }
}

/// Provides a strategy for randomly generating variables and literals.
#[cfg(test)]
pub(crate) mod strategy {
    use super::{Lit, Var};
    use proptest::{bool, prelude::*};

    fn var(index: impl Strategy<Value = u32>) -> impl Strategy<Value = Var> {
        index.prop_map(Var::from_index)
    }

    pub(crate) fn lit(index: impl Strategy<Value = u32>) -> impl Strategy<Value = Lit> {
        (var(index), bool::ANY).prop_map(|(var, is_negative)| Lit::from_var(var, is_negative))
    }
}
