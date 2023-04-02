use crate::literal::Var;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantTy {
    Exists,
    Forall,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ScopeTy {
    Unbound,
    Existential,
    Universal,
}

impl Default for ScopeTy {
    fn default() -> Self {
        Self::Unbound
    }
}

impl From<QuantTy> for ScopeTy {
    fn from(quantifier: QuantTy) -> Self {
        match quantifier {
            QuantTy::Exists => Self::Existential,
            QuantTy::Forall => Self::Universal,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScopeId(usize);

#[derive(Debug, Clone)]
pub struct Scope {
    bound: Vec<Var>,
    ty: ScopeTy,
}

impl std::fmt::Display for QuantTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuantTy::Exists => write!(f, "e"),
            QuantTy::Forall => write!(f, "a"),
        }
    }
}

impl std::fmt::Display for Scope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.ty {
            ScopeTy::Unbound => return Ok(()),
            ScopeTy::Existential => write!(f, "e")?,
            ScopeTy::Universal => write!(f, "a")?,
        }
        for &var in &self.bound {
            write!(f, " {var}")?;
        }
        writeln!(f, " 0")
    }
}
