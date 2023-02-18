use crate::literal::{db::VariableDatabase, Var};

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

#[derive(Debug, Clone)]
pub(crate) struct ScopeDatabase {
    scopes: Vec<Scope>,
}

impl Default for ScopeId {
    fn default() -> Self {
        ScopeDatabase::UNBOUND
    }
}

impl Default for ScopeDatabase {
    fn default() -> Self {
        // The first scope contains the unbound variables
        Self { scopes: vec![Scope { bound: Default::default(), ty: ScopeTy::Unbound }] }
    }
}

impl ScopeDatabase {
    pub(crate) const UNBOUND: ScopeId = ScopeId(0);

    pub(crate) fn new_quantifier(&mut self, quant: QuantTy) -> ScopeId {
        let id = ScopeId(self.scopes.len());
        self.scopes.push(Scope { bound: Vec::default(), ty: quant.into() });
        id
    }

    pub(crate) fn bind_variable(
        &mut self,
        vars: &mut VariableDatabase,
        scope: ScopeId,
        variable: Var,
    ) {
        let var_info = &mut vars[variable];
        assert!(var_info.scope.is_none(), "Variable {} bound multiple times", variable);
        var_info.scope = Some(scope);
        var_info.ty = self[scope].ty;
        self[scope].bound.push(variable);
    }
}

impl std::ops::Index<ScopeId> for ScopeDatabase {
    type Output = Scope;

    fn index(&self, index: ScopeId) -> &Self::Output {
        &self.scopes[index.0]
    }
}

impl std::ops::IndexMut<ScopeId> for ScopeDatabase {
    fn index_mut(&mut self, index: ScopeId) -> &mut Self::Output {
        &mut self.scopes[index.0]
    }
}

impl std::fmt::Display for QuantTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuantTy::Exists => write!(f, "e"),
            QuantTy::Forall => write!(f, "a"),
        }
    }
}

impl std::fmt::Display for ScopeDatabase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for scope in &self.scopes {
            write!(f, "{}", scope)?;
        }
        Ok(())
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
            write!(f, " {}", var)?;
        }
        writeln!(f, " 0")
    }
}
