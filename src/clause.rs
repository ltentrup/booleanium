use crate::literal::Lit;

pub(crate) mod alloc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    lits: Vec<Lit>,
}

impl Clause {
    pub(crate) fn new(literals: &[Lit]) -> Self {
        // assert!(literals.len() > 2);
        Self { lits: literals.to_vec() }
    }

    pub(crate) fn iter(&self) -> std::slice::Iter<'_, Lit> {
        self.lits.iter()
    }

    pub(crate) fn lits(&self) -> &[Lit] {
        &self.lits
    }

    #[allow(dead_code)]
    pub(crate) fn lits_mut(&mut self) -> &mut [Lit] {
        &mut self.lits
    }
}

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for &lit in &self.lits {
            write!(f, "{lit} ")?;
        }
        write!(f, "0")
    }
}

impl<'a> IntoIterator for &'a Clause {
    type Item = &'a Lit;
    type IntoIter = std::slice::Iter<'a, Lit>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
