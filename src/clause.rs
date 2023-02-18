use crate::literal::{db::VariableDatabase, Lit, Var};

use self::{alloc::Allocator, binary::BinaryClauses, db::ClauseDatabase};

pub(crate) mod alloc;
pub(crate) mod binary;
pub(crate) mod db;
// pub(crate) mod views;

#[derive(Debug, Clone, Default)]
pub(crate) struct Clauses {
    pub(crate) alloc: Allocator,
    pub(crate) long: ClauseDatabase,
    pub(crate) binary: BinaryClauses,
    pub(crate) unit: Vec<Lit>,
}

impl Clauses {
    pub(crate) fn num_clauses(&self) -> u32 {
        (self.long.num_clauses() + self.binary.count() + self.unit.len()) as u32
    }

    pub(crate) fn add_unit_clause(&mut self, lit: Lit) {
        self.unit.push(lit);
    }

    pub(crate) fn add_binary_clause(&mut self, lits: [Lit; 2]) {
        self.binary.add(lits)
    }

    pub(crate) fn add_long_clause(&mut self, clause: &[Lit]) {
        let id = self.alloc.add(clause);
        self.long.add(id)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    lits: Vec<Lit>,
}

impl Clause {
    pub(crate) fn new(literals: &[Lit]) -> Self {
        // assert!(literals.len() > 2);
        Self { lits: literals.iter().copied().collect() }
    }

    pub(crate) fn iter(&self) -> std::slice::Iter<'_, Lit> {
        self.lits.iter()
    }

    pub(crate) fn reduce_universal(&mut self, vars: &VariableDatabase) {
        let max_scope = self
            .iter()
            .filter(|&&l| vars[l].existential())
            .map(|&l| vars[l].scope.unwrap_or_default())
            .max()
            .unwrap_or_default();
        self.lits.retain(|&lit| vars[lit].existential() || vars[lit].scope.unwrap() <= max_scope);
    }

    pub(crate) fn lits(&self) -> &[Lit] {
        &self.lits
    }

    pub(crate) fn lits_mut(&mut self) -> &mut [Lit] {
        &mut self.lits
    }

    pub(crate) fn resolve(&mut self, other: &Clause, self_lit: Lit) {
        assert!(self.lits.contains(&self_lit));
        assert!(other.lits.contains(&!self_lit));

        self.lits.retain(|&l| l != self_lit);
        self.lits.extend(other.lits.iter().filter(|&&l| l != !self_lit));
        self.lits.sort_unstable();
        self.lits.dedup();
    }
}

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for &lit in &self.lits {
            write!(f, "{} ", lit)?;
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
