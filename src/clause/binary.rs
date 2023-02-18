//! Original implementation from https://github.com/jix/varisat

use crate::literal::Lit;

/// Binary clauses.
#[derive(Debug, Default, Clone)]
pub(crate) struct BinaryClauses {
    by_lit: Vec<Vec<Lit>>,
    count: usize,
}

impl BinaryClauses {
    /// Update structures for a new variable count.
    pub(crate) fn set_var_count(&mut self, count: usize) {
        self.by_lit.resize_with(count * 2, Default::default);
    }

    /// Add a binary clause.
    pub(super) fn add(&mut self, lits: [Lit; 2]) {
        for (&lit, &other) in lits.iter().zip(lits.iter().rev()) {
            self.by_lit[(!lit).as_index()].push(other);
        }
        self.count += 1;
    }

    /// Implications of a given literal
    pub(crate) fn implied(&self, lit: Lit) -> &[Lit] {
        &self.by_lit[lit.as_index()]
    }

    /// Number of binary clauses.
    pub(crate) fn count(&self) -> usize {
        self.count
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = [Lit; 2]> + '_ {
        self.by_lit.iter().enumerate().flat_map(|(idx, implied)| {
            let lit = Lit::from_index(idx);
            implied
                .iter()
                .filter_map(move |&other| if lit < other { Some([!lit, other]) } else { None })
        })
    }
}
