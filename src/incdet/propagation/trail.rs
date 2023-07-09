use crate::literal::Lit;

#[derive(Debug, Clone, Default)]
pub(crate) struct Trail {
    /// List of assignments in chronological order
    trail: Vec<Lit>,
    /// Indices into trail marking the decision levels
    decisions: Vec<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct DecLvl(usize);

impl Trail {
    pub(crate) fn push(&mut self, lit: Lit) {
        self.trail.push(lit);
    }

    pub(crate) fn decision_level(&self) -> DecLvl {
        DecLvl(self.decisions.len())
    }

    pub(crate) fn add_decision(&mut self, lit: Lit) {
        let trail_idx = self.trail.len();
        self.trail.push(lit);
        self.decisions.push(trail_idx);
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &Lit> + DoubleEndedIterator {
        self.trail.iter()
    }

    pub(crate) fn iter_decisions(&self) -> impl Iterator<Item = &Lit> {
        self.decisions.iter().map(|&idx| &self.trail[idx])
    }

    pub(crate) fn is_decision(&self, lit: Lit) -> bool {
        self.iter_decisions().any(|&l| l == lit)
    }

    pub(crate) fn backtrack_to<F>(&mut self, lvl: DecLvl, callback: F)
    where
        F: FnMut(Lit),
    {
        let trail_idx = self.decisions[lvl.0];
        self.decisions.truncate(lvl.0);
        self.trail[trail_idx..].iter().copied().rev().for_each(callback);
        self.trail.truncate(trail_idx);
    }

    pub(crate) fn len(&self) -> usize {
        self.trail.len()
    }
}

impl DecLvl {
    pub(crate) const ROOT: DecLvl = DecLvl(0);

    pub(crate) fn is_root(self) -> bool {
        self == Self::ROOT
    }

    pub(crate) fn successor(self) -> Self {
        Self(self.0 + 1)
    }
}

impl std::fmt::Display for DecLvl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
