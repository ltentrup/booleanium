//! Case-split extension, adapted from "Understanding and Extending
//! Incremental Determinization for 2QBF" (Rabe, Tentrup, Rasmussen,
//! Seshia, CAV 2018).
//!
//! When the search stalls — many conflicts without a verdict, typically on
//! instances whose CEGAR cubes do not generalize — the universal domain is
//! split on a universal variable `u` and the two specialized instances
//! `φ[u:=1]` and `φ[u:=0]` are solved in isolation by fresh sub-solvers:
//! the split is the syntactic identity `∀u. φ ≡ φ[u:=1] ∧ φ[u:=0]`.
//! Specialization removes satisfied clauses and strips falsified literals,
//! which turns circuit gates into constants that the sub-solvers propagate
//! cheaply.
//!
//! The sub-solvers are kept for certification: the combined Skolem function
//! is the if-then-else over `u` of the branch functions, so a satisfiable
//! result is verified by verifying both branches.

use crate::{
    incdet::IncDet,
    literal::{Lit, Var},
    SolverResult,
};
use std::collections::HashMap;
use tracing::info;

/// Maximum case-split recursion depth (at most `2^depth` sub-instances).
const MAX_SPLIT_DEPTH: u32 = 12;

/// A performed case split with its solved sub-instances.
#[derive(Debug)]
pub(crate) struct CaseSplit {
    #[allow(dead_code)]
    pub(crate) var: Var,
    pub(crate) positive: IncDet,
    pub(crate) negative: IncDet,
}

impl IncDet {
    /// Whether the stalled search should be split into cases.
    pub(crate) fn should_case_split(&self) -> bool {
        self.options.case_splits
            && self.split_depth < MAX_SPLIT_DEPTH
            && self.stats.global.conflicts >= self.options.case_split_threshold
    }

    /// Splits the universal domain on the most frequent universal variable
    /// and solves both specializations. Returns `None` if no universal
    /// variable occurs in the matrix.
    pub(crate) fn solve_by_case_split(&mut self) -> Option<SolverResult> {
        let var = self.split_variable()?;
        info!(
            "case split on universal {var} at depth {} after {} conflicts",
            self.split_depth, self.stats.global.conflicts
        );
        let mut positive = self.specialize(Lit::positive(var));
        let result_pos = positive._solve();
        let result = match result_pos {
            SolverResult::Unsatisfiable | SolverResult::Unknown => result_pos,
            SolverResult::Satisfiable => {
                let mut negative = self.specialize(Lit::negative(var));
                let result_neg = negative._solve();
                self.split = Some(Box::new(CaseSplit { var, positive, negative }));
                result_neg
            }
        };
        info!("case split on {var} resolved: {result}");
        Some(result)
    }

    /// Builds a fresh solver for the matrix specialized by `lit`: clauses
    /// containing `lit` are satisfied and dropped, occurrences of `¬lit`
    /// are stripped. The prefix is inherited unchanged — the split variable
    /// simply no longer occurs.
    fn specialize(&self, lit: Lit) -> IncDet {
        let mut sub = IncDet::with_options(self.options);
        sub.split_depth = self.split_depth + 1;
        for scope in &self.prefix {
            if !scope.variables.is_empty() {
                sub._quantify(scope.quantifier, &scope.variables);
            }
        }
        let mut stripped = Vec::new();
        for cid in self.allocator.ids().take(self.original_clause_count) {
            let clause = &self.allocator[cid];
            if clause.iter().any(|&l| l == lit) {
                continue;
            }
            stripped.clear();
            stripped.extend(clause.iter().copied().filter(|&l| l != !lit));
            sub._add_clause(&stripped);
        }
        sub
    }

    /// The universal variable with the most occurrences in the original
    /// matrix.
    fn split_variable(&self) -> Option<Var> {
        let mut occurrences: HashMap<Var, usize> = HashMap::new();
        for cid in self.allocator.ids().take(self.original_clause_count) {
            for l in self.allocator[cid].iter() {
                let data = &self.vars[l.var()];
                if data.scope.is_some() && data.is_universal(&self.prefix) {
                    *occurrences.entry(l.var()).or_default() += 1;
                }
            }
        }
        occurrences.into_iter().max_by_key(|&(var, count)| (count, var)).map(|(var, _)| var)
    }
}
