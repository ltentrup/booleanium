//! A straight-forward representation of a QBF in CNF.

use crate::{
    literal::{Lit, Var},
    qdimacs::FromQdimacs,
    QuantTy,
};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct QCNF {
    pub prefix: Vec<(QuantTy, Vec<Var>)>,
    pub matrix: Vec<Vec<Lit>>,
}

impl QCNF {
    /// How many existential variables the matrix *determines* from the
    /// universals — the ceiling on what determinization could ever
    /// recover, whatever the detector or the encoding.
    ///
    /// A variable is definable from the universals iff no two models
    /// agreeing on every universal disagree on it (Padoa). Two copies
    /// of the matrix sharing the universals decide it: if
    /// `F(U,E) ∧ F(U,E′) ∧ v ∧ ¬v′` is unsatisfiable then `v` is a
    /// function of the universals, which is exactly the condition for
    /// determinizing it at the root.
    ///
    /// Returns `(definable, sampled, total existentials)`, or `None`
    /// when the matrix itself is unsatisfiable — every variable is then
    /// vacuously definable, since no two models can disagree when there
    /// are none, and the count would measure nothing. At most `limit`
    /// variables are sampled (evenly spread), so the answer is a
    /// proportion on instances too large to ask about exhaustively.
    #[must_use]
    pub fn definable_from_universals(&self, limit: usize) -> Option<(usize, usize, usize)> {
        use crate::sat::{varisat::Varisat, SatSolver};

        let universals: std::collections::HashSet<Var> = self
            .prefix
            .iter()
            .filter(|(q, _)| *q == QuantTy::Forall)
            .flat_map(|(_, vars)| vars.iter().copied())
            .collect();
        // Everything that is not universal, which is what the solver
        // determinizes: the prefix existentials *and* the free
        // variables, which are treated as outermost existentials and
        // are absent from the prefix. Counting only the prefix made the
        // denominator too small and the recovered fraction exceed 100%.
        let mut existentials: Vec<Var> = self
            .matrix
            .iter()
            .flatten()
            .map(|l| l.var())
            .filter(|v| !universals.contains(v))
            .collect();
        existentials.sort_unstable();
        existentials.dedup();
        if existentials.is_empty() {
            return Some((0, 0, 0));
        }
        let max_var = self
            .matrix
            .iter()
            .flatten()
            .map(|l| l.var().to_dimacs())
            .chain(universals.iter().chain(existentials.iter()).map(|v| v.to_dimacs()))
            .max()
            .unwrap_or(0);

        // the primed copy renames everything that is not universal
        let prime = |l: Lit| -> i32 {
            let (var, sign) = (l.var().to_dimacs(), if l.is_positive() { 1 } else { -1 });
            sign * if universals.contains(&l.var()) { var } else { var + max_var }
        };

        let mut plain = Varisat::default();
        let mut doubled = Varisat::default();
        for solver in [&mut plain, &mut doubled] {
            solver.add_variables(2 * max_var as usize + 2);
        }
        let encode = |solver: &mut Varisat, lit: i32| -> <Varisat as SatSolver>::Lit {
            let _ = solver;
            <Varisat as SatSolver>::Lit::from_dimacs(isize::try_from(lit).expect("fits"))
        };
        for clause in &self.matrix {
            let original: Vec<_> =
                clause.iter().map(|&l| encode(&mut plain, l.to_dimacs())).collect();
            plain.add_clause(&original);
            let copy: Vec<_> = clause.iter().map(|&l| encode(&mut plain, l.to_dimacs())).collect();
            doubled.add_clause(&copy);
            let primed: Vec<_> = clause.iter().map(|&l| encode(&mut plain, prime(l))).collect();
            doubled.add_clause(&primed);
        }
        if !plain.solve().ok()? {
            return None;
        }
        let total = existentials.len();
        let step = ((total + limit.max(1) - 1) / limit.max(1)).max(1);
        let sample: Vec<Var> = existentials.iter().copied().step_by(step).collect();
        let mut definable = 0;
        for var in &sample {
            let positive = encode(&mut plain, var.to_dimacs());
            let negated = encode(&mut plain, -prime(Lit::positive(*var)));
            if !doubled.solve_with_assumptions(&[positive, negated]).ok()? {
                definable += 1;
            }
        }
        Some((definable, sample.len(), total))
    }

    #[must_use]
    pub fn new(prefix: &[(QuantTy, &[u32])], matrix: &[&[i32]]) -> Self {
        let prefix = prefix
            .iter()
            .map(|&(q, vars)| {
                (q, vars.iter().map(|&var| Var::from_dimacs(var.try_into().unwrap())).collect())
            })
            .collect();
        let matrix = matrix
            .iter()
            .map(|&lits| lits.iter().map(|&lit| Lit::from_dimacs(lit)).collect())
            .collect();
        QCNF { prefix, matrix }
    }

    fn num_clauses(&self) -> u32 {
        self.matrix.len().try_into().unwrap()
    }

    fn num_variables(&self) -> u32 {
        self.prefix
            .iter()
            .flat_map(|(_, bound)| bound)
            .map(|var| var.to_dimacs())
            .chain(self.matrix.iter().flatten().map(|lit| lit.to_dimacs()))
            .max()
            .unwrap_or_default()
            .try_into()
            .unwrap()
    }

    #[allow(dead_code)]
    pub(crate) fn is_2qbf(&self) -> bool {
        matches!(&self.prefix[..], &[(QuantTy::Forall, _), (QuantTy::Exists, _)])
    }

    /// Checks a winning move of the universal player: under every
    /// extension of the (partial) universal assignment `witness`, no
    /// assignment of the remaining variables satisfies the matrix. Only
    /// usable for tiny instances (test oracle).
    #[cfg(test)]
    pub(crate) fn is_winning_universal_move(&self, witness: &[i32]) -> bool {
        use crate::literal::Lit;
        let witness: Vec<Lit> = witness.iter().map(|&l| Lit::from_dimacs(l)).collect();
        // enumerate all assignments of every variable of the matrix; the
        // witness must block all of them
        let mut vars: Vec<Var> = self.matrix.iter().flatten().map(|l| l.var()).collect();
        vars.sort_unstable();
        vars.dedup();
        let n = vars.len();
        assert!(n <= 20, "oracle only for tiny instances");
        'outer: for point in 0u32..(1 << n) {
            let truth = |l: Lit| -> bool {
                let idx = vars.binary_search(&l.var()).expect("var collected");
                let value = point & (1 << idx) != 0;
                value == l.is_positive()
            };
            for &w in &witness {
                if !truth(w) {
                    continue 'outer;
                }
            }
            if self.matrix.iter().all(|c| c.iter().any(|&l| truth(l))) {
                // a satisfying extension exists: not a winning move
                return false;
            }
        }
        true
    }
}

impl FromQdimacs for QCNF {
    fn set_num_variables(&mut self, _: u32) {}

    fn set_num_clauses(&mut self, _: u32) {}

    fn quantify(&mut self, quant: crate::QuantTy, vars: &[Var]) {
        self.prefix.push((quant, vars.to_owned()));
    }

    fn add_clause(&mut self, lits: &[Lit]) {
        self.matrix.push(lits.to_owned());
    }
}

impl std::fmt::Display for QCNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "p cnf {} {}", self.num_variables(), self.num_clauses())?;
        for (q, vars) in &self.prefix {
            writeln!(
                f,
                "{q} {} 0",
                vars.iter().map(ToString::to_string).collect::<Vec<_>>().join(" ")
            )?;
        }
        for clause in &self.matrix {
            for lit in clause {
                write!(f, "{lit} ")?;
            }
            writeln!(f, "0")?;
        }
        Ok(())
    }
}

#[cfg(test)]
macro_rules! qcnf_core {
    ($prefix:expr, $matrix:expr,) => {
		(crate::qcnf::QCNF::new(&$prefix, &$matrix))
	};
    ($prefix:expr, $matrix:expr, a $( $x:literal )* ; $($tail:tt)* ) => {{
		$prefix.push((crate::quantifier::QuantTy::Forall, &[ $( $x ),* ]));
        qcnf_core![$prefix, $matrix, $($tail)*]
    }};
    ($prefix:expr, $matrix:expr, e $( $x:literal )* ; $($tail:tt)* ) => {{
		$prefix.push((crate::quantifier::QuantTy::Exists, &[ $( $x ),* ]));
        qcnf_core![$prefix, $matrix,$($tail)*]
    }};
    ($prefix:expr, $matrix:expr, $( $x:literal )* ; $($tail:tt)* ) => {{
		$matrix.push(&[ $( $x ),* ]);
        qcnf_core![$prefix, $matrix, $($tail)*]
    }};
}

/// Macro that creates a [`QCNF`] instance from a QDIMACS-like representation.
/// The main differences are:
/// * No support for comments
/// * No header line
/// * Lines are seperated by `;`, whereas QDIMACS uses `0`.
///
/// # Example
/// ```
/// let qcnf = qcnf_formula![
///     a 1 2;
///     e 3;
///     1 2;
/// ];
/// ```
///
#[cfg(test)]
macro_rules! qcnf_formula {
	($($tail:tt)*) => {
		 {
			 let mut prefix: Vec<(crate::quantifier::QuantTy, &[u32])> = Vec::new();
			 let mut matrix: Vec<&[i32]> = Vec::new();
			 qcnf_core![prefix, matrix, $($tail)*]
		 }

	};
}

#[cfg(test)]
impl QCNF {
    /// Evaluates the QBF semantics by brute-force enumeration of all
    /// assignments. Only usable for tiny instances; serves as a trivially
    /// correct reference for differential testing.
    pub(crate) fn brute_force(&self) -> crate::SolverResult {
        use std::collections::{HashMap, HashSet};

        fn eval(
            vars: &[(QuantTy, Var)],
            assignment: &mut HashMap<Var, bool>,
            matrix: &[Vec<crate::literal::Lit>],
        ) -> bool {
            let Some(&(quant, var)) = vars.first() else {
                return matrix.iter().all(|clause| {
                    clause.iter().any(|lit| {
                        assignment
                            .get(&lit.var())
                            .map_or(false, |&value| value == lit.is_positive())
                    })
                });
            };
            let rest = &vars[1..];
            let mut branch = |value: bool| {
                assignment.insert(var, value);
                let result = eval(rest, assignment, matrix);
                assignment.remove(&var);
                result
            };
            match quant {
                QuantTy::Exists => branch(false) || branch(true),
                QuantTy::Forall => branch(false) && branch(true),
            }
        }

        // free variables are existentially quantified at the outermost level
        let bound: HashSet<Var> =
            self.prefix.iter().flat_map(|(_, vars)| vars.iter().copied()).collect();
        let mut free: Vec<Var> = Vec::new();
        for lit in self.matrix.iter().flatten() {
            if !bound.contains(&lit.var()) && !free.contains(&lit.var()) {
                free.push(lit.var());
            }
        }
        let vars: Vec<(QuantTy, Var)> = free
            .into_iter()
            .map(|var| (QuantTy::Exists, var))
            .chain(
                self.prefix
                    .iter()
                    .flat_map(|(quant, vars)| vars.iter().map(move |&var| (*quant, var))),
            )
            .collect();
        assert!(vars.len() <= 24, "brute-force evaluation only supports tiny instances");
        let mut assignment = HashMap::new();
        if eval(&vars, &mut assignment, &self.matrix) {
            crate::SolverResult::Satisfiable
        } else {
            crate::SolverResult::Unsatisfiable
        }
    }
}

/// Provides a strategy for randomly generating QCNFs.
#[cfg(test)]
pub(crate) mod strategy {
    use super::{QuantTy, Var, QCNF};
    use crate::literal::strategy::lit;
    use proptest::{
        collection::{self, SizeRange},
        prelude::*,
    };

    /// A strategy to generate a QCNF with the provided parameters.
    pub(crate) fn qcnf(
        alternations: impl Into<SizeRange>,
        alternation_len: impl Into<SizeRange>,
        clauses: impl Into<SizeRange>,
        clause_len: impl Into<SizeRange>,
    ) -> impl Strategy<Value = QCNF> {
        let alternations = alternations.into();
        let alternation_len = alternation_len.into();
        let clauses = clauses.into();
        let clause_len = clause_len.into();

        prefix(alternations, alternation_len)
            .prop_flat_map(move |(max_var_idx, prefix)| {
                let clauses = clauses.clone();
                let clause_len = clause_len.clone();
                collection::vec(collection::vec(lit(0..max_var_idx), clause_len), clauses).prop_map(
                    move |matrix| {
                        let prefix = prefix.clone();
                        QCNF { prefix, matrix }
                    },
                )
            })
            .no_shrink()
    }

    /// A strategy to generate a quantifier prefix with the provided parameters.
    fn prefix(
        alternations: SizeRange,
        alternation_len: SizeRange,
    ) -> impl Strategy<Value = (u32, Vec<(QuantTy, Vec<Var>)>)> {
        let alternation_lens =
            collection::vec(collection::vec(Just(()), alternation_len), alternations);
        (alternation_lens).prop_map(|alternation_lens| {
            let mut var_index = 0;
            let prefix = alternation_lens
                .iter()
                .enumerate()
                .map(|(idx, alternation)| {
                    (
                        if idx % 2 == 0 { QuantTy::Exists } else { QuantTy::Forall },
                        alternation
                            .iter()
                            .map(|_| {
                                let var = Var::from_index(var_index);
                                var_index += 1;
                                var
                            })
                            .collect(),
                    )
                })
                .rev()
                .collect();
            (var_index, prefix)
        })
    }
}

#[cfg(test)]
mod test {

    #[test]
    fn qcnf_macro() {
        let qcnf = qcnf_formula![
            a 1 2;
            e 3;
            1 2;
        ];
        assert_eq!(qcnf.num_clauses(), 1);
        assert_eq!(qcnf.num_variables(), 3);
    }
}
