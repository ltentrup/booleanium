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

    pub(crate) fn is_2qbf(&self) -> bool {
        match &self.prefix[..] {
            &[(QuantTy::Forall, _), (QuantTy::Exists, _)] => true,
            _ => false,
        }
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
