//! QRAT refutation proofs for unsatisfiable results: emission types and
//! an internal checker.
//!
//! With CEGAR and case splits disabled, every clause the solver derives
//! is justified by rules a propositional/QBF proof checker can replay
//! without trusting the solver:
//!
//! * **Learnt clauses** are conclusions of linear resolution chains over
//!   implication clauses (originals and earlier learnt clauses), so they
//!   check by *reverse unit propagation* (RUP): assume every literal of
//!   the clause false and propagate — the chain's reasons become units in
//!   reverse order and run into a conflict.
//! * **Forced root constants** (units derived by constant propagation)
//!   check by RUP for the same reason.
//! * **Pure constants** are winnability-preserving choices, not
//!   consequences; they check by the QRAT rule: every clause containing
//!   the opposite literal is satisfied by an earlier constant, so each
//!   outer resolvent contains a unit of the formula and is an asymmetric
//!   tautology.
//! * **Universal reduction** appears only in its ∀∃ endgame form: a
//!   clause without existential literals reduces to the empty clause.
//!
//! The proof is emitted in the standard QRAT format (clause addition
//! lines, `d`-prefixed deletion lines, `0`-terminated), so external
//! checkers can consume it; [`check_refutation`] is the independent
//! in-tree checker the differential fuzz drives.

use crate::{literal::Lit, qcnf::QCNF, QuantTy};
use std::collections::HashSet;
use std::fmt::Write;

/// One emitted proof step.
#[derive(Debug, Clone)]
pub(crate) enum ProofLine {
    Add(Vec<Lit>),
    Delete(Vec<Lit>),
}

/// The proof log of a solver run.
#[derive(Debug, Clone, Default)]
pub(crate) struct ProofLog {
    pub(crate) lines: Vec<ProofLine>,
    /// set once the search starts: clause additions before that are the
    /// original formula and are not proof steps
    pub(crate) active: bool,
    /// set when the run took a step the proof rules cannot express; a
    /// poisoned log yields no proof instead of an invalid one
    pub(crate) poisoned: bool,
}

impl ProofLog {
    pub(crate) fn add(&mut self, lits: &[Lit]) {
        if self.active && !self.poisoned {
            self.lines.push(ProofLine::Add(lits.to_vec()));
        }
    }

    pub(crate) fn delete(&mut self, lits: &[Lit]) {
        if self.active && !self.poisoned {
            self.lines.push(ProofLine::Delete(lits.to_vec()));
        }
    }

    pub(crate) fn render(&self) -> Option<String> {
        if self.poisoned {
            return None;
        }
        let mut out = String::new();
        for line in &self.lines {
            let (prefix, lits) = match line {
                ProofLine::Add(lits) => ("", lits),
                ProofLine::Delete(lits) => ("d ", lits),
            };
            let mut rendered = String::from(prefix);
            for &l in lits {
                let _ = write!(rendered, "{} ", l.to_dimacs());
            }
            rendered.push('0');
            out.push_str(&rendered);
            out.push('\n');
        }
        Some(out)
    }
}

/// A propositional assignment during RUP checking, indexed by DIMACS
/// variable magnitude.
fn value(assigned: &[Option<bool>], l: Lit) -> Option<bool> {
    let raw = l.to_dimacs();
    assigned[raw.unsigned_abs() as usize].map(|v| v == (raw > 0))
}

/// Reverse unit propagation: assumes every literal of `clause` false and
/// unit-propagates over `formula`; `true` means a conflict was reached,
/// certifying that `formula` implies `clause`.
fn rup(formula: &[Vec<Lit>], clause: &[Lit], max_var: usize) -> bool {
    let mut assigned: Vec<Option<bool>> = vec![None; max_var + 1];
    for &l in clause {
        let raw = l.to_dimacs();
        let slot = &mut assigned[raw.unsigned_abs() as usize];
        if slot.is_some() && *slot != Some(raw < 0) {
            // the clause is a tautology; nothing to certify
            return true;
        }
        *slot = Some(raw < 0);
    }
    loop {
        let mut progress = false;
        for c in formula {
            let mut unassigned = None;
            let mut satisfied = false;
            let mut open = 0usize;
            for &l in c {
                match value(&assigned, l) {
                    Some(true) => {
                        satisfied = true;
                        break;
                    }
                    Some(false) => {}
                    None => {
                        open += 1;
                        unassigned = Some(l);
                    }
                }
            }
            if satisfied || open > 1 {
                continue;
            }
            match unassigned {
                None => return true,
                Some(l) => {
                    let raw = l.to_dimacs();
                    assigned[raw.unsigned_abs() as usize] = Some(raw > 0);
                    progress = true;
                }
            }
        }
        if !progress {
            return false;
        }
    }
}

/// Checks a QRAT refutation of `qcnf`. Accepts the RUP, unit-QRAT, and
/// ∀∃ universal-reduction rules described in the module documentation.
///
/// # Errors
///
/// Returns the first unjustified or malformed proof line.
// the checker reads best as one piece: load, reduce, then the per-line rules
#[allow(clippy::too_many_lines)]
pub fn check_refutation(qcnf: &QCNF, proof: &str) -> Result<(), String> {
    // block index and quantifier per declared variable; free variables
    // count as existentials of the outermost block
    let mut scope: std::collections::HashMap<i32, (usize, QuantTy)> =
        std::collections::HashMap::new();
    for (block, (quant, vars)) in qcnf.prefix.iter().enumerate() {
        for v in vars {
            scope.insert(v.to_dimacs(), (block, *quant));
        }
    }
    let universal = |l: &Lit| matches!(scope.get(&l.to_dimacs().abs()), Some((_, QuantTy::Forall)));
    // universal reduction: a universal literal quantified after every
    // existential literal of the clause is removed (in a clause without
    // existential literals, all of them are)
    let reduce = |c: &mut Vec<Lit>| {
        let innermost_existential = c
            .iter()
            .filter(|l| !universal(l))
            .map(|l| scope.get(&l.to_dimacs().abs()).map_or(0, |&(block, _)| block))
            .max();
        match innermost_existential {
            Some(bound) => c.retain(|l| {
                !universal(l)
                    || scope.get(&l.to_dimacs().abs()).is_some_and(|&(block, _)| block < bound)
            }),
            None => c.clear(),
        }
    };

    // tautological clauses are logically inert — never unit, never
    // falsified — and their outer resolvents self-subsume, so they are
    // dropped up front (the solver drops them during preprocessing too)
    let tautological = |c: &[Lit]| c.iter().any(|&l| c.contains(&!l));
    let dedup = |c: &Vec<Lit>| {
        let mut lits = c.clone();
        lits.sort_unstable_by_key(|l| l.to_dimacs());
        lits.dedup();
        lits
    };
    let mut formula: Vec<Vec<Lit>> = qcnf
        .matrix
        .iter()
        .filter(|c| !tautological(c))
        .map(|c| {
            let mut lits = dedup(c);
            reduce(&mut lits);
            lits
        })
        .collect();
    let mut max_var = qcnf
        .matrix
        .iter()
        .flatten()
        .map(|l| l.to_dimacs().unsigned_abs() as usize)
        .max()
        .unwrap_or(0)
        .max(
            qcnf.prefix
                .iter()
                .flat_map(|(_, vars)| vars.iter())
                .map(|v| v.to_dimacs().unsigned_abs() as usize)
                .max()
                .unwrap_or(0),
        );

    for (no, line) in proof.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let (delete, rest) = match line.strip_prefix("d ") {
            Some(rest) => (true, rest),
            None => (false, line),
        };
        let mut lits: Vec<Lit> = Vec::new();
        let mut terminated = false;
        for token in rest.split_ascii_whitespace() {
            let raw: i32 =
                token.parse().map_err(|_| format!("line {}: invalid literal {token}", no + 1))?;
            if raw == 0 {
                terminated = true;
                break;
            }
            max_var = max_var.max(raw.unsigned_abs() as usize);
            lits.push(Lit::from_dimacs(raw));
        }
        if !terminated {
            return Err(format!("line {}: missing terminating 0", no + 1));
        }
        if delete {
            let set: HashSet<Lit> = lits.iter().copied().collect();
            let position = formula
                .iter()
                .position(|c| c.len() == lits.len() && c.iter().all(|l| set.contains(l)));
            match position {
                Some(i) => {
                    formula.swap_remove(i);
                }
                None => return Err(format!("line {}: deleted clause not in formula", no + 1)),
            }
            continue;
        }
        if lits.is_empty() {
            // the endgame: a propositional conflict, or a clause that
            // universal reduction emptied (stored as the empty clause)
            if rup(&formula, &[], max_var) || formula.iter().any(Vec::is_empty) {
                return Ok(());
            }
            return Err(format!("line {}: empty clause is not justified", no + 1));
        }
        let justified = rup(&formula, &lits, max_var)
            || (lits.len() == 1 && {
                // unit QRAT: every outer resolvent with a clause containing
                // the opposite literal must be an asymmetric tautology
                let unit = lits[0];
                formula.iter().filter(|c| c.contains(&!unit)).all(|c| {
                    let resolvent: Vec<Lit> = c.iter().copied().filter(|&l| l != !unit).collect();
                    rup(&formula, &resolvent, max_var)
                })
            });
        if !justified {
            return Err(format!("line {}: clause {rest} is not justified", no + 1));
        }
        // store the clause after universal reduction, the same rule the
        // solver applies to every derived clause
        reduce(&mut lits);
        formula.push(lits);
    }
    Err("the proof does not derive the empty clause".to_string())
}
