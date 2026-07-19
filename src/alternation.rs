//! Quantifier alternations beyond 2QBF: recursive expansion with the
//! incremental 2QBF core as a persistent oracle (see `RESEARCH.md`,
//! RQ6).
//!
//! The outermost existential block `X` is solved by CEGAR over a plain
//! SAT *abstraction*: candidates `X*` are proposed, the remainder of the
//! prefix is solved under the assumptions `X*`, and inner refutations
//! refine the abstraction. When the remainder is exactly ∀Y∃Z, the
//! oracle is one persistent [`IncrementalSolver`] — `Y` universal,
//! `Z ∪ X` existential, one `solve_with_assumptions(X*)` per candidate,
//! with everything learnt carrying across candidates — and an inner
//! refutation returns a *verified* universal witness `Y*`, so the
//! refinement is the classic expansion `matrix[Y := Y*]` over fresh
//! `Z`-copies — the blocking clause `¬X*` is added alongside (sound,
//! since the oracle refuted the candidate; it guarantees progress even
//! when `Y*` is only the unverified recorded candidate). Without any
//! witness (deep recursion) the blocking clause alone keeps the loop
//! total. A ∀-outermost prefix runs the dual candidate loop — search
//! for a refuting outer assignment, block answered candidates — which
//! keeps the matrix fixed instead of cascading negation gates through
//! the recursion.

use crate::{
    incdet::{IncDet, Options},
    incremental::IncrementalSolver,
    literal::{Lit, Var},
    qcnf::QCNF,
    QuantTy, SolverResult,
};
use std::collections::{HashMap, HashSet};

/// Solves a prenex QBF with any number of quantifier blocks.
#[must_use]
pub fn solve(qcnf: &QCNF, options: Options) -> SolverResult {
    let qcnf = normalized(qcnf);
    solve_normalized(&qcnf, options)
}

fn solve_normalized(qcnf: &QCNF, options: Options) -> SolverResult {
    if qcnf.prefix.len() <= 2 {
        let mut solver = IncDet::from_qcnf_with_options(qcnf, options);
        return solver.solve();
    }
    match qcnf.prefix[0].0 {
        QuantTy::Exists => expansion_loop(qcnf, options),
        QuantTy::Forall => forall_loop(qcnf, options),
    }
}

/// The dual candidate loop at a ∀-outermost block: search for a
/// refuting outer assignment; every answered candidate is blocked.
/// (Negating the matrix instead would cascade Tseitin gates through the
/// recursion and blow up; the dual loop keeps the matrix fixed. Strong
/// dual refinements would need regions of answered candidates — future
/// work, the weak blocking clause keeps the loop total.)
fn forall_loop(qcnf: &QCNF, options: Options) -> SolverResult {
    use crate::sat::{varisat::Varisat, LookupSolver, SatSolver};

    let outer: Vec<Var> = qcnf.prefix[0].1.clone();
    let mut alpha = LookupSolver::<Varisat>::default();
    alpha.set_var_count(
        outer.iter().map(|v| usize::try_from(v.to_dimacs()).expect("fits")).max().unwrap_or(0) + 1,
    );
    // force the solver to materialize every outer variable so models
    // cover them
    for &v in &outer {
        let l = alpha.lookup(Lit::positive(v));
        alpha.add_clause(&[l, !l]);
    }
    let mut rounds = 0u32;
    loop {
        rounds += 1;
        if rounds > 4096 {
            tracing::warn!("universal candidate budget exhausted");
            return SolverResult::Unknown;
        }
        if !alpha.solve().unwrap() {
            // every universal choice is answered
            return SolverResult::Satisfiable;
        }
        let model: HashMap<Var, bool> = alpha
            .orig_model()
            .expect("model after sat")
            .into_iter()
            .map(|l| (l.var(), l.is_positive()))
            .collect();
        let candidate: Vec<Lit> = outer
            .iter()
            .map(|&v| {
                if model.get(&v).copied().unwrap_or(false) {
                    Lit::positive(v)
                } else {
                    Lit::negative(v)
                }
            })
            .collect();
        let restricted = normalized(&restrict(qcnf, &candidate, 1));
        match solve_normalized(&restricted, options) {
            // the candidate is a winning universal prefix move
            SolverResult::Unsatisfiable => return SolverResult::Unsatisfiable,
            SolverResult::Unknown => return SolverResult::Unknown,
            SolverResult::Satisfiable => {
                let blocking: Vec<_> = candidate.iter().map(|&l| alpha.lookup(!l)).collect();
                alpha.add_clause(&blocking);
            }
        }
    }
}

/// Drops empty blocks, merges adjacent blocks of the same quantifier,
/// and binds free variables to an outermost existential block.
fn normalized(qcnf: &QCNF) -> QCNF {
    let mut prefix: Vec<(QuantTy, Vec<Var>)> = Vec::new();
    let declared: HashSet<Var> =
        qcnf.prefix.iter().flat_map(|(_, vars)| vars.iter().copied()).collect();
    let mut free: Vec<Var> = qcnf
        .matrix
        .iter()
        .flatten()
        .map(|l| l.var())
        .filter(|v| !declared.contains(v))
        .collect::<HashSet<_>>()
        .into_iter()
        .collect();
    free.sort_unstable_by_key(|v| v.to_dimacs());
    if !free.is_empty() {
        prefix.push((QuantTy::Exists, free));
    }
    for (quant, vars) in &qcnf.prefix {
        if vars.is_empty() {
            continue;
        }
        match prefix.last_mut() {
            Some((q, block)) if q == quant => block.extend(vars.iter().copied()),
            _ => prefix.push((*quant, vars.clone())),
        }
    }
    QCNF { prefix, matrix: qcnf.matrix.clone() }
}

/// CEGAR at the outermost existential block of a normalized prefix with
/// at least three blocks.
// the loop reads best as one piece: oracle setup, candidates, refinements
#[allow(clippy::too_many_lines)]
fn expansion_loop(qcnf: &QCNF, options: Options) -> SolverResult {
    use crate::sat::{varisat::Varisat, LookupSolver, SatSolver};

    let outer: Vec<Var> = qcnf.prefix[0].1.clone();
    let outer_set: HashSet<Var> = outer.iter().copied().collect();
    let rest = &qcnf.prefix[1..];

    // the persistent 2QBF oracle for a three-block prefix ∃X ∀Y ∃Z:
    // Y universal, Z and X existential, X assumed per candidate
    let oracle = if rest.len() == 2 {
        let mut solver = IncrementalSolver::new(options);
        for v in &rest[0].1 {
            solver.declare_universal(u32::try_from(v.to_dimacs()).expect("fits"));
        }
        for v in outer.iter().chain(&rest[1].1) {
            solver.declare_existential(u32::try_from(v.to_dimacs()).expect("fits"));
        }
        for clause in &qcnf.matrix {
            let lits: Vec<i32> = clause.iter().map(|l| l.to_dimacs()).collect();
            solver.add_clause(&lits);
        }
        Some(solver)
    } else {
        None
    };
    let mut oracle = oracle;

    // the abstraction over X: seeded with the clauses that mention only
    // outer variables (they must hold under any strategy). Every
    // refinement introduces fresh copy variables, so the lookup table
    // grows by one round's worth of variables up front each iteration.
    let mut alpha = LookupSolver::<Varisat>::default();
    let total_vars = usize::try_from(
        qcnf.prefix
            .iter()
            .flat_map(|(_, vars)| vars.iter())
            .map(|v| v.to_dimacs())
            .max()
            .unwrap_or(0),
    )
    .expect("fits");
    let mut next_copy_var = i32::try_from(total_vars).expect("fits") + 1;
    alpha.set_var_count(total_vars + 2);
    for clause in &qcnf.matrix {
        if clause.iter().all(|l| outer_set.contains(&l.var())) {
            let lits: Vec<_> = clause.iter().map(|&l| alpha.lookup(l)).collect();
            alpha.add_clause(&lits);
        }
    }

    // expansion can blow up on hard instances (the known weakness of
    // the algorithm family); give up honestly instead of exhausting
    // memory
    let mut rounds = 0u32;
    let mut added_literals = 0usize;
    loop {
        rounds += 1;
        if rounds > 4096 || added_literals > 8_000_000 {
            tracing::warn!("expansion budget exhausted after {rounds} refinements");
            return SolverResult::Unknown;
        }
        if !alpha.solve().unwrap() {
            return SolverResult::Unsatisfiable;
        }
        let model: HashMap<Var, bool> = alpha
            .orig_model()
            .expect("model after sat")
            .into_iter()
            .map(|l| (l.var(), l.is_positive()))
            .collect();
        let candidate: Vec<Lit> = outer
            .iter()
            .map(|&v| {
                if model.get(&v).copied().unwrap_or(false) {
                    Lit::positive(v)
                } else {
                    Lit::negative(v)
                }
            })
            .collect();

        // ask the remainder under the candidate
        // room for one refinement round of fresh copies
        alpha.set_var_count(usize::try_from(next_copy_var).expect("fits") + total_vars + 2);

        let (verdict, witness) = match &mut oracle {
            Some(solver) => {
                let assumptions: Vec<i32> = candidate.iter().map(|l| l.to_dimacs()).collect();
                let verdict = solver.solve_with_assumptions(&assumptions);
                // any universal assignment is a sound expansion point (a
                // winning outer choice must answer it), so the unverified
                // candidate serves; the blocking clause below guarantees
                // progress either way
                let witness = solver
                    .universal_witness_candidate()
                    .map(|w| w.into_iter().map(Lit::from_dimacs).collect::<Vec<_>>());
                (verdict, witness)
            }
            None => {
                let restricted = restrict(qcnf, &candidate, 1);
                (solve_normalized(&normalized(&restricted), options), None)
            }
        };
        match verdict {
            SolverResult::Satisfiable => return SolverResult::Satisfiable,
            SolverResult::Unknown => return SolverResult::Unknown,
            SolverResult::Unsatisfiable => {}
        }

        // the oracle refuted this candidate: excluding it is always
        // sound and guarantees progress
        let blocking: Vec<_> = candidate.iter().map(|&l| alpha.lookup(!l)).collect();
        alpha.add_clause(&blocking);

        if let Some(universal) = witness {
            {
                // strong refinement: the expansion matrix[Y := Y*] over a
                // fresh copy of every non-outer variable; verified
                // witnesses guarantee the candidate is excluded
                let assigned: HashSet<Lit> = universal.iter().copied().collect();
                let mut rename: HashMap<Var, i32> = HashMap::new();
                let mut empty_added = false;
                for clause in &qcnf.matrix {
                    if clause.iter().any(|l| assigned.contains(l)) {
                        continue;
                    }
                    let mut lits: Vec<_> = Vec::new();
                    for &l in clause {
                        if assigned.contains(&!l) {
                            continue;
                        }
                        let mapped = if outer_set.contains(&l.var()) {
                            l
                        } else {
                            let raw = *rename.entry(l.var()).or_insert_with(|| {
                                let fresh = next_copy_var;
                                next_copy_var += 1;
                                fresh
                            });
                            let lit = Lit::from_dimacs(raw);
                            if l.is_positive() {
                                lit
                            } else {
                                !lit
                            }
                        };
                        lits.push(alpha.lookup(mapped));
                    }
                    if lits.is_empty() {
                        empty_added = true;
                    }
                    added_literals += lits.len() + 1;
                    alpha.add_clause(&lits);
                }
                if empty_added {
                    // some clause is falsified by the witness alone: no
                    // outer choice can answer it
                    return SolverResult::Unsatisfiable;
                }
            }
        }
    }
}

/// The instance restricted by the given outer-block assignment: satisfied
/// clauses dropped, falsified literals deleted, the first `blocks` prefix
/// blocks removed.
fn restrict(qcnf: &QCNF, assignment: &[Lit], blocks: usize) -> QCNF {
    let assigned: HashSet<Lit> = assignment.iter().copied().collect();
    let matrix: Vec<Vec<Lit>> = qcnf
        .matrix
        .iter()
        .filter(|clause| !clause.iter().any(|l| assigned.contains(l)))
        .map(|clause| clause.iter().copied().filter(|l| !assigned.contains(&!*l)).collect())
        .collect();
    QCNF { prefix: qcnf.prefix[blocks..].to_vec(), matrix }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::qcnf::strategy;
    use proptest::prelude::*;

    fn check(qcnf: &QCNF) -> Result<(), TestCaseError> {
        let expected = qcnf.brute_force();
        let actual = solve(qcnf, Options::default());
        prop_assert_eq!(actual, expected, "alternation solver disagrees on:\n{}", qcnf);
        Ok(())
    }

    #[test]
    fn three_block_basics() {
        // ∃x ∀y ∃z: z ↔ (x xor y) and z must equal x — forces x-choice
        // to survive both y values; unsatisfiable
        let qcnf = QCNF::new(
            &[
                (QuantTy::Exists, &[1][..]),
                (QuantTy::Forall, &[2][..]),
                (QuantTy::Exists, &[3][..]),
            ],
            &[
                &[-3, 1, 2][..],
                &[-3, -1, -2][..],
                &[3, -1, 2][..],
                &[3, 1, -2][..],
                &[-3, 1][..],
                &[3, -1][..],
            ],
        );
        assert_eq!(solve(&qcnf, Options::default()), qcnf.brute_force());
        // ∃x ∀y ∃z: z ↔ (x xor y) — satisfiable for any x
        let qcnf = QCNF::new(
            &[
                (QuantTy::Exists, &[1][..]),
                (QuantTy::Forall, &[2][..]),
                (QuantTy::Exists, &[3][..]),
            ],
            &[&[-3, 1, 2][..], &[-3, -1, -2][..], &[3, -1, 2][..], &[3, 1, -2][..]],
        );
        assert_eq!(solve(&qcnf, Options::default()), SolverResult::Satisfiable);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]
        /// Random instances with one to four quantifier blocks against
        /// the brute-force oracle.
        #[test]
        fn differential_alternations(qcnf in strategy::qcnf(1..=6, 1..=3, 1..=14, 1..=4)) {
            check(&qcnf)?;
        }

        /// Denser three-block instances (the persistent-oracle path).
        #[test]
        fn differential_three_blocks(qcnf in strategy::qcnf(3..=3, 1..=4, 4..=16, 2..=4)) {
            check(&qcnf)?;
        }
    }
}
