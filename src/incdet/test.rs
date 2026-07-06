use crate::{incdet::IncDet, SolverResult};

/// Differential testing of [`IncDet`] against brute-force QBF evaluation.
mod fuzz {
    use crate::{
        incdet::{IncDet, Options},
        qcnf::{strategy, QCNF},
        QuantTy,
    };
    use proptest::prelude::*;

    fn check(qcnf: &QCNF) -> Result<(), TestCaseError> {
        let expected = qcnf.brute_force();
        let mut solver = IncDet::from_qcnf(qcnf);
        let actual = solver.solve();
        prop_assert_eq!(actual, expected, "solver disagrees with oracle on instance:\n{}", qcnf);
        if actual == crate::SolverResult::Satisfiable {
            prop_assert!(
                solver.verify_skolem_functions(),
                "invalid Skolem functions for instance:\n{}",
                qcnf
            );
        }
        Ok(())
    }

    /// Checks the instance for every combination of solver options.
    fn check_all_options(qcnf: &QCNF) -> Result<(), TestCaseError> {
        let expected = qcnf.brute_force();
        for constant_propagation in [false, true] {
            for incremental_conflict_check in [false, true] {
                for flags in 0..16 {
                    let options = Options {
                        constant_propagation,
                        incremental_conflict_check,
                        clause_deletion: flags & 1 != 0,
                        restarts: flags & 2 != 0,
                        cegar: flags & 4 != 0,
                        case_splits: flags & 8 != 0,
                        // split almost immediately to exercise the machinery
                        case_split_threshold: 2,
                    };
                    let mut solver = IncDet::from_qcnf_with_options(qcnf, options);
                    let actual = solver.solve();
                    prop_assert_eq!(
                        actual,
                        expected,
                        "solver with {:?} disagrees with oracle on instance:\n{}",
                        options,
                        qcnf
                    );
                    if actual == crate::SolverResult::Satisfiable {
                        prop_assert!(
                            solver.verify_skolem_functions(),
                            "invalid Skolem functions with {:?} for instance:\n{}",
                            options,
                            qcnf
                        );
                    }
                }
            }
        }
        Ok(())
    }

    /// Flips every quantifier in the prefix, turning the generated ∀∃
    /// instances into ∃∀ instances.
    fn flip_quantifiers(mut qcnf: QCNF) -> QCNF {
        for (quant, _) in &mut qcnf.prefix {
            *quant = match quant {
                QuantTy::Exists => QuantTy::Forall,
                QuantTy::Forall => QuantTy::Exists,
            };
        }
        qcnf
    }

    proptest! {
        /// Random 2QBF instances (universal block followed by existential block).
        #[test]
        fn differential_2qbf(qcnf in strategy::qcnf(2..=2, 1..=5, 1..=14, 1..=5)) {
            check(&qcnf)?;
        }

        /// Random purely existential instances.
        #[test]
        fn differential_sat(qcnf in strategy::qcnf(1..=1, 1..=8, 1..=16, 1..=5)) {
            check(&qcnf)?;
        }

        /// Random 2QBF instances without unit clauses, so that solving relies
        /// on decisions and the watch machinery instead of unit propagation.
        #[test]
        fn differential_2qbf_wide(qcnf in strategy::qcnf(2..=2, 2..=8, 4..=24, 2..=6)) {
            check(&qcnf)?;
        }

        /// 3-CNF-like 2QBF instances close to the phase transition, to
        /// exercise multi-level backtracking and clause learning.
        #[test]
        fn differential_2qbf_dense(qcnf in strategy::qcnf(2..=2, 2..=8, 14..=22, 3..=4)) {
            check(&qcnf)?;
        }

        /// All solver option combinations on conflict-heavy instances.
        #[test]
        fn differential_options(qcnf in strategy::qcnf(2..=2, 2..=8, 14..=22, 3..=4)) {
            check_all_options(&qcnf)?;
        }

        /// ∃∀ instances, which universal reduction turns into SAT problems.
        #[test]
        fn differential_exists_forall(qcnf in strategy::qcnf(2..=2, 1..=5, 1..=14, 1..=5).prop_map(flip_quantifiers)) {
            check(&qcnf)?;
        }

        /// Purely existential instances with free variables (every third
        /// variable is removed from the prefix).
        #[test]
        fn differential_free_variables(qcnf in strategy::qcnf(1..=1, 1..=8, 1..=16, 1..=5).prop_map(drop_vars_from_prefix)) {
            check(&qcnf)?;
        }
    }

    /// Removes every third variable from the prefix, making it free.
    fn drop_vars_from_prefix(mut qcnf: QCNF) -> QCNF {
        let mut counter = 0;
        for (_, vars) in &mut qcnf.prefix {
            vars.retain(|_| {
                counter += 1;
                counter % 3 != 0
            });
        }
        qcnf
    }
}

/// Free variables are treated as outermost existential variables.
#[test]
fn free_variables() {
    use crate::qdimacs::QdimacsParser;
    use std::io::Cursor;

    // variables 2 and 3 are free, the formula is satisfiable
    let qdimacs = "p cnf 3 2\ne 1 0\n1 -2 0\n2 -3 0\n";
    let mut solver: IncDet = QdimacsParser::new(Cursor::new(qdimacs)).parse().unwrap();
    assert_eq!(solver.solve(), SolverResult::Satisfiable);

    // all variables free, unsatisfiable
    let qdimacs = "p cnf 1 2\n1 0\n-1 0\n";
    let mut solver: IncDet = QdimacsParser::new(Cursor::new(qdimacs)).parse().unwrap();
    assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
}

/// Variables that are declared in the header but occur neither in the
/// prefix nor in the matrix used to crash the solver.
#[test]
fn declared_but_unused_variables() {
    use crate::qdimacs::QdimacsParser;
    use std::io::Cursor;

    let qdimacs = "p cnf 5 2\na 1 0\ne 2 0\n1 -2 0\n-1 2 0\n";
    let mut solver: IncDet = QdimacsParser::new(Cursor::new(qdimacs)).parse().unwrap();
    assert_eq!(solver.solve(), SolverResult::Satisfiable);
}

#[test]
fn propagation_sat() {
    let qcnf = qcnf_formula![
        a 1;
        e 2;
        1 -2;
        -1 2;
    ];
    let mut solver = IncDet::from_qcnf(&qcnf);
    assert_eq!(solver.solve(), SolverResult::Satisfiable);
}

#[test]
fn propagation_unsat() {
    let qcnf = qcnf_formula![
        a 1;
        e 2;
        1 -2;
        -1 2;
        -1 -2;
    ];
    let mut solver = IncDet::from_qcnf(&qcnf);
    assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
}

/// Example from "Incremental Determinization" by Rabe & Seshia.
/// The formula is solved by propagation only.
#[test]
fn propagation_sat_incdet_paper() {
    let qcnf = qcnf_formula![
        a 1 2;
        e 3 4;
        // 3 <=> 1 & 2
        1 -3; 2 -3; -1 -2 3;
        // 4 <=> 1 | 3
        -1 -4; -3 -4; 1 3 4;
    ];
    let mut solver = IncDet::from_qcnf(&qcnf);
    assert_eq!(solver.solve(), SolverResult::Satisfiable);
}

#[test]
fn global_conflict_analysis() {
    let qcnf = qcnf_formula![
        a 1;
        e 2 3;
        2;
        2 -3;
        -2 3;
        2 3;
    ];
    let mut solver = IncDet::from_qcnf(&qcnf);
    assert_eq!(solver.solve(), SolverResult::Satisfiable);
}

#[test]
fn unsat_with_decsision() {
    let qcnf = qcnf_formula![
        a 1 2;
        e 3 4 5;
        2 -3;
        -1 -2 3;
        1 -4;
        -3 -4;
        1 3 4;
        -1 5;
        1 -5;
    ];
    let mut solver = IncDet::from_qcnf(&qcnf);
    assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
}

#[test]
fn unsat_1() {
    let qcnf = qcnf_formula![
        a 3;
        e 1 2 4 5;
        -5 -3;
        5 -1;
        1;
        4 2;
    ];
    let mut solver = IncDet::from_qcnf(&qcnf);
    assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
}

#[test]
fn unsat_2() {
    let qcnf = qcnf_formula![
        a 2 4;
        e 1 3 5;
        -5 2;
        -3 -1;
        3 1;
        1 -3 5;
        -1 -4;
    ];
    let mut solver = IncDet::from_qcnf(&qcnf);
    assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
}

#[test]
fn constant_propagation_unsat() {
    let qcnf = qcnf_formula![
        a 2;
        e 1;
        -1;
        1 -2;
    ];
    let mut solver = IncDet::from_qcnf(&qcnf);
    assert_eq!(solver.solve(), SolverResult::Unsatisfiable);
}

#[test]
#[ignore = "benchmark helper, run manually with --nocapture"]
fn bench_conflict_check_configs() {
    use crate::incdet::Options;
    use crate::qcnf::strategy;
    use proptest::{
        strategy::{Strategy, ValueTree},
        test_runner::TestRunner,
    };
    use std::time::{Duration, Instant};

    let mut runner = TestRunner::default();
    // larger instances than the differential tests, no oracle needed since
    // the two configurations are compared against each other
    let strat = strategy::qcnf(2..=2, 10..=14, 25..=45, 3..=4);
    let mut times = [Duration::ZERO; 2];
    let mut work = [0u64; 2];
    for i in 0..300 {
        let qcnf = strat.new_tree(&mut runner).unwrap().current();
        let mut results = Vec::new();
        for (idx, incremental_conflict_check) in [false, true].into_iter().enumerate() {
            let options = Options { incremental_conflict_check, ..Options::default() };
            let mut solver = IncDet::from_qcnf_with_options(&qcnf, options);
            let start = Instant::now();
            results.push(solver.solve());
            times[idx] += start.elapsed();
            work[idx] +=
                u64::from(solver.stats.global.conflicts) + u64::from(solver.stats.global.decisions);
        }
        assert_eq!(results[0], results[1], "configs disagree on instance {i}:\n{qcnf}");
    }
    eprintln!(
        "rebuilt solver: {:?} (work {}), incremental solver: {:?} (work {})",
        times[0], work[0], times[1], work[1]
    );
}

#[test]
#[ignore = "coverage measurement helper, run manually"]
fn fuzz_path_coverage() {
    use crate::qcnf::strategy;
    use proptest::{
        strategy::{Strategy, ValueTree},
        test_runner::TestRunner,
    };
    for (clauses, clause_len) in
        [(4..=24, 2..=6), (20..=45, 2..=3), (8..=20, 2..=3), (10..=16, 3..=3), (14..=22, 3..=4)]
    {
        let mut runner = TestRunner::default();
        let strat = strategy::qcnf(2..=2, 2..=8, clauses.clone(), clause_len.clone());
        let (mut decisions, mut conflicts, mut learnt, mut sat, mut unsat) =
            (0u64, 0u64, 0u64, 0u64, 0u64);
        for _ in 0..2000 {
            let qcnf = strat.new_tree(&mut runner).unwrap().current();
            let mut solver = IncDet::from_qcnf(&qcnf);
            match solver.solve() {
                SolverResult::Satisfiable => sat += 1,
                SolverResult::Unsatisfiable => unsat += 1,
                SolverResult::Unknown => {}
            }
            decisions += u64::from(solver.stats.global.decisions);
            conflicts += u64::from(solver.stats.global.conflicts);
            learnt += u64::from(solver.stats.global.added_clauses);
        }
        eprintln!("clauses={clauses:?} len={clause_len:?}: sat={sat} unsat={unsat} decisions={decisions} conflicts={conflicts} learnt={learnt}");
    }
    panic!("see stderr for results");
}
