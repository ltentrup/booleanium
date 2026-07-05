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
        Ok(())
    }

    /// Checks the instance for every combination of solver options.
    fn check_all_options(qcnf: &QCNF) -> Result<(), TestCaseError> {
        let expected = qcnf.brute_force();
        for constant_propagation in [false, true] {
            for incremental_conflict_check in [false, true] {
                let options = Options { constant_propagation, incremental_conflict_check };
                let mut solver = IncDet::from_qcnf_with_options(qcnf, options);
                let actual = solver.solve();
                prop_assert_eq!(
                    actual,
                    expected,
                    "solver with {:?} disagrees with oracle on instance:\n{}",
                    options,
                    qcnf
                );
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
    }
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
            let options = Options { constant_propagation: true, incremental_conflict_check };
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
