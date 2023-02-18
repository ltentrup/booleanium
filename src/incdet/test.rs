use crate::{incdet::IncDet, SolverResult};

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
