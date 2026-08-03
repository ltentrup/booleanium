#![deny(unsafe_code)]
#![deny(unused_must_use)]
#![warn(clippy::all, clippy::pedantic)]
#![allow(clippy::missing_panics_doc, clippy::module_name_repetitions)]
//#![warn(clippy::cargo)]

use std::{
    fmt::Display,
    process::{ExitCode, Termination},
};

pub mod aiger;
pub mod alternation;
#[macro_use]
pub mod qcnf;
mod clause;
pub mod cli;
mod datastructure;
pub mod incdet;
pub mod incremental;
mod literal;
#[cfg(feature = "probe")]
pub mod probe;
pub mod qcir;
pub mod qdimacs;
pub mod qrat;
mod quantifier;
mod sat;
pub mod smtlib;

// Re-export
pub use quantifier::QuantTy;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SolverResult {
    Satisfiable = 10,
    Unsatisfiable = 20,
    Unknown = 30,
}

impl Display for SolverResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolverResult::Satisfiable => write!(f, "satisfiable"),
            SolverResult::Unsatisfiable => write!(f, "unsatisfiable"),
            SolverResult::Unknown => write!(f, "unknown"),
        }
    }
}

impl Termination for SolverResult {
    fn report(self) -> ExitCode {
        ExitCode::from(self as u8)
    }
}
