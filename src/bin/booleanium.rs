use booleanium::{
    aiger,
    incdet::{IncDet, Options},
    qdimacs::{ExtendedParseError, QdimacsParser},
    SolverResult,
};
use clap::Parser;
use miette::{IntoDiagnostic, Result};
use std::{io::Cursor, io::Read, path::PathBuf};

/// An experimental QBF solver based on incremental determinization.
#[derive(Debug, Parser)]
#[command(version, about)]
struct Args {
    /// Path to a QDIMACS or ASCII AIGER (QAIGER) file; reads from stdin
    /// if omitted.
    file: Option<PathBuf>,

    /// Disable eager propagation of constant Skolem functions.
    #[arg(long)]
    no_constant_propagation: bool,

    /// Rebuild a SAT solver per global conflict check instead of reusing an
    /// incremental solver.
    #[arg(long)]
    no_incremental_conflict_check: bool,

    /// Disable periodic deletion of long, unused learnt clauses.
    #[arg(long)]
    no_clause_deletion: bool,

    /// Disable CEGAR conflict resolution.
    #[arg(long)]
    no_cegar: bool,

    /// Disable case splitting on universal variables.
    #[arg(long)]
    no_case_splits: bool,

    /// Number of conflicts after which the search stalls into a case split.
    #[arg(long, default_value_t = 5000)]
    case_split_threshold: u32,

    /// Restart the search on a Luby schedule.
    #[arg(long)]
    restarts: bool,

    /// Verify the Skolem functions of a satisfiable result.
    #[arg(long)]
    certify: bool,
}

impl Args {
    fn options(&self) -> Options {
        Options {
            constant_propagation: !self.no_constant_propagation,
            incremental_conflict_check: !self.no_incremental_conflict_check,
            clause_deletion: !self.no_clause_deletion,
            cegar: !self.no_cegar,
            case_splits: !self.no_case_splits,
            case_split_threshold: self.case_split_threshold,
            restarts: self.restarts,
            ..Options::default()
        }
    }
}

fn main() -> Result<SolverResult> {
    tracing_subscriber::fmt::init();
    let args = Args::parse();

    let contents = match &args.file {
        Some(path) => std::fs::read(path).into_diagnostic()?,
        None => {
            tracing::info!("no file provided, reading from stdin");
            let mut buffer = Vec::new();
            std::io::stdin().read_to_end(&mut buffer).into_diagnostic()?;
            buffer
        }
    };
    let mut solver = IncDet::with_options(args.options());
    if contents.starts_with(b"aag ") {
        // ASCII AIGER circuit input (QAIGER convention)
        let text = std::str::from_utf8(&contents).into_diagnostic()?;
        let qcnf = aiger::parse_qaiger(text).into_diagnostic()?;
        solver = IncDet::from_qcnf_with_options(&qcnf, args.options());
    } else {
        let reader = Cursor::new(&contents);
        if let Err(err) = QdimacsParser::new(reader).parse_into(&mut solver) {
            Err(ExtendedParseError { source_code: contents, related: vec![err] })?;
        }
    }

    let result = solver.solve();
    println!("result status: {result}");
    if args.certify && result == SolverResult::Satisfiable {
        if solver.verify_skolem_functions() {
            println!("certificate: valid");
        } else {
            println!("certificate: INVALID");
            return Ok(SolverResult::Unknown);
        }
    }

    Ok(result)
}
