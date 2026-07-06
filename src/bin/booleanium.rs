use booleanium::{
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
    /// Path to a QDIMACS file; reads from stdin if omitted.
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
            restarts: self.restarts,
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
    let reader = Cursor::new(&contents);

    let mut solver = IncDet::with_options(args.options());
    if let Err(err) = QdimacsParser::new(reader).parse_into(&mut solver) {
        Err(ExtendedParseError { source_code: contents, related: vec![err] })?;
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
