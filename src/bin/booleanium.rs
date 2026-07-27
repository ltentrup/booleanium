use booleanium::{
    aiger,
    incdet::{IncDet, Options},
    qcir,
    qdimacs::{ExtendedParseError, QdimacsParser},
    smtlib, QuantTy, SolverResult,
};
use clap::Parser;
use miette::{IntoDiagnostic, Result};
use std::{io::Cursor, io::Read, path::PathBuf};

/// An experimental QBF solver based on incremental determinization.
#[derive(Debug, Parser)]
#[command(version, about)]
struct Args {
    /// Path to a QDIMACS, ASCII AIGER (QAIGER), QCIR, or SMT-LIB file
    /// (auto-detected); reads from stdin if omitted.
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

    /// Write the Skolem functions of a satisfiable result as a strategy
    /// circuit (ASCII AIGER, universal inputs to existential outputs) to
    /// this path.
    #[arg(long, value_name = "PATH")]
    strategy: Option<PathBuf>,

    /// Log a QRAT refutation proof and write it to this path on an
    /// unsatisfiable result (disables CEGAR and case splits, whose
    /// derivations the clausal proof rules cannot express).
    #[arg(long, value_name = "PATH")]
    proof: Option<PathBuf>,

    /// Solve prefixes beyond two blocks without ∀-expansion, i.e. purely
    /// by the CEGAR loops. The two dispatch paths share almost nothing
    /// but the 2QBF oracle, so running both is a differential check on
    /// real instances.
    #[arg(long)]
    no_expansion: bool,
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
            proof: self.proof.is_some(),
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
    let first = contents.iter().find(|c| !c.is_ascii_whitespace()).copied();
    if first == Some(b'(') || first == Some(b';') {
        // SMT-LIB script input
        let text = std::str::from_utf8(&contents).into_diagnostic()?;
        let mut frontend = smtlib::Frontend::new(args.options());
        print!("{}", frontend.run(text));
        return Ok(frontend.last_result().unwrap_or(SolverResult::Unknown));
    }
    if contents.starts_with(b"#QCIR") {
        // prenex QCIR circuit input; an exists-forall prefix is solved
        // by negation with the verdict inverted
        let text = std::str::from_utf8(&contents).into_diagnostic()?;
        let parsed = qcir::parse_qcir(text).into_diagnostic()?;
        let mut solver = IncDet::from_qcnf_with_options(&parsed.qcnf, args.options());
        let mut result = solver.solve();
        if parsed.negated {
            result = match result {
                SolverResult::Satisfiable => SolverResult::Unsatisfiable,
                SolverResult::Unsatisfiable => SolverResult::Satisfiable,
                SolverResult::Unknown => SolverResult::Unknown,
            };
            if args.certify || args.strategy.is_some() || args.proof.is_some() {
                tracing::warn!(
                    "certificates, strategies, and proofs describe the negated instance                      and are not emitted for exists-forall QCIR inputs"
                );
            }
            println!("result status: {result}");
            return Ok(result);
        }
        println!("result status: {result}");
        if args.certify && result == SolverResult::Satisfiable {
            if solver.verify_skolem_functions() {
                println!("certificate: valid");
            } else {
                println!("certificate: INVALID");
                return Ok(SolverResult::Unknown);
            }
        }
        if let Some(path) = &args.proof {
            if result == SolverResult::Unsatisfiable {
                match solver.qrat_proof() {
                    Some(proof) => {
                        std::fs::write(path, proof).into_diagnostic()?;
                        println!("proof written to {}", path.display());
                    }
                    None => println!("proof: NOT AVAILABLE (run left the proof rules)"),
                }
            }
        }
        if let Some(path) = &args.strategy {
            if result == SolverResult::Satisfiable {
                let circuit = solver.skolem_model().to_aiger(&|v| parsed.name_of(v));
                std::fs::write(path, circuit).into_diagnostic()?;
                println!("strategy written to {}", path.display());
            }
        }
        return Ok(result);
    }
    let mut solver;
    if contents.starts_with(b"aag ") {
        // ASCII AIGER circuit input (QAIGER convention)
        let text = std::str::from_utf8(&contents).into_diagnostic()?;
        let qcnf = aiger::parse_qaiger(text).into_diagnostic()?;
        solver = IncDet::from_qcnf_with_options(&qcnf, args.options());
    } else {
        let mut qcnf = booleanium::qcnf::QCNF::default();
        let reader = Cursor::new(&contents);
        if let Err(err) = QdimacsParser::new(reader).parse_into(&mut qcnf) {
            Err(ExtendedParseError { source_code: contents, related: vec![err] })?;
        }
        let blocks = qcnf.prefix.iter().filter(|(_, vars)| !vars.is_empty()).count();
        if blocks > 2 {
            // alternations beyond 2QBF: recursive expansion over the
            // 2QBF core, with a composed strategy where the pipeline can
            // build one (no refutation proofs yet)
            if args.proof.is_some() {
                tracing::warn!("proofs are not available beyond 2QBF");
            }
            let budget =
                if args.no_expansion { 0 } else { booleanium::alternation::EXPANSION_BUDGET };
            let (result, strategy) =
                booleanium::alternation::solve_certified(&qcnf, args.options(), budget);
            #[cfg(feature = "probe")]
            {
                use std::sync::atomic::Ordering::Relaxed;
                eprintln!(
                    "leaf solves: {} over {} vars / {} clauses",
                    booleanium::alternation::LEAF_CALLS.load(Relaxed),
                    booleanium::alternation::LEAF_VARS.load(Relaxed),
                    booleanium::alternation::LEAF_CLAUSES.load(Relaxed),
                );
            }
            println!("result status: {result}");
            if args.certify || args.strategy.is_some() {
                let Some(strategy) = &strategy else {
                    if result == SolverResult::Satisfiable {
                        // the pipeline took a route it cannot invert
                        // (∀-expansion); the verdict still stands
                        println!("strategy: NOT AVAILABLE");
                    } else {
                        tracing::warn!("no strategy: the result is not satisfiable");
                    }
                    return Ok(result);
                };
                if args.certify {
                    if booleanium::alternation::verify_strategy(&qcnf, strategy) {
                        println!("certificate: valid");
                    } else {
                        println!("certificate: INVALID");
                        return Ok(SolverResult::Unknown);
                    }
                }
                if let Some(path) = &args.strategy {
                    let universals: Vec<_> = qcnf
                        .prefix
                        .iter()
                        .filter(|(q, _)| *q == QuantTy::Forall)
                        .flat_map(|(_, vars)| vars.iter().copied())
                        .collect();
                    std::fs::write(path, strategy.to_aiger(&universals, &|_| None))
                        .into_diagnostic()?;
                    println!("strategy written to {}", path.display());
                }
            }
            return Ok(result);
        }
        solver = IncDet::from_qcnf_with_options(&qcnf, args.options());
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
    if let Some(path) = &args.proof {
        if result == SolverResult::Unsatisfiable {
            match solver.qrat_proof() {
                Some(proof) => {
                    std::fs::write(path, proof).into_diagnostic()?;
                    println!("proof written to {}", path.display());
                }
                None => println!("proof: NOT AVAILABLE (run left the proof rules)"),
            }
        } else {
            tracing::warn!("no proof to write: the result is not unsatisfiable");
        }
    }
    if let Some(path) = &args.strategy {
        if result == SolverResult::Satisfiable {
            let circuit = solver.skolem_model().to_aiger(&|_| None);
            std::fs::write(path, circuit).into_diagnostic()?;
            println!("strategy written to {}", path.display());
        } else {
            tracing::warn!("no strategy to write: the result is not satisfiable");
        }
    }

    Ok(result)
}
