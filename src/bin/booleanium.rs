use booleanium::{
    cli,
    incdet::IncDet,
    qdimacs::{ExtendedParseError, QdimacsParser},
    SolverResult,
};
use miette::Result;
use std::io::Cursor;

fn main() -> Result<SolverResult> {
    tracing_subscriber::fmt::init();

    let contents = cli::content_from_args()?;
    let reader = Cursor::new(&contents);

    let mut solver: IncDet = match QdimacsParser::new(reader).parse() {
        Ok(q) => q,
        Err(err) => Err(ExtendedParseError { source_code: contents, related: vec![err] })?,
    };

    let result = solver.solve();
    println!("result status: {}", result);

    Ok(result)
}
