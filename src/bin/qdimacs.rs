use miette::Result;
use booleanium::{
    qcnf::QCNF,
    qdimacs::{ExtendedParseError, QdimacsParser},
};
use std::io::Cursor;

fn main() -> Result<()> {
    use booleanium::cli;

    tracing_subscriber::fmt::init();

    let contents = cli::content_from_args()?;
    let reader = Cursor::new(&contents);

    let qcnf: QCNF = match QdimacsParser::new(reader).parse() {
        Ok(q) => q,
        Err(err) => Err(ExtendedParseError { source_code: contents, related: vec![err] })?,
    };

    print!("{}", qcnf);
    Ok(())
}
