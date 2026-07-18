//! Checks a QRAT refutation proof against a QDIMACS (or QAIGER)
//! instance with the in-tree checker: `qrat_check <instance> <proof>`.
//! Exits 0 on a valid proof, 1 otherwise.

use booleanium::{aiger, qcnf::QCNF, qdimacs::QdimacsParser, qrat};
use std::io::Cursor;

fn main() {
    tracing_subscriber::fmt::init();
    let mut args = std::env::args().skip(1);
    let (Some(instance), Some(proof)) = (args.next(), args.next()) else {
        eprintln!("usage: qrat_check <instance> <proof>");
        std::process::exit(2);
    };
    let contents = std::fs::read(instance).expect("instance file readable");
    let qcnf: QCNF = if contents.starts_with(b"aag ") {
        let text = std::str::from_utf8(&contents).expect("aag files are text");
        aiger::parse_qaiger(text).expect("instance parses")
    } else {
        let mut qcnf = QCNF::default();
        QdimacsParser::new(Cursor::new(&contents)).parse_into(&mut qcnf).expect("instance parses");
        qcnf
    };
    let proof = std::fs::read_to_string(proof).expect("proof file readable");
    match qrat::check_refutation(&qcnf, &proof) {
        Ok(()) => println!("proof: valid"),
        Err(err) => {
            println!("proof: INVALID ({err})");
            std::process::exit(1);
        }
    }
}
