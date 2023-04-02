//! Parser for the QDIMACS input file format.
//! The format specification is provided at <https://www.qbflib.org/qdimacs.html>.

use crate::{
    literal::{Lit, Var},
    QuantTy,
};
use miette::{Diagnostic, SourceSpan};
use std::{
    io::{Bytes, Read},
    iter::Peekable,
};
use thiserror::Error;

#[derive(Debug, Error, Diagnostic)]
#[error("Cannot parse QDIMACS")]
#[diagnostic()]
pub struct ExtendedParseError {
    #[source_code]
    pub source_code: Vec<u8>,

    #[related]
    pub related: Vec<ParseError>,
}

#[derive(Debug, Error, Diagnostic)]
pub enum ParseError {
    #[error("The underlying IO has failed")]
    IO(#[from] std::io::Error),

    #[error("Invalid header: {}", reason)]
    #[diagnostic()]
    InvalidHeader {
        reason: HeaderError,

        #[label]
        err_span: SourceSpan,
    },

    #[error("Missing QDMIACS header, i.e., `p cnf ...`")]
    MissingHeader,

    #[error("Unexpected end of file")]
    UnexpectedEndOfFile {
        #[label]
        err_span: SourceSpan,
    },

    #[error("Unexpected character")]
    #[diagnostic()]
    UnexpectedChar {
        #[label]
        err_span: SourceSpan,
    },

    #[error("Invalid integer")]
    InvalidInt {
        #[label]
        err_span: SourceSpan,
    },

    #[error("Variable {val} is out of bound")]
    VariableOutOfBound {
        val: i64,

        #[label]
        err_span: SourceSpan,
    },

    #[error("Literal {val} is out of bound")]
    LiteralOutOfBound {
        val: i64,

        #[label]
        err_span: SourceSpan,
    },

    #[error(
        "Number of clauses does not match header: expected {}, but found {} clauses",
        expected,
        found
    )]
    NumClausesMismatch { expected: u32, found: u32 },
}

#[derive(Debug, Error, Diagnostic)]
pub enum HeaderError {
    #[error("`p cnf` prefix missing or invalid")]
    InvalidPrefix,

    #[error("Invalid variable count")]
    InvalidVariableCount,

    #[error("Invalid clause count")]
    InvalidClauseCount,
}

/// An instance of an implementor can be derived from a textual representation
/// of a QBF in the QDIMACS format.
pub trait FromQdimacs: Default {
    fn set_num_variables(&mut self, variables: u32);
    fn set_num_clauses(&mut self, clauses: u32);
    fn quantify(&mut self, quant: QuantTy, vars: &[Var]);
    fn add_clause(&mut self, lits: &[Lit]);
}

#[derive(Debug)]
pub struct QdimacsParser<R: Read> {
    bytes: Peekable<Bytes<R>>,
    num_clauses: u32,
    num_clauses_read: u32,

    offset: usize,
}

impl<R: Read> QdimacsParser<R> {
    pub fn new(reader: R) -> Self {
        Self { bytes: reader.bytes().peekable(), offset: 0, num_clauses: 0, num_clauses_read: 0 }
    }

    /// Parses a QDIMACS file and returns the representation `Q`.
    ///
    /// # Errors
    ///
    /// This function will return an error if the read content is not valid QDIMACS.
    /// The function propagates underlying IO failures.
    pub fn parse<Q: FromQdimacs>(&mut self) -> Result<Q, ParseError> {
        let mut result = Q::default();
        self.parse_comment_or_header(&mut result)?;
        self.parse_prefix(&mut result)?;
        self.parse_matrix(&mut result)?;

        // check that number of clauses match the header
        if self.num_clauses_read != self.num_clauses {
            return Err(ParseError::NumClausesMismatch {
                expected: self.num_clauses,
                found: self.num_clauses_read,
            });
        }

        Ok(result)
    }

    /// Either `c ...` or `p cnf ...`
    fn parse_comment_or_header<Q: FromQdimacs>(
        &mut self,
        result: &mut Q,
    ) -> Result<(), ParseError> {
        while let Some(b) = self.next_byte()? {
            match b {
                b'c' => {
                    // start of a comment line, ignore remaining line
                    self.skip_until(b'\n')?;
                }
                b'p' => {
                    // `p cnf [NUM_VARIABLES] [NUM_CLAUSES]` header
                    self.expect(&b" cnf"[..]).map_err(|_| ParseError::InvalidHeader {
                        reason: HeaderError::InvalidPrefix,
                        err_span: self.err_span(),
                    })?;

                    // parse variable count
                    self.skip_whitespace_and_peek()?.ok_or_else(|| {
                        ParseError::UnexpectedEndOfFile { err_span: self.err_span() }
                    })?;
                    let num_variables: u32 =
                        self.parse_int().map_err(|err| ParseError::InvalidHeader {
                            reason: HeaderError::InvalidVariableCount,
                            err_span: err.err_span().unwrap_or_else(|| self.err_span()),
                        })?;

                    // parse clause count
                    self.skip_whitespace_and_peek()?.ok_or_else(|| {
                        ParseError::UnexpectedEndOfFile { err_span: self.err_span() }
                    })?;
                    let num_clauses: u32 =
                        self.parse_int().map_err(|err| ParseError::InvalidHeader {
                            reason: HeaderError::InvalidClauseCount,
                            err_span: err.err_span().unwrap_or_else(|| self.err_span()),
                        })?;

                    self.num_clauses = num_clauses;
                    result.set_num_variables(num_variables);
                    result.set_num_clauses(num_clauses);
                    return Ok(());
                }
                b if b.is_ascii_whitespace() => {
                    // ignore whitespace at the beginning of the file
                }
                _ => return Err(ParseError::UnexpectedChar { err_span: self.err_offset().into() }),
            }
        }
        Err(ParseError::MissingHeader)
    }

    /// Either `e ...` or `a ...`, stops before matrix begins.
    fn parse_prefix<Q: FromQdimacs>(&mut self, result: &mut Q) -> Result<(), ParseError> {
        while let Some(b) = self.skip_whitespace_and_peek()? {
            match b {
                b'a' | b'e' => {
                    self.parse_prefix_line(result)?;
                }
                b'-' | (b'0'..=b'9') => {
                    // end of quantifier prefix
                    return Ok(());
                }
                _ => return Err(ParseError::UnexpectedChar { err_span: self.err_offset().into() }),
            }
        }
        Ok(())
    }

    /// Either `e ...` or `a ...`
    fn parse_prefix_line<Q: FromQdimacs>(&mut self, result: &mut Q) -> Result<(), ParseError> {
        let quant = match self
            .next_byte()?
            .ok_or_else(|| ParseError::UnexpectedEndOfFile { err_span: self.err_span() })?
        {
            b'e' => QuantTy::Exists,
            b'a' => QuantTy::Forall,
            _ => unreachable!(),
        };
        let mut vars = Vec::new();
        loop {
            self.skip_whitespace_and_peek()?
                .ok_or_else(|| ParseError::UnexpectedEndOfFile { err_span: self.err_span() })?;
            let start_offset = self.err_offset();
            let var: i32 = self.parse_int()?;
            if var == 0 {
                break;
            }
            if !(1..=Var::MAX_VAR.to_dimacs()).contains(&var) {
                return Err(ParseError::VariableOutOfBound {
                    val: var.into(),
                    // reduce end offset by one, as last byte was a whitespace
                    err_span: (start_offset..self.err_offset().saturating_sub(1)).into(),
                });
            }
            vars.push(Var::from_dimacs(var));
        }
        result.quantify(quant, &vars);
        Ok(())
    }

    /// Parses clauses until EOF
    fn parse_matrix<Q: FromQdimacs>(&mut self, result: &mut Q) -> Result<(), ParseError> {
        let mut clause = Vec::new();
        while (self.skip_whitespace_and_peek()?).is_some() {
            clause.clear();
            loop {
                self.skip_whitespace_and_peek()?
                    .ok_or_else(|| ParseError::UnexpectedEndOfFile { err_span: self.err_span() })?;
                let start_offset = self.err_offset();
                let lit: i32 = self.parse_int()?;
                if lit == 0 {
                    break;
                }
                if !(Lit::MIN_LIT.to_dimacs()..=Lit::MAX_LIT.to_dimacs()).contains(&lit) {
                    return Err(ParseError::LiteralOutOfBound {
                        val: lit.into(),
                        err_span: (start_offset..self.err_offset()).into(),
                    });
                }
                clause.push(Lit::from_dimacs(lit));
            }
            result.add_clause(&clause);
            self.num_clauses_read += 1;
        }
        Ok(())
    }

    /// Consumes the next byte in the input.
    /// Returns the byte or `None` in the case of EOF.
    fn next_byte(&mut self) -> Result<Option<u8>, ParseError> {
        let byte = self.bytes.next().transpose()?;
        if byte.is_some() {
            self.offset += 1;
        }
        Ok(byte)
    }

    /// Returns the next byte value without consuming.
    fn peek_byte(&mut self) -> Option<u8> {
        match self.bytes.peek() {
            Some(Ok(b)) => Some(*b),
            _ => None,
        }
    }

    fn skip_until(&mut self, until: u8) -> Result<(), ParseError> {
        while self
            .next_byte()?
            .ok_or_else(|| ParseError::UnexpectedEndOfFile { err_span: self.err_span() })?
            != until
        {}
        Ok(())
    }

    /// Skips input bytes until a non-ASCII whitespace character is found.
    /// Returns the first non-ASCII whitespace character (if not EOF).
    fn skip_whitespace_and_peek(&mut self) -> Result<Option<u8>, ParseError> {
        while let Some(b) = self.peek_byte() {
            if !b.is_ascii_whitespace() {
                return Ok(Some(b));
            }
            self.next_byte()?;
        }
        Ok(None)
    }

    fn expect(&mut self, value: &[u8]) -> Result<(), ParseError> {
        for (&expected, found) in value.iter().zip(&mut self.bytes) {
            let found = found?;
            self.offset += 1;
            if found != expected {
                return Err(ParseError::UnexpectedChar { err_span: self.err_offset().into() });
            }
        }
        Ok(())
    }

    fn parse_int<I>(&mut self) -> Result<I, ParseError>
    where
        I: TryFrom<i64>,
    {
        let start_span = self.err_offset();
        let mut parsed: i64 = 0;
        let mut is_negated = false;
        while let Some(b) = self.next_byte()? {
            match b {
                b'-' => {
                    if is_negated {
                        return Err(ParseError::InvalidInt { err_span: self.err_span() });
                    }
                    is_negated = true;
                }
                b @ b'0'..=b'9' => {
                    let val = i64::from(b - b'0');
                    parsed = if let Some(parsed) =
                        parsed.checked_mul(10).and_then(|res| res.checked_add(val))
                    {
                        parsed
                    } else {
                        // overflow while parsing integer
                        return Err(ParseError::InvalidInt {
                            err_span: (start_span..self.err_offset()).into(),
                        });
                    }
                }
                b => {
                    if !b.is_ascii_whitespace() {
                        return Err(ParseError::InvalidInt {
                            err_span: (start_span..self.err_offset()).into(),
                        });
                    }
                    break;
                }
            }
        }
        if is_negated {
            parsed = -parsed;
        }
        I::try_from(parsed).map_err(|_| {
            ParseError::LiteralOutOfBound {
                val: parsed,
                // reduce end offset by one, as last byte was a whitespace
                err_span: (start_span..self.err_offset().saturating_sub(1)).into(),
            }
        })
    }

    fn err_offset(&self) -> usize {
        self.offset
    }

    fn err_span(&self) -> SourceSpan {
        self.offset.saturating_sub(1).into()
    }
}

impl ParseError {
    fn err_span(&self) -> Option<SourceSpan> {
        match self {
            ParseError::InvalidInt { err_span }
            | ParseError::LiteralOutOfBound { err_span, .. } => Some(*err_span),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::qcnf::QCNF;
    use proptest::prelude::*;
    use std::io::Cursor;

    proptest! {
        #[test]
        fn doesnt_crash(s in ".*") {
            let reader = Cursor::new(s);
            let _qcnf: Option<QCNF> = QdimacsParser::new(reader).parse().ok();
        }

        #[test]
        fn roundtrip_from_qcnf(input in crate::qcnf::strategy::qcnf(1..4, 1..10, 0..100, 0..10)) {
            let qdimacs = format!("{input}");
            let reader = Cursor::new(qdimacs);
            let parsed: QCNF = QdimacsParser::new(reader).parse()?;
            assert_eq!(parsed, input);
        }
    }

    macro_rules! expect_error {
        ( $input:expr, $pat:pat ) => {
            let reader = std::io::Cursor::new(&$input);
            match QdimacsParser::new(reader).parse::<crate::qcnf::QCNF>() {
                Ok(parsed) => panic!("Expexcted errror but got {:?}", parsed),
                Err(err) => match err {
                    $pat => (),
                    _ => panic!("Unexpected error {:?}", err),
                },
            }
        };
    }

    #[test]
    fn minimal() -> Result<(), ParseError> {
        let qdimacs = "p cnf 0 0";
        let reader = Cursor::new(qdimacs);
        let qbf: QCNF = QdimacsParser::new(reader).parse()?;
        println!("{qbf}");
        Ok(())
    }

    #[test]
    fn no_matrix() -> Result<(), ParseError> {
        let qdimacs = "p cnf 10 0\ne 1 2 3 0\na 4 5 6 0\n";
        let reader = Cursor::new(qdimacs);
        let qbf: QCNF = QdimacsParser::new(reader).parse()?;
        println!("{qbf}");
        Ok(())
    }

    #[test]
    fn no_prefix() -> Result<(), ParseError> {
        let qdimacs = "p cnf 10 2\n1 2 3 0\n4 5 6 0\n";
        let reader = Cursor::new(qdimacs);
        let qbf: QCNF = QdimacsParser::new(reader).parse()?;
        println!("{qbf}");
        Ok(())
    }

    #[test]
    fn simple() -> Result<(), ParseError> {
        let qdimacs = "
		c satisfiable.qdimacs
		p cnf 3 4
		e 1 0
		a 2 0
		e 3 0
		-1 2 -3 0
		2 3 0
		-2 3 0
		1 3 0
		";
        let reader = Cursor::new(qdimacs);
        let qbf: QCNF = QdimacsParser::new(reader).parse()?;
        println!("{qbf}");
        Ok(())
    }

    #[test]
    fn roundtrip() -> Result<(), ParseError> {
        let orig = qcnf_formula![
            e 1; a 2; e 3;
            -1 2 -3;
            2 3;
            -2 3;
            1 3;
        ];
        let qdimacs = format!("{orig}");
        let reader = Cursor::new(qdimacs);
        let parsed: QCNF = QdimacsParser::new(reader).parse()?;
        assert_eq!(orig, parsed);
        Ok(())
    }

    #[test]
    fn missing_header() {
        expect_error!(b"", ParseError::MissingHeader);
        expect_error!(b"c comment\nc comments\n\n", ParseError::MissingHeader);
    }

    #[test]
    fn out_of_bound() {
        // i32::MAX = 2147483647 is the largest representable literal
        // i32::MIN = -2147483648 is not a valid literal
        expect_error!(b"p cnf 0 0\n1 2147483648 3 0", ParseError::LiteralOutOfBound { .. });
        expect_error!(b"p cnf 0 0\n1 -2147483648 3 0", ParseError::LiteralOutOfBound { .. });
    }

    #[test]
    fn end_of_file() {
        expect_error!(b"p cnf 0 0\n1 2 3 0\n-1 2 3", ParseError::UnexpectedEndOfFile { .. });
    }

    #[test]
    fn header() -> Result<(), ParseError> {
        let qdimacs = "p cnf     10      0";
        let reader = Cursor::new(qdimacs);
        let _qcnf: QCNF = QdimacsParser::new(reader).parse()?;

        expect_error!(
            b"p dnf 2 2",
            ParseError::InvalidHeader { reason: HeaderError::InvalidPrefix, .. }
        );
        expect_error!(
            b"pcnf 2 2",
            ParseError::InvalidHeader { reason: HeaderError::InvalidPrefix, .. }
        );
        expect_error!(
            b"p cnf -2 2",
            ParseError::InvalidHeader { reason: HeaderError::InvalidVariableCount, .. }
        );
        expect_error!(
            b"p cnf 2 -2",
            ParseError::InvalidHeader { reason: HeaderError::InvalidClauseCount, .. }
        );
        Ok(())
    }

    #[test]
    fn num_clauses() {
        expect_error!(
            b"p cnf 3 2\n1 -2 0\n2 -3 0\n3 -1 0\n",
            ParseError::NumClausesMismatch { expected: 2, found: 3 }
        );
    }
}

#[cfg(kani)]
mod verification {
    use super::*;
    use crate::qcnf::*;

    #[kani::proof]
    #[kani::unwind(0)]
    pub fn parsing() {
        const LIMIT: usize = 1;
        let contents: [u8; LIMIT] = kani::any();
        let _: Option<QCNF> = QdimacsParser::new(&contents as &[u8]).parse().ok();
    }
}
