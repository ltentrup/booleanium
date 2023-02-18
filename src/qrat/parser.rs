use crate::{clause::Clause, literal::Lit};
use std::{
    fmt::Display,
    io::{BufRead, BufReader, Read},
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParserError {
    #[error("The underlying IO has failed")]
    IO(#[from] std::io::Error),
    #[error("Invalid character: {byte}")]
    InvalidCharacter { byte: u8 },
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct QratProof {
    trace: Vec<QratClause>,
}

impl QratProof {
    fn add(&mut self, clause: QratClause) {
        self.trace.push(clause);
    }
}

impl Display for QratProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for clause in &self.trace {
            writeln!(f, "{}", clause)?;
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct QratParser {
    trace: QratProof,

    current_clause: Option<QratClause>,
    state: ParserState,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct QratClause {
    clause: Vec<Lit>,
    operation: QratOperation,
}

impl Display for QratClause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.operation {
            QratOperation::Addition => write!(
                f,
                "{}",
                self.clause
                    .iter()
                    .map(|l| format!("{}", l))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            QratOperation::Deletion => write!(
                f,
                "d {}",
                self.clause
                    .iter()
                    .map(|l| format!("{}", l))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            QratOperation::UnivElim => write!(
                f,
                "u {}",
                self.clause
                    .iter()
                    .map(|l| format!("{}", l))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QratOperation {
    Addition,
    Deletion,
    UnivElim,
}

#[derive(Debug, Clone, Copy)]
enum ParserState {
    ParseClause,
    ParseLiteral { negated: bool, literal: i32 },
}

impl Default for ParserState {
    fn default() -> Self {
        Self::ParseClause
    }
}

impl QratParser {
    pub fn parse(reader: impl Read) -> Result<QratProof, ParserError> {
        let mut reader = BufReader::new(reader);
        let mut parser = Self::default();
        loop {
            let data = reader.fill_buf()?;
            if data.is_empty() {
                break;
            }
            parser.parse_chunk(data)?;
            let len = data.len();
            reader.consume(len);
        }
        Ok(parser.trace)
    }

    fn parse_chunk(&mut self, chunk: &[u8]) -> Result<(), ParserError> {
        for &byte in chunk {
            match self.state {
                ParserState::ParseClause => match byte {
                    b'-' => {
                        self.state = ParserState::ParseLiteral {
                            negated: true,
                            literal: 0,
                        }
                    }
                    b'0'..=b'9' => {
                        self.state = ParserState::ParseLiteral {
                            negated: false,
                            literal: (byte - b'0') as i32,
                        };
                    }
                    b'd' => {
                        self.current_clause = Some(QratClause {
                            clause: Vec::default(),
                            operation: QratOperation::Deletion,
                        });
                    }
                    b'u' => {
                        self.current_clause = Some(QratClause {
                            clause: Vec::default(),
                            operation: QratOperation::UnivElim,
                        });
                    }
                    b' ' | b'\t' | b'\n' | b'\r' => {}
                    _ => return Err(ParserError::InvalidCharacter { byte }),
                },
                ParserState::ParseLiteral { negated, literal } => match byte {
                    b'0'..=b'9' => {
                        self.state = ParserState::ParseLiteral {
                            negated,
                            literal: literal * 10 + (byte - b'0') as i32,
                        }
                    }
                    b' ' | b'\t' | b'\n' | b'\r' => {
                        if literal == 0 {
                            if negated {
                                todo!("error: negated 0");
                            }
                            self.trace
                                .add(self.current_clause.take().unwrap_or(QratClause {
                                    clause: Vec::default(),
                                    operation: QratOperation::Addition,
                                }));
                        } else {
                            let lit = Lit::from_dimacs(if negated { -literal } else { literal });
                            let current = self.current_clause.get_or_insert(QratClause {
                                clause: Vec::default(),
                                operation: QratOperation::Addition,
                            });
                            current.clause.push(lit);
                        }
                        self.state = ParserState::ParseClause;
                    }
                    _ => return Err(ParserError::InvalidCharacter { byte }),
                },
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    /// Example from Figure 2 of *Solution Validation and Extraction for QBF Preprocessing*
    /// by Heule, Seidl, and Biere.
    #[test]
    fn simple_sat() -> Result<(), Box<dyn std::error::Error>> {
        let _true_qbf = "
			p cnf 3 3
			a 1 0
			e 2 3 0
			 1  2 0
			-1  3 0
			-2 -3 0
		";
        let qrat_proof = "
			  -1 -2 0
			d  3 -1 0
			d -3 -2 0
			d -2 -1 0
			d  2  1 0
		";

        let qrat_proof = QratParser::parse(qrat_proof.as_bytes())?;
        let reparsed = QratParser::parse(format!("{}", qrat_proof).as_bytes())?;
        assert_eq!(qrat_proof, reparsed);

        Ok(())
    }

    /// Example from Figure 2 of *Solution Validation and Extraction for QBF Preprocessing*
    /// by Heule, Seidl, and Biere.
    #[test]
    fn simple_unsat() -> Result<(), Box<dyn std::error::Error>> {
        let _false_qbf = "
			p cnf 3 3
			a 1 0
			e 2 3 0
			 1  2 0
			 1  3 0
			-2 -3 0
		";
        let qrat_proof = "
			  -2  0
			d -2 -3 0
			   1  0
			u  1  0
			   0
		";

        let qrat_proof = QratParser::parse(qrat_proof.as_bytes())?;
        let reparsed = QratParser::parse(format!("{}", qrat_proof).as_bytes())?;
        assert_eq!(qrat_proof, reparsed);

        Ok(())
    }
}
