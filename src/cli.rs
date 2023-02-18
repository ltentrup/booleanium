use miette::{Diagnostic, Result};
use std::{env::args, io::Read, path::PathBuf};
use thiserror::Error;

#[derive(Debug, Error, Diagnostic)]
pub enum ArgError {
    #[error("Expect single argument containing the path to a QDIMACS file")]
    ExpectedFile,

    #[error("Path {} does not exist", path.display())]
    FileDoesNotExist { path: PathBuf },

    #[error("{} is not a file", path.display())]
    NotAFile { path: PathBuf },

    #[error("Cannot read file {}: {}", path.display(), err)]
    CannotReadFile { path: PathBuf, err: std::io::Error },

    #[error("Cannot read from stdin: {}", err)]
    CannotReadStdIn { err: std::io::Error },
}

pub fn content_from_args() -> Result<Vec<u8>> {
    let mut args = args();
    if args.len() == 1 {
        tracing::info!("No arguments provided, read from stdin");
        let mut buffer = Vec::new();
        std::io::stdin()
            .read_to_end(&mut buffer)
            .map_err(|err| ArgError::CannotReadStdIn { err })?;
        return Ok(buffer);
    } else if args.len() != 2 {
        return Err(ArgError::ExpectedFile.into());
    }
    let file_path = args.nth(1).unwrap();
    let file_path = PathBuf::from(file_path);
    if !file_path.exists() {
        return Err(ArgError::FileDoesNotExist { path: file_path }.into());
    }
    if !file_path.is_file() {
        return Err(ArgError::NotAFile { path: file_path }.into());
    }
    let contents = std::fs::read(&file_path)
        .map_err(|err| ArgError::CannotReadFile { path: file_path.clone(), err })?;
    Ok(contents)
}
