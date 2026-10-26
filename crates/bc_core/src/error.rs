// SPDX-License-Identifier: MIT

//! Error type shared by the lexer, parser, evaluator, and numeric routines.
//!
//! Diagnostic texts follow `docs/COMPATIBILITY.md` §3.2.

use alloc::string::String;
use core::fmt;

/// A runtime failure raised while evaluating an expression or statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
    DivideByZero,
    ModuloByZero,
    NegativeSqrt,
    UndefinedFunction(String),
    ParameterMismatch,
    ParameterTypeMismatch(String),
    ArraySubscriptOutOfBounds(String),
    ExponentTooLarge,
    ScaleTooLarge,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DivideByZero => f.write_str("Divide by zero"),
            Self::ModuloByZero => f.write_str("Modulo by zero"),
            Self::NegativeSqrt => f.write_str("Square root of a negative number"),
            Self::UndefinedFunction(name) => write!(f, "Function {} not defined.", name),
            Self::ParameterMismatch => f.write_str("Parameter number mismatch"),
            Self::ParameterTypeMismatch(name) => {
                write!(f, "Parameter type mismatch parameter {}.", name)
            }
            Self::ArraySubscriptOutOfBounds(name) => {
                write!(f, "Array {} subscript out of bounds.", name)
            }
            Self::ExponentTooLarge => f.write_str("exponent too large in raise"),
            Self::ScaleTooLarge => f.write_str("scale too large"),
        }
    }
}

/// Any condition that stops the processing of an input unit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BcError {
    /// `quit` was read. Not a failure: processing stops at this point.
    Quit,
    /// A lexical or syntax error. `line` is 1-based within the parsed text; `message` is the
    /// user-facing text and `detail` describes what the parser expected (for debugging only).
    Syntax {
        line: usize,
        message: String,
        detail: String,
    },
    /// A runtime error raised inside function `func` (`None` at top level).
    Runtime {
        kind: RuntimeError,
        func: Option<String>,
    },
}

impl BcError {
    /// Creates a generic `syntax error` diagnostic.
    pub fn syntax(line: usize, detail: String) -> Self {
        Self::Syntax {
            line,
            message: String::from("syntax error"),
            detail,
        }
    }

    /// Attributes a runtime error to function `name` unless an inner call already claimed it.
    pub fn in_function(self, name: &str) -> Self {
        match self {
            Self::Runtime { kind, func: None } => Self::Runtime {
                kind,
                func: Some(String::from(name)),
            },
            other => other,
        }
    }
}

impl From<RuntimeError> for BcError {
    fn from(kind: RuntimeError) -> Self {
        Self::Runtime { kind, func: None }
    }
}

impl fmt::Display for BcError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Quit => f.write_str("quit"),
            Self::Syntax { line, message, .. } => write!(f, "{}: {}", line, message),
            Self::Runtime { kind, func } => write!(
                f,
                "Runtime error (func={}): {}",
                func.as_deref().unwrap_or("(main)"),
                kind
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    #[test]
    fn display_formats() {
        assert_eq!(BcError::Quit.to_string(), "quit");
        assert_eq!(
            BcError::syntax(3, "expected Rparen".to_string()).to_string(),
            "3: syntax error"
        );
        let err = BcError::from(RuntimeError::ParameterTypeMismatch("a".to_string()));
        assert_eq!(
            err.to_string(),
            "Runtime error (func=(main)): Parameter type mismatch parameter a."
        );
        assert_eq!(
            err.in_function("f").in_function("g").to_string(),
            "Runtime error (func=f): Parameter type mismatch parameter a."
        );
        assert_eq!(BcError::Quit.in_function("f"), BcError::Quit);
    }
}
