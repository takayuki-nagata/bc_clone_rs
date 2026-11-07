// SPDX-License-Identifier: MIT

//! Error type shared by the lexer, parser, evaluator, and numeric routines.
//!
//! Diagnostic texts follow `docs/COMPATIBILITY.md` §3.2.

use alloc::string::String;
use core::fmt;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

/// A runtime failure raised while evaluating an expression or statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
    DivideByZero,
    /// Zero raised to a negative power (GNU bc words this one in lower case).
    NegativePowerOfZero,
    ModuloByZero,
    NegativeSqrt,
    UndefinedFunction(String),
    ParameterMismatch,
    ParameterTypeMismatch(String),
    ArraySubscriptOutOfBounds(String),
    ExponentTooLarge,
    ScaleTooLarge,
    /// A math library argument whose result cannot be computed: `e(x)` with an integer part
    /// above `EXP_ARG_MAX`, or `j(n,x)` with an order outside `i64` that is not provably 0.
    MathArgumentTooLarge,
    /// More nested evaluation (mostly recursion) than the evaluator's `max_depth` allows.
    NestingTooDeep,
    /// An `ibase` or `obase` outside its range, passed to a public conversion function
    /// (`BCNum::try_from_string`, `BCNum::try_format_obase`). Evaluation never raises it: the
    /// evaluator clamps the registers.
    BaseOutOfRange,
}

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExBcError(BcError);

} // verus!

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DivideByZero => f.write_str("Divide by zero"),
            Self::NegativePowerOfZero => f.write_str("divide by zero"),
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
            Self::MathArgumentTooLarge => f.write_str("argument too large"),
            Self::NestingTooDeep => f.write_str("nesting too deep"),
            Self::BaseOutOfRange => f.write_str("base out of range"),
        }
    }
}

/// Any condition that stops the processing of an input unit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BcError {
    /// `quit` was read. Not a failure: processing stops at this point.
    Quit,
    /// A lexical or syntax error. `line` is 1-based within the parsed text; `message` is the
    /// user-facing text.
    Syntax { line: usize, message: String },
    /// A runtime error raised inside function `func` (`None` at top level).
    Runtime {
        kind: RuntimeError,
        func: Option<String>,
    },
}

impl BcError {
    /// Creates a generic `syntax error` diagnostic.
    pub fn syntax(line: usize) -> Self {
        Self::Syntax {
            line,
            message: String::from("syntax error"),
        }
    }
}

verus! {

impl BcError {
    /// Attributes a runtime error to function `name` unless an inner call already claimed it.
    #[allow(clippy::ptr_arg, reason = "the specification relates the attributed name to the String")]
    pub fn in_function(self, name: &String) -> (r: Self)
        ensures
            r == match self {
                BcError::Runtime { kind, func: None } => BcError::Runtime { kind, func: Some(*name) },
                _ => self,
            },
    {
        match self {
            Self::Runtime { kind, func: None } => Self::Runtime { kind, func: Some(name.clone()) },
            other => other,
        }
    }
}

} // verus!

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
        assert_eq!(BcError::syntax(3).to_string(), "3: syntax error");
        let err = BcError::from(RuntimeError::ParameterTypeMismatch("a".to_string()));
        assert_eq!(
            err.to_string(),
            "Runtime error (func=(main)): Parameter type mismatch parameter a."
        );
        assert_eq!(
            err.in_function(&"f".to_string())
                .in_function(&"g".to_string())
                .to_string(),
            "Runtime error (func=f): Parameter type mismatch parameter a."
        );
        assert_eq!(BcError::Quit.in_function(&"f".to_string()), BcError::Quit);
    }

    #[test]
    fn every_runtime_error_has_its_message() {
        let a = || "a".to_string();
        let cases = [
            (RuntimeError::DivideByZero, "Divide by zero"),
            (RuntimeError::NegativePowerOfZero, "divide by zero"),
            (RuntimeError::ModuloByZero, "Modulo by zero"),
            (
                RuntimeError::NegativeSqrt,
                "Square root of a negative number",
            ),
            (
                RuntimeError::UndefinedFunction(a()),
                "Function a not defined.",
            ),
            (RuntimeError::ParameterMismatch, "Parameter number mismatch"),
            (
                RuntimeError::ParameterTypeMismatch(a()),
                "Parameter type mismatch parameter a.",
            ),
            (
                RuntimeError::ArraySubscriptOutOfBounds(a()),
                "Array a subscript out of bounds.",
            ),
            (
                RuntimeError::ExponentTooLarge,
                "exponent too large in raise",
            ),
            (RuntimeError::ScaleTooLarge, "scale too large"),
            (RuntimeError::MathArgumentTooLarge, "argument too large"),
            (RuntimeError::NestingTooDeep, "nesting too deep"),
            (RuntimeError::BaseOutOfRange, "base out of range"),
        ];
        for (kind, message) in cases {
            assert_eq!(kind.to_string(), message);
        }
    }
}
