// SPDX-License-Identifier: MIT

//! Public conversions to and from text, not verified because they use formatting and string
//! operations that Verus does not model. Each checks its preconditions through verified code
//! (`from_digit_values_checked`, `checked_format_bytes`) before anything else.

use alloc::string::String;
use core::fmt;

use crate::error::{BcError, RuntimeError};
use crate::math::{BCNum, literal_digit_values};

impl fmt::Display for RuntimeError {
    // coverage: miri(display_formats); why: fmt
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

impl fmt::Display for BcError {
    // coverage: miri(display_formats); why: fmt
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

impl BCNum {
    /// Parses the text of a numeric constant (digits `0`-`9` and `A`-`Z`, at most one radix
    /// point, backslash-newlines allowed) under `ibase` into a BCNum, as the evaluator reads a
    /// constant (`literal_digit_values`, then `from_digit_values`). Lowercase letters are read
    /// as uppercase; for other characters the result is unspecified. An `ibase` outside 2 to 16
    /// is `BaseOutOfRange`, and a constant with more than `BC_SCALE_MAX` fraction digits is
    /// `ScaleTooLarge`, rejected before any arithmetic, which keeps the scale invariant.
    // coverage: miri(public_conversions_check_their_bases_and_scale); why: string
    pub fn try_from_string(num_str: &str, ibase: usize) -> Result<Self, RuntimeError> {
        let text = num_str.replace("\\\n", "").to_ascii_uppercase();
        let (ds, fs) = literal_digit_values(text.as_bytes());
        Self::from_digit_values_checked(&ds, &fs, ibase)
    }

    /// Formats the value as a string in `obase`, as `print` writes it (without the newline
    /// and the 70-column wrapping). An `obase` outside 2 to `BC_BASE_MAX` is `BaseOutOfRange`,
    /// and a scale above `BC_SCALE_MAX` is `ScaleTooLarge`.
    // coverage: miri(public_conversions_check_their_bases_and_scale); why: string
    pub fn try_format_obase(&self, obase: usize) -> Result<String, RuntimeError> {
        // The bytes of `format_bytes` are ASCII.
        Ok(self
            .checked_format_bytes(obase)?
            .into_iter()
            .map(char::from)
            .collect())
    }
}

/// Not in `verus!`: vstd's specification of `From::from` (`obeys_from_spec`) does not fit an
/// enum conversion.
impl From<RuntimeError> for BcError {
    // coverage: miri(display_formats); why: trait
    fn from(kind: RuntimeError) -> Self {
        Self::Runtime { kind, func: None }
    }
}
