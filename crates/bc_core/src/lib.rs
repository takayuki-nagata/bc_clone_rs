// SPDX-License-Identifier: MIT

//! Arbitrary-precision bc engine library compatible with no_std + alloc.

#![no_std]

extern crate alloc;

#[cfg(test)]
extern crate std;

pub mod eval;
pub mod math;
pub mod parser;

pub use eval::{BcWriter, Evaluator, WrappedStdout};
pub use math::BCNum;
pub use parser::{Expr, ExprOrArray, FunctionDef, Lexer, Param, Parser, Stmt, Token, TokenType};
