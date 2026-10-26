// SPDX-License-Identifier: MIT

//! Arbitrary-precision bc engine library compatible with no_std + alloc.

#![no_std]

extern crate alloc;

#[cfg(test)]
extern crate std;

#[cfg(not(verus_keep_ghost))]
pub mod driver;
#[cfg(not(verus_keep_ghost))]
pub mod error;
#[cfg(not(verus_keep_ghost))]
pub mod eval;
#[cfg(kani)]
mod kani_proofs;
#[cfg(not(verus_keep_ghost))]
pub mod math;
#[cfg(not(verus_keep_ghost))]
pub mod parser;
pub mod verified_kernels;
#[cfg(verus_keep_ghost)]
pub mod verus_proofs;

#[cfg(not(verus_keep_ghost))]
pub use driver::{RunSummary, STDIN_SOURCE, UnitAccumulator, UnitOutcome};
#[cfg(not(verus_keep_ghost))]
pub use error::{BcError, RuntimeError};
#[cfg(not(verus_keep_ghost))]
pub use eval::{BcWriter, Evaluator, WrappedStdout};
#[cfg(not(verus_keep_ghost))]
pub use math::BCNum;
#[cfg(not(verus_keep_ghost))]
pub use parser::{Expr, ExprOrArray, FunctionDef, Lexer, Param, Parser, Stmt, Token, TokenType};
