// SPDX-License-Identifier: MIT

//! Arbitrary-precision bc engine library compatible with no_std + alloc.

#![no_std]
// `bc_core` must not panic on any input (AGENTS.md, "Error handling contract"): no unwrapping,
// no explicit panics, and no lossy integer casts outside tests. Each remaining exception carries
// an `allow` with the invariant that justifies it.
#![cfg_attr(
    not(test),
    deny(
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::panic,
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        clippy::cast_possible_wrap
    )
)]

extern crate alloc;

// The proofs refer to the executable specification, which only the `verify` feature links.
#[cfg(all(verus_keep_ghost, not(feature = "verify")))]
compile_error!("verify bc_core with `cargo verus verify -p bc_core --features verify`");

#[cfg(test)]
extern crate std;

#[cfg(not(verus_keep_ghost))]
pub mod driver;
pub mod error;
#[cfg(not(verus_keep_ghost))]
pub mod eval;
#[cfg(kani)]
mod kani_proofs;
pub mod math;
#[cfg(not(verus_keep_ghost))]
mod mathlib;
#[cfg(not(verus_keep_ghost))]
pub mod parser;
#[cfg(verus_keep_ghost)]
pub use bc_spec::spec_num;
mod trusted_bigint;
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
pub use parser::{
    DEFAULT_MAX_DEPTH, Expr, ExprOrArray, ExtensionPolicy, FunctionDef, Lexer, Param, Parser,
    Register, Stmt, Token, TokenType,
};
