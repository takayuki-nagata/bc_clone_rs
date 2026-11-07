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

#[allow(
    clippy::assign_op_pattern,
    clippy::derivable_impls,
    clippy::len_zero,
    clippy::single_match,
    clippy::too_many_arguments,
    reason = "the code keeps the forms that the proofs reason about"
)]
pub mod driver;
pub mod error;
pub mod eval;
pub(crate) mod format;
#[cfg(kani)]
mod kani_proofs;
pub mod math;
mod mathlib;
pub mod parser;
#[cfg(verus_keep_ghost)]
mod real_arith;
#[cfg(verus_keep_ghost)]
pub use bc_spec::spec_num;
mod bigint;
#[cfg(verus_keep_ghost)]
mod refine;
mod trusted_bigint;
#[cfg(verus_keep_ghost)]
mod trusted_math;
#[cfg(verus_keep_ghost)]
mod trusted_std;
pub mod verified_kernels;
#[cfg(verus_keep_ghost)]
pub mod verus_proofs;

pub use driver::{RunSummary, STDIN_SOURCE, SourceUnits, UnitAccumulator, UnitOutcome};
pub use error::{BcError, RuntimeError};
pub use eval::{BcWriter, ErrWriter, Evaluator, WrappedStdout};
pub use math::BCNum;
pub use parser::{
    Arg, Code, DEFAULT_MAX_DEPTH, ExtensionPolicy, FunctionDecl, FunctionDef, Lexer, Node, Param,
    Parser, Register, Token, TokenType,
};
