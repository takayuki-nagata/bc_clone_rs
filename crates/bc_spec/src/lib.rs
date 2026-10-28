// SPDX-License-Identifier: MIT

//! Executable formal specification of `bc_clone` (the reference interpreter).
//!
//! The specification is a Verus `spec fn` from the program inputs (options, then each file
//! operand and standard input as bytes) to the observable outcome (stdout bytes, stderr bytes,
//! exit status). `exec_spec_verified!` compiles each `spec fn` into an `exec_*` function and
//! proves that the two are equal; the binary `bc_spec_oracle` (`src/main.rs`) runs the compiled
//! function as the oracle of the differential tests (`scripts/build_spec_oracle.sh`,
//! `crates/bc_cli/tests/spec_differential.rs`).
//!
//! **Authority.** POSIX.1-2024 `bc` and the implementation-defined choices in
//! `docs/COMPATIBILITY.md` are what this specification encodes. Where it disagrees with
//! `bc_core`, decide which side follows those documents and fix that side.
//!
//! **Layers.** Numbers mean values of the L0 model in `spec_num.rs` (`SpecBCNum` over `int`).
//! The executable layer (L1) stores them as decimal digit sequences, because `exec_spec` cannot
//! compile `int`; each L1 operation carries a lemma that it computes the L0 operation.
//!
//! **For the refinement proofs** of `bc_core`: `fuel` proves that a result
//! that did not run out of fuel stays the same with more fuel, and `values` that the evaluator
//! uses numbers only through their L0 values.
//!
//! **Writing rules** (forced by `exec_spec_verified!`):
//! - recurse on `drop_first`, not on an index `i + 1`;
//! - no `*` on machine integers (the generated code cannot carry `nonlinear_arith` hints);
//!   multiply digit sequences by repeated addition;
//! - no recursive types: the syntax tree is an arena (`Seq<Node>` with `usize` children);
//! - no `Map` fields: environments are association lists;
//! - no typed `let`, no `&` expressions;
//! - keep functions small: a large one can exceed the resource limit in its generated
//!   equivalence proof, which `#[verifier::rlimit]` does not reach (split it, as `p_reg`).
//!
//! Functions that are compiled with `exec_spec_unverified!` because their equivalence proof
//! does not go through are listed here: (none yet).
//!
//! **Not modeled** (the oracle exits with `NOT_MODELED`): `-l`, the interactive REPL and SIGINT,
//! unreadable files, memory exhaustion. `BC_SPEC_MAX_DEPTH` sets `max_depth` (default 100000,
//! the release build of `bc_clone`).

// Imports used only by `spec fn`s and proofs are unused once `verus!` erases them.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

pub mod convert;
pub mod eval;
pub mod fuel;
pub mod lexer;
pub mod num;
pub mod output;
pub mod parser;
pub mod power;
pub mod spec_num;
pub mod top;
pub mod values;
