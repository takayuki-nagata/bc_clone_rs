// SPDX-License-Identifier: MIT

//! Top level of the specification: options, inputs and the observable outcome.

use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

/// Exit status of the oracle for inputs outside the specification (see the crate docs).
pub const NOT_MODELED: u8 = 125;

exec_spec_verified! {

/// Command-line options that the specification models (`-s` and `-w`).
pub struct Options {
    pub reject_extensions: bool,
    pub warn_extensions: bool,
}

/// One input source: a file operand, or standard input (named `(standard_in)`), as bytes.
pub struct Input {
    pub name: Seq<u8>,
    pub text: Seq<u8>,
}

/// Everything a run of `bc_clone` makes observable.
pub struct Outcome {
    pub stdout: Seq<u8>,
    pub stderr: Seq<u8>,
    pub status: u8,
}

/// The meaning of `bc_clone` with `opts` on `inputs` (the file operands in order, then
/// standard input).
pub open spec fn run(opts: Options, inputs: Seq<Input>) -> Outcome {
    Outcome { stdout: seq![], stderr: seq![], status: 125u8 }
}

} // exec_spec_verified!

} // verus!
