// SPDX-License-Identifier: MIT

//! The public entry points of the driver, which front ends call. Not verified: each calls the
//! verified function of the same name with `_ref`, whose precondition is the invariant of a
//! type whose fields are private to the crate (`AGENTS.md`), and passes arbitrary ghost
//! arguments, for which the theorems hold.

use alloc::vec::Vec;

use super::{RunSummary, SourceUnits, UnitAccumulator, UnitOutcome};
use crate::eval::Evaluator;
#[cfg(not(verus_keep_ghost))]
use verus_builtin::Ghost;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

impl Evaluator {
    /// Parses and executes one input unit, reporting any error to `stderr_writer`.
    ///
    /// `source` names the input in syntax diagnostics (a file name, or [`STDIN_SOURCE`]) and
    /// `first_line` is the line number of the unit's first line within that source.
    #[verifier::external_body]
    // coverage: miri(unit_beyond_the_limit_is_rejected_without_being_scanned); why: boundary
    pub fn run_unit(&mut self, unit: &[u8], source: &str, first_line: usize) -> UnitOutcome {
        let policy = self.extension_policy;
        let max_depth = self.max_depth;
        self.run_unit_ref(unit, source, first_line, policy, max_depth, Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }

    /// Splits `text` into units and runs each one, continuing after errors until the end of
    /// the text or `quit`. `text` is bytes and need not be UTF-8.
    #[verifier::external_body]
    // coverage: miri(running_the_units_one_at_a_time_is_running_the_source); why: boundary
    pub fn run_source(&mut self, text: &[u8], source: &str) -> RunSummary {
        self.run_source_ref(text, source, Ghost(arbitrary()), Ghost(arbitrary()))
    }

    /// Runs the next unit of `units`, or returns `None` after the last one. A front end that
    /// calls this until `None` or [`UnitOutcome::Quit`] runs the text as [`Evaluator::run_source`]
    /// does.
    #[verifier::external_body]
    // coverage: miri(running_the_units_one_at_a_time_is_running_the_source); why: boundary
    pub fn run_next_unit(&mut self, units: &mut SourceUnits, source: &str) -> Option<UnitOutcome> {
        let policy = self.extension_policy;
        let limit = self.max_depth;
        self.run_next_source_unit_ref(units, source, policy, limit, Ghost(arbitrary()), Ghost(arbitrary()))
    }
}

impl UnitAccumulator {
    /// Appends one line (with its trailing newline, if any). Returns the completed unit and the
    /// line number of its first line when the accumulated text forms a complete unit.
    #[verifier::external_body]
    // coverage: miri(accumulator_groups_continuations_and_blocks); why: boundary
    pub fn push_line(&mut self, line: &[u8]) -> Option<(Vec<u8>, usize)> {
        self.push_line_ref(line)
    }
}

impl SourceUnits {
    /// The units of `text`, which is bytes and need not be UTF-8.
    #[verifier::external_body]
    // coverage: miri(running_the_units_one_at_a_time_is_running_the_source); why: boundary
    pub fn new(text: Vec<u8>) -> Self {
        Self::new_ref(text)
    }
}

} // verus!

impl core::fmt::Debug for UnitAccumulator {
    // coverage: miri(accumulator_debug_shows_its_lines); why: fmt
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("UnitAccumulator")
            .field("buf", &self.buf)
            .field("start_line", &self.start_line)
            .field("next_line", &self.next_line)
            .finish()
    }
}
