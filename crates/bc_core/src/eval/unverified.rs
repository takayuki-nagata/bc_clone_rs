// SPDX-License-Identifier: MIT

//! The evaluator's public constructor and its diagnostic stream for front ends. Not verified:
//! `new` takes the writers as trait objects, and `stderr_writer` lends the stream for writes
//! outside the model (a front end's own messages).

use alloc::boxed::Box;

use super::{BcWriter, ErrWriter, Evaluator, WrappedStdout};
use crate::parser::DEFAULT_MAX_DEPTH;

impl Evaluator {
    /// Creates a new Evaluator with abstract BcWriter streams.
    // coverage: miri(running_the_units_one_at_a_time_is_running_the_source); why: dyn
    pub fn new(
        math_enabled: bool,
        stdout_writer: Box<dyn BcWriter>,
        stderr_writer: Box<dyn BcWriter>,
    ) -> Self {
        // The streams and the nesting limit are outside `inv`; `with_streams` establishes it.
        Self::with_streams(
            math_enabled,
            WrappedStdout::new(stdout_writer),
            ErrWriter::new(stderr_writer),
            DEFAULT_MAX_DEPTH,
        )
    }

    /// The diagnostic stream, for a front end's own messages (e.g. a file that cannot be read).
    // coverage: miri(diagnostic_stream_flushes_its_writer); why: boundary
    pub fn stderr_writer(&mut self) -> &mut ErrWriter {
        &mut self.stderr_writer
    }
}
