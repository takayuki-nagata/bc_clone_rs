// SPDX-License-Identifier: MIT

//! The output streams, trusted: Verus sees them only through the models `out_log`, `out_col`
//! and `err_log`.
//!
//! The wrappers `WrappedStdout::write_bytes`, `flush_out`, `ErrWriter::write_bytes` and
//! `flush_err` are assumed to change the models as their contracts say: a writer is taken to
//! store exactly the bytes it receives, which the default `BcWriter::write_bytes` does not do
//! for invalid UTF-8, nor the bare-metal UART, which turns `\n` into `\r\n`; a failing writer
//! is outside the model. `WrappedStdout::new` and `ErrWriter::new` are taken to start with
//! empty logs. The tests below run each wrapper.

use alloc::boxed::Box;
use alloc::string::String;
use core::fmt::Write as FmtWrite;

use crate::format::wrap_output;
#[cfg(verus_keep_ghost)]
use bc_spec::output::write_wrapped;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Abstract output writer trait compatible with both no_std and std environments.
pub trait BcWriter: FmtWrite + Send {
    /// Writes bytes. A string literal is printed byte for byte, so the bytes need not be UTF-8.
    /// The default implementation passes them to `write_str`, replacing each invalid UTF-8
    /// sequence with U+FFFD; a writer to a byte stream overrides it to write them unchanged.
    // coverage: miri(default_writer_keeps_text_and_replaces_invalid_utf8); why: string, fmt
    fn write_bytes(&mut self, b: &[u8]) -> core::fmt::Result {
        match core::str::from_utf8(b) {
            Ok(text) => self.write_str(text),
            Err(_) => self.write_str(&String::from_utf8_lossy(b)),
        }
    }

    /// Flushes any buffered content.
    // coverage: miri(default_writer_keeps_text_and_replaces_invalid_utf8); why: fmt
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

impl BcWriter for String {}

impl WrappedStdout {
    /// Creates a new WrappedStdout writing to the given writer.
    // coverage: miri(stream_wrappers_pass_exactly_their_bytes); why: dyn
    pub fn new(writer: Box<dyn BcWriter>) -> Self {
        Self { writer, col: 0 }
    }

    /// Writes a string to the output stream with POSIX line wrapping: a backslash-newline
    /// before a character at column 68 or beyond (`format::wrap_output`, verified against the
    /// specification's `write_wrapped`).
    // coverage: miri(front_end_methods_reach_the_writer); why: dyn
    pub fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let (out, col) = wrap_output(self.col, s.as_bytes());
        self.col = col;
        self.writer.write_bytes(&out)
    }

    /// Flushes the underlying writer.
    // coverage: miri(front_end_methods_reach_the_writer); why: dyn
    pub fn flush(&mut self) -> core::fmt::Result {
        self.writer.flush()
    }
}

verus! {

/// Wrapper to write output characters with POSIX-style 70-character line wrapping. Opaque to
/// Verus: the refinement proofs see it through `out_log` and `out_col`.
#[verifier::external_body]
pub struct WrappedStdout {
    writer: Box<dyn BcWriter>,
    col: usize,
}

/// The diagnostic stream. Opaque to Verus: the refinement proofs see it through `err_log`.
#[verifier::external_body]
pub struct ErrWriter {
    writer: Box<dyn BcWriter>,
}

/// The bytes written to standard output so far (the model of the output stream).
pub uninterp spec fn out_log(w: &WrappedStdout) -> Seq<u8>;

/// The output column of standard output (`write_wrapped`'s column).
pub uninterp spec fn out_col(w: &WrappedStdout) -> u64;

/// The bytes written to the diagnostic stream so far.
pub uninterp spec fn err_log(w: &ErrWriter) -> Seq<u8>;

impl WrappedStdout {
    /// Writes `b` to standard output with POSIX line wrapping (the verified
    /// `format::wrap_output`). Trusted: the writer's `BcWriter::write_bytes` receives exactly
    /// the wrapped bytes, as the specification's `write_wrapped` describes (a writer that stores
    /// text replaces invalid UTF-8 there); a failing writer is outside the model.
    // coverage: miri(stream_wrappers_pass_exactly_their_bytes)
    #[verifier::external_body]
    pub(crate) fn write_bytes(&mut self, b: &[u8])
        ensures
            (out_log(final(self)), out_col(final(self))) == write_wrapped(out_log(old(self)), out_col(old(self)), b@),
    {
        let (out, col) = wrap_output(self.col, b);
        self.col = col;
        let _ = self.writer.write_bytes(&out);
    }

    /// Flushes the underlying writer (no effect on what has been written).
    // coverage: miri(stream_wrappers_pass_exactly_their_bytes)
    #[verifier::external_body]
    pub(crate) fn flush_out(&mut self)
        ensures
            out_log(final(self)) == out_log(old(self)),
            out_col(final(self)) == out_col(old(self)),
    {
        let _ = self.writer.flush();
    }
}

impl ErrWriter {
    /// Writes `b` to the diagnostic stream. Trusted: the writer's `BcWriter::write_bytes`
    /// receives exactly these bytes; a failing writer is outside the model (diagnostics ignore
    /// write errors).
    // coverage: miri(stream_wrappers_pass_exactly_their_bytes)
    #[verifier::external_body]
    pub(crate) fn write_bytes(&mut self, b: &[u8])
        ensures
            err_log(final(self)) == err_log(old(self)).add(b@),
    {
        let _ = self.writer.write_bytes(b);
    }
    /// Flushes the underlying writer (no effect on what has been written).
    // coverage: miri(stream_wrappers_pass_exactly_their_bytes)
    #[verifier::external_body]
    pub(crate) fn flush_err(&mut self)
        ensures
            err_log(final(self)) == err_log(old(self)),
    {
        let _ = self.writer.flush();
    }
}

} // verus!

impl ErrWriter {
    /// Creates the diagnostic stream writing to the given writer.
    // coverage: miri(stream_wrappers_pass_exactly_their_bytes); why: dyn
    pub fn new(writer: Box<dyn BcWriter>) -> Self {
        Self { writer }
    }

    /// Flushes the underlying writer.
    // coverage: miri(front_end_methods_reach_the_writer); why: dyn
    pub fn flush(&mut self) -> core::fmt::Result {
        self.writer.flush()
    }

    /// Writes formatted text, so that `writeln!(evaluator.stderr_writer, ...)` works without
    /// importing `fmt::Write`.
    // coverage: miri(front_end_methods_reach_the_writer); why: fmt
    pub fn write_fmt(&mut self, args: core::fmt::Arguments<'_>) -> core::fmt::Result {
        FmtWrite::write_fmt(self, args)
    }
}

impl FmtWrite for ErrWriter {
    // coverage: miri(front_end_methods_reach_the_writer); why: fmt
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.writer.write_str(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    use std::sync::{Arc, Mutex};

    /// Records the bytes it receives, unchanged, and the number of flushes.
    #[derive(Clone, Default)]
    struct Recorder(Arc<Mutex<(Vec<u8>, usize)>>);

    impl FmtWrite for Recorder {
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            self.write_bytes(s.as_bytes())
        }
    }

    impl BcWriter for Recorder {
        fn write_bytes(&mut self, b: &[u8]) -> core::fmt::Result {
            if let Ok(mut g) = self.0.lock() {
                g.0.extend_from_slice(b);
            }
            Ok(())
        }
        fn flush(&mut self) -> core::fmt::Result {
            if let Ok(mut g) = self.0.lock() {
                g.1 += 1;
            }
            Ok(())
        }
    }

    fn seen(r: &Recorder) -> (Vec<u8>, usize) {
        r.0.lock().map(|g| g.clone()).unwrap_or_default()
    }

    #[test]
    fn stream_wrappers_pass_exactly_their_bytes() {
        // Standard output: the writer receives `wrap_output` of the bytes, continuing the column.
        let rec = Recorder::default();
        let mut out = WrappedStdout::new(Box::new(rec.clone()));
        let first: Vec<u8> = (0..100u8).map(|i| b'0' + i % 10).collect();
        out.write_bytes(&first);
        out.write_bytes(b"\xff\n");
        let (expected1, col) = wrap_output(0, &first);
        let (expected2, _) = wrap_output(col, b"\xff\n");
        let mut expected = expected1;
        expected.extend_from_slice(&expected2);
        assert_eq!(seen(&rec), (expected.clone(), 0));
        out.flush_out();
        assert_eq!(seen(&rec), (expected, 1));

        // The diagnostic stream: the bytes themselves, not UTF-8.
        let rec = Recorder::default();
        let mut err = ErrWriter::new(Box::new(rec.clone()));
        err.write_bytes(b"a\xffb");
        err.write_bytes(b"\n");
        err.flush_err();
        assert_eq!(seen(&rec), (b"a\xffb\n".to_vec(), 1));
    }

    #[test]
    fn front_end_methods_reach_the_writer() {
        let rec = Recorder::default();
        let mut out = WrappedStdout::new(Box::new(rec.clone()));
        let long = "7".repeat(80);
        assert!(out.write_str(&long).is_ok());
        assert!(out.flush().is_ok());
        assert_eq!(seen(&rec), (wrap_output(0, long.as_bytes()).0, 1));

        let rec = Recorder::default();
        let mut err = ErrWriter::new(Box::new(rec.clone()));
        assert!(err.write_fmt(format_args!("x={}", 1)).is_ok());
        assert!(FmtWrite::write_str(&mut err, ";").is_ok());
        assert!(err.flush().is_ok());
        assert_eq!(seen(&rec), (b"x=1;".to_vec(), 1));
    }

    #[test]
    fn default_writer_keeps_text_and_replaces_invalid_utf8() {
        let mut s = String::new();
        assert!(BcWriter::write_bytes(&mut s, "é1".as_bytes()).is_ok());
        assert!(BcWriter::write_bytes(&mut s, b"\xff").is_ok());
        assert!(BcWriter::flush(&mut s).is_ok());
        assert_eq!(s, "é1\u{fffd}");
    }
}
