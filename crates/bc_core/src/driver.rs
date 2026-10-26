// SPDX-License-Identifier: MIT

//! Input-unit driver shared by every front end (CLI, C API, Zephyr, bare metal, Wasm).
//!
//! Implements `docs/COMPATIBILITY.md` §3.1–3.2: input is split into *units* (one line, or one
//! complete multi-line construct). Each unit is parsed and executed on its own; an error is
//! reported and discards only the rest of its unit, and `quit` stops processing.

use alloc::string::String;
use alloc::vec::Vec;

use crate::error::BcError;
use crate::eval::Evaluator;
use crate::parser::{ExtensionPolicy, Lexer, Parser};
use crate::verified_kernels::verified_repl_block_completeness;

/// Source name used in syntax diagnostics for standard input, as in GNU bc.
pub const STDIN_SOURCE: &str = "(standard_in)";

/// Result of processing one input unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnitOutcome {
    /// The unit was parsed and executed without error.
    Completed,
    /// A syntax or runtime error was reported; the rest of the unit was discarded.
    Failed,
    /// `quit` was read; processing must stop.
    Quit,
}

/// Summary of processing a whole source text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct RunSummary {
    /// Number of units that failed with a syntax or runtime error.
    pub errors: usize,
    /// Whether `quit` stopped processing.
    pub quit: bool,
}

/// Accumulates input lines until they form a complete unit.
///
/// A unit is complete when it does not end with a backslash-newline continuation and has no
/// open brace, comment, or string (see `verified_repl_block_completeness`).
#[derive(Debug, Clone, Default)]
pub struct UnitAccumulator {
    buf: String,
    start_line: usize,
    next_line: usize,
}

impl UnitAccumulator {
    /// Creates an empty accumulator whose first line is line 1.
    pub fn new() -> Self {
        Self {
            buf: String::new(),
            start_line: 1,
            next_line: 1,
        }
    }

    /// Appends one line (with its trailing newline, if any). Returns the completed unit and the
    /// line number of its first line when the accumulated text forms a complete unit.
    pub fn push_line(&mut self, line: &str) -> Option<(String, usize)> {
        if self.buf.is_empty() {
            self.start_line = self.next_line;
        }
        self.buf.push_str(line);
        if line.ends_with('\n') {
            self.next_line += 1;
        }
        if self.buf.ends_with("\\\n") || self.buf.ends_with("\\\r\n") {
            return None;
        }
        if verified_repl_block_completeness(self.buf.as_bytes()).1 {
            return None;
        }
        self.take()
    }

    /// Returns the incomplete text left at end of input, if any, so that it can be reported.
    pub fn finish(&mut self) -> Option<(String, usize)> {
        self.take()
    }

    /// Whether lines of an incomplete unit are waiting for more input (e.g. an open `{`).
    pub fn is_pending(&self) -> bool {
        !self.buf.is_empty()
    }

    /// Discards any partially accumulated unit (used after an interrupt).
    pub fn clear(&mut self) {
        self.buf.clear();
    }

    fn take(&mut self) -> Option<(String, usize)> {
        if self.buf.is_empty() {
            None
        } else {
            Some((core::mem::take(&mut self.buf), self.start_line))
        }
    }
}

impl Evaluator {
    /// Parses and executes one input unit, reporting any error to `stderr_writer`.
    ///
    /// `source` names the input in syntax diagnostics (a file name, or [`STDIN_SOURCE`]) and
    /// `first_line` is the line number of the unit's first line within that source.
    pub fn run_unit(&mut self, unit: &str, source: &str, first_line: usize) -> UnitOutcome {
        let policy = self.extension_policy;
        let mut extension_uses = Vec::new();
        let parsed = Parser::try_new(Lexer::new(unit)).and_then(|mut parser| {
            parser.set_extension_policy(policy);
            let stmts = parser.try_parse_program();
            extension_uses = parser.take_extension_uses();
            stmts
        });

        // `-w` / `-s`: report every use of non-POSIX syntax with GNU bc's prefixes. Under `-s`
        // the unit is not executed.
        let prefix = if policy == ExtensionPolicy::Reject {
            "Error: "
        } else {
            "(Warning) "
        };
        for (line, description) in &extension_uses {
            let _ = writeln!(
                self.stderr_writer,
                "{} {}: {}{}",
                source,
                first_line + line - 1,
                prefix,
                description
            );
        }
        if policy == ExtensionPolicy::Reject && !extension_uses.is_empty() && parsed.is_ok() {
            let _ = self.stderr_writer.flush();
            return UnitOutcome::Failed;
        }

        let result = parsed.and_then(|stmts| {
            for stmt in &stmts {
                self.try_execute(stmt)?;
                if self.quit_flag {
                    return Err(BcError::Quit);
                }
            }
            Ok(())
        });
        let _ = self.stdout_writer.flush();

        match result {
            Ok(()) => UnitOutcome::Completed,
            Err(BcError::Quit) => UnitOutcome::Quit,
            Err(err) => {
                self.break_flag = false;
                self.return_flag = false;
                // Diagnostic formats: `docs/COMPATIBILITY.md` §3.2.
                if let BcError::Syntax { line, message, .. } = &err {
                    let _ = writeln!(
                        self.stderr_writer,
                        "{} {}: {}",
                        source,
                        first_line + line - 1,
                        message
                    );
                } else {
                    let _ = writeln!(self.stderr_writer, "{}", err);
                }
                let _ = self.stderr_writer.flush();
                UnitOutcome::Failed
            }
        }
    }

    /// Splits `text` into units and runs each one, continuing after errors until the end of
    /// the text or `quit`.
    pub fn run_source(&mut self, text: &str, source: &str) -> RunSummary {
        let mut summary = RunSummary::default();
        let mut acc = UnitAccumulator::new();
        let units = text
            .split_inclusive('\n')
            .filter_map(|line| acc.push_line(line))
            .collect::<alloc::vec::Vec<_>>();
        for (unit, line) in units.into_iter().chain(acc.finish()) {
            match self.run_unit(&unit, source, line) {
                UnitOutcome::Completed => {}
                UnitOutcome::Failed => summary.errors += 1,
                UnitOutcome::Quit => {
                    summary.quit = true;
                    break;
                }
            }
        }
        summary
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::boxed::Box;
    use alloc::rc::Rc;
    use alloc::string::ToString;
    use core::cell::RefCell;
    use core::fmt;

    #[derive(Clone, Default)]
    struct Shared(Rc<RefCell<String>>);

    // SAFETY: test-only writer used from a single thread.
    unsafe impl Send for Shared {}

    impl fmt::Write for Shared {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            self.0.borrow_mut().push_str(s);
            Ok(())
        }
    }

    impl crate::eval::BcWriter for Shared {}

    fn run(text: &str) -> (RunSummary, String, String) {
        let out = Shared::default();
        let err = Shared::default();
        let mut ev = Evaluator::new(false, Box::new(out.clone()), Box::new(err.clone()));
        let summary = ev.run_source(text, STDIN_SOURCE);
        let out = out.0.borrow().clone();
        let err = err.0.borrow().clone();
        (summary, out, err)
    }

    #[test]
    fn accumulator_groups_continuations_and_blocks() {
        let mut acc = UnitAccumulator::new();
        assert!(!acc.is_pending());
        assert_eq!(acc.push_line("1 + \\\n"), None);
        assert_eq!(acc.push_line("2\n"), Some(("1 + \\\n2\n".to_string(), 1)));
        assert_eq!(acc.push_line("{\n"), None);
        assert!(acc.is_pending());
        assert_eq!(acc.push_line("3\n"), None);
        assert_eq!(acc.push_line("}\n"), Some(("{\n3\n}\n".to_string(), 3)));
        assert!(!acc.is_pending());
        assert_eq!(acc.push_line("4"), Some(("4".to_string(), 6)));
        assert_eq!(acc.finish(), None);

        assert_eq!(acc.push_line("/* open\n"), None);
        acc.clear();
        assert_eq!(acc.finish(), None);
    }

    #[test]
    fn register_getters_reflect_assignments() {
        let mut ev = Evaluator::new(
            false,
            Box::new(Shared::default()),
            Box::new(Shared::default()),
        );
        assert_eq!((ev.scale(), ev.ibase(), ev.obase()), (0, 10, 10));
        ev.run_source("scale = 5; obase = 8; ibase = 3\n", STDIN_SOURCE);
        assert_eq!((ev.scale(), ev.ibase(), ev.obase()), (5, 3, 8));
        ev.set_scale(usize::MAX);
        assert_eq!(ev.scale(), crate::verified_kernels::BC_SCALE_MAX);
    }

    #[test]
    fn errors_discard_only_the_rest_of_their_unit() {
        let (summary, out, err) = run("1/0; 5\n7\n");
        assert_eq!(
            summary,
            RunSummary {
                errors: 1,
                quit: false
            }
        );
        assert_eq!(out, "7\n");
        assert_eq!(err, "Runtime error (func=(main)): Divide by zero\n");
    }

    #[test]
    fn syntax_errors_report_the_line_within_the_source() {
        let (summary, out, err) = run("1\n2\n3 +\n4\n");
        assert_eq!(summary.errors, 1);
        assert_eq!(out, "1\n2\n4\n");
        assert_eq!(err, "(standard_in) 4: syntax error\n");
    }

    #[test]
    fn incomplete_unit_at_end_of_input_is_reported() {
        let (summary, out, err) = run("1\n{ 2\n");
        assert_eq!(summary.errors, 1);
        assert_eq!(out, "1\n");
        assert_eq!(err, "(standard_in) 3: syntax error\n");
    }

    #[test]
    fn runtime_errors_name_the_innermost_function() {
        let (_, _, err) = run("define g() { return (1/0) }\ndefine f() { return (g()) }\nf()\n");
        assert_eq!(err, "Runtime error (func=g): Divide by zero\n");
    }

    #[test]
    fn quit_stops_processing_without_running_its_unit() {
        let (summary, out, err) = run("1\n2; quit\n3\n");
        assert_eq!(
            summary,
            RunSummary {
                errors: 0,
                quit: true
            }
        );
        assert_eq!(out, "1\n");
        assert_eq!(err, "");
    }
}
