// SPDX-License-Identifier: MIT

//! Input-unit driver shared by every front end (CLI, C API, Zephyr, bare metal, Wasm).
//!
//! Implements `docs/COMPATIBILITY.md` §3.1–3.2: input is split into *units* (one line, or one
//! complete multi-line construct). Each unit is parsed and executed on its own; an error is
//! reported and discards only the rest of its unit, and `quit` stops processing.

use alloc::string::String;
use alloc::vec::Vec;

use crate::error::BcError;
#[cfg(verus_keep_ghost)]
use crate::error::RuntimeError;
use crate::eval::Evaluator;
#[cfg(verus_keep_ghost)]
use crate::eval::{err_log, lemma_inv_frame, out_col, out_log, r_state, r_unit, same_but_err};
use crate::format::push_dec;
use crate::parser::{ExtensionPolicy, Lexer, Parser, Stmt};
#[cfg(verus_keep_ghost)]
use crate::refine::{r_err, r_stmts, text_view};
use crate::verified_kernels::{verified_repl_block_scan, verified_unit_within_limit};
#[cfg(verus_keep_ghost)]
use bc_spec::eval::{EState, with_call, with_depth, with_err, with_flags};
#[cfg(verus_keep_ghost)]
use bc_spec::fuel::done;
#[cfg(verus_keep_ghost)]
use bc_spec::lexer::{Unit, tokenize};
#[cfg(verus_keep_ghost)]
use bc_spec::parser::{ExtUse, PCfg, PR, parse_unit};
#[cfg(verus_keep_ghost)]
use bc_spec::top::{Options, RunState, at_line, ext_diags, run_parsed_unit};
#[cfg(not(verus_keep_ghost))]
use verus_builtin::Ghost;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::string::StringSliceAdditionalSpecFns;

/// Source name used in syntax diagnostics for standard input, as in GNU bc.
pub const STDIN_SOURCE: &str = "(standard_in)";

/// Diagnostic for an input unit longer than `BC_UNIT_MAX` (`docs/COMPATIBILITY.md` §2).
pub const UNIT_TOO_LONG: &str = "input unit too long";

verus! {

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

#[cfg(verus_keep_ghost)]
type SpecOptions = Options;
#[cfg(not(verus_keep_ghost))]
type SpecOptions = ();
#[cfg(verus_keep_ghost)]
type SpecRun = RunState;
#[cfg(not(verus_keep_ghost))]
type SpecRun = ();
#[cfg(verus_keep_ghost)]
type SpecUnit = Unit;
#[cfg(not(verus_keep_ghost))]
type SpecUnit = ();
#[cfg(verus_keep_ghost)]
type SpecExt = Seq<ExtUse>;
#[cfg(not(verus_keep_ghost))]
type SpecExt = ();

/// The evaluator between units corresponds to the specification's state `st`: once both reset
/// the depth and the invocation `ibase` (as `run_unit` does), `r_state` holds.
pub(crate) open spec fn r_top(e: Evaluator, st: EState) -> bool {
    r_state(Evaluator { eval_depth: 0, invocation_ibase: None, ..e }, with_call(with_depth(st, 0), st.calls, false, st.inv_ibase))
}

/// The options of the specification are the evaluator's extension policy and nesting limit.
pub(crate) open spec fn r_opts(e: Evaluator, opts: Options) -> bool {
    &&& opts.reject_extensions == (e.extension_policy == ExtensionPolicy::Reject)
    &&& opts.warn_extensions == (e.extension_policy == ExtensionPolicy::Warn)
    &&& opts.max_depth == e.max_depth as u64
}

/// The parser configuration of the specification's `run_unit`.
pub(crate) open spec fn unit_cfg(opts: Options) -> PCfg {
    PCfg { record_extensions: opts.reject_extensions || opts.warn_extensions, max_depth: opts.max_depth }
}

/// The extension uses the parser recorded: line within the unit and description.
pub(crate) open spec fn r_ext(ext: Seq<(usize, String)>, sext: Seq<ExtUse>) -> bool {
    ext.len() == sext.len() && forall|i: int| 0 <= i < ext.len() ==> sext[i].line == (#[trigger] ext[i]).0 as u64
        && sext[i].desc == text_view(ext[i].1)
}

/// What `run_unit` assumes of the parser (the parser is not proved): the statements, or the
/// error, and the extension uses correspond to the specification's `parse_unit`.
pub(crate) open spec fn r_parsed(parsed: Result<Vec<Stmt>, BcError>, ext: Seq<(usize, String)>, p: PR) -> bool {
    &&& r_ext(ext, p.st.ext)
    &&& match parsed {
        Ok(stmts) => p.ok && r_stmts(stmts@, p.st.nodes, p.list),
        Err(BcError::Quit) => !p.ok && p.err.quit,
        Err(BcError::Syntax { line, message, .. }) => !p.ok && !p.err.quit && p.err.line == line as u64
            && p.err.msg == text_view(message),
        Err(BcError::Runtime { .. }) => false,
    }
}

/// The outcome of a unit corresponds to the specification's step from `rs` to `rs2`, unless the
/// specification leaves its model there (it ran out of fuel).
pub(crate) open spec fn r_outcome(r: UnitOutcome, e: Evaluator, rs: RunState, rs2: RunState) -> bool {
    !rs2.not_modeled ==> r_top(e, rs2.st) && !rs2.not_modeled && match r {
        UnitOutcome::Completed => !rs2.quit && rs2.errors == rs.errors,
        UnitOutcome::Failed => !rs2.quit && rs2.errors == bc_spec::top::failed(rs, rs2.st).errors,
        UnitOutcome::Quit => rs2.quit,
    }
}

/// `r_top` ignores the depth and the invocation `ibase`.
proof fn lemma_r_top(e: Evaluator, st: EState, d: u64)
    requires
        r_state(e, with_depth(st, d)),
    ensures
        r_top(e, st),
{
}

impl Evaluator {
    /// Flushes standard output.
    fn flush_stdout(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            *final(self) == (Evaluator { stdout_writer: final(self).stdout_writer, ..*old(self) }),
            out_log(&final(self).stdout_writer) == out_log(&old(self).stdout_writer),
            out_col(&final(self).stdout_writer) == out_col(&old(self).stdout_writer),
    {
        let ghost e0 = *self;
        self.stdout_writer.flush_out();
        proof {
            lemma_inv_frame(e0, *self);
        }
    }

    /// Flushes the diagnostic stream.
    fn flush_stderr(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            same_but_err(*old(self), *final(self)),
            err_log(&final(self).stderr_writer) == err_log(&old(self).stderr_writer),
    {
        let ghost e0 = *self;
        self.stderr_writer.flush_err();
        proof {
            lemma_inv_frame(e0, *self);
        }
    }

    /// Clears a pending `break` or `return` after an error.
    fn clear_flags(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            *final(self) == (Evaluator { break_flag: false, return_flag: false, ..*old(self) }),
    {
        let ghost e0 = *self;
        self.break_flag = false;
        self.return_flag = false;
        proof {
            lemma_inv_frame(e0, *self);
        }
    }

    /// Writes `<source> <line>: ` for line `line` of a unit that starts at line `first` (the
    /// specification's `at_line`).
    fn write_at_line(&mut self, source: &str, first: usize, line: usize)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            same_but_err(*old(self), *final(self)),
            err_log(&final(self).stderr_writer) == err_log(&old(self).stderr_writer).add(at_line(source.spec_bytes(), first as u64, line as u64)),
    {
        let ghost log0 = err_log(&self.stderr_writer);
        let ghost e0 = *self;
        self.stderr_writer.write_bytes(source.as_bytes());
        let sp: [u8; 1] = [32];
        self.stderr_writer.write_bytes(&sp);
        let f = first as u64;
        let l = line as u64;
        let n = if l >= 1 && f <= 0xffff_ffff && l <= 0xffff_ffff { f + l - 1 } else { f };
        let mut digits = Vec::new();
        push_dec(&mut digits, n);
        self.stderr_writer.write_bytes(digits.as_slice());
        let sep: [u8; 2] = [58, 32];
        self.stderr_writer.write_bytes(&sep);
        proof {
            assert(sp@ =~= seq![32u8]);
            assert(sep@ =~= seq![58u8, 32]);
            assert(err_log(&self.stderr_writer) =~= log0.add(at_line(source.spec_bytes(), first as u64, line as u64)));
            lemma_inv_frame(e0, *self);
        }
    }

    /// Writes the `-w` / `-s` diagnostics of the extension uses `ext` (the specification's
    /// `ext_diags`), with GNU bc's prefixes.
    #[allow(clippy::ptr_arg, reason = "the specification relates the list to the unit")]
    #[allow(clippy::redundant_as_str, reason = "Verus specifies str::as_bytes and String::as_str, not String::as_bytes")]
    fn write_ext_diags(&mut self, ext: &Vec<(usize, String)>, source: &str, first: usize, reject: bool, Ghost(sext): Ghost<SpecExt>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            same_but_err(*old(self), *final(self)),
            r_ext(ext@, sext) ==> err_log(&final(self).stderr_writer)
                == err_log(&old(self).stderr_writer).add(ext_diags(sext, source.spec_bytes(), first as u64, reject)),
    {
        let ghost log0 = err_log(&self.stderr_writer);
        let ghost hyp = r_ext(ext@, sext);
        let ghost src = source.spec_bytes();
        let error: [u8; 7] = [69, 114, 114, 111, 114, 58, 32];
        let warning: [u8; 10] = [40, 87, 97, 114, 110, 105, 110, 103, 41, 32];
        let nl: [u8; 1] = [10];
        let mut i: usize = 0;
        proof {
            if hyp {
                assert(sext.skip(0) =~= sext);
                assert(log0.add(ext_diags(sext, src, first as u64, reject)) =~= log0.add(ext_diags(sext.skip(0), src, first as u64, reject)));
            }
        }
        while i < ext.len()
            invariant
                self.inv(),
                same_but_err(*old(self), *self),
                i <= ext.len(),
                hyp == r_ext(ext@, sext),
                src == source.spec_bytes(),
                error@ == seq![69u8, 114, 114, 111, 114, 58, 32],
                warning@ == seq![40u8, 87, 97, 114, 110, 105, 110, 103, 41, 32],
                nl@ == seq![10u8],
                hyp ==> log0.add(ext_diags(sext, src, first as u64, reject))
                    == err_log(&self.stderr_writer).add(ext_diags(sext.skip(i as int), src, first as u64, reject)),
            decreases ext.len() - i,
        {
            let ghost log1 = err_log(&self.stderr_writer);
            let ghost e1 = *self;
            let (line, desc) = &ext[i];
            self.write_at_line(source, first, *line);
            if reject {
                self.stderr_writer.write_bytes(&error);
            } else {
                self.stderr_writer.write_bytes(&warning);
            }
            self.stderr_writer.write_bytes(desc.as_str().as_bytes());
            self.stderr_writer.write_bytes(&nl);
            proof {
                if hyp {
                    let rest = sext.skip(i as int);
                    assert(rest[0] == sext[i as int]);
                    assert(rest.drop_first() =~= sext.skip(i as int + 1));
                    assert(sext[i as int].line == *line as u64 && sext[i as int].desc == text_view(*desc));
                    let prefix = if reject { seq![69u8, 114, 114, 111, 114, 58, 32] } else { seq![40u8, 87, 97, 114, 110, 105, 110, 103, 41, 32] };
                    let one = at_line(src, first as u64, rest[0].line).add(prefix).add(rest[0].desc).push(10u8);
                    assert(ext_diags(rest, src, first as u64, reject) == one.add(ext_diags(rest.drop_first(), src, first as u64, reject)));
                    assert(err_log(&self.stderr_writer) =~= log1.add(one));
                    assert(log1.add(one).add(ext_diags(sext.skip(i as int + 1), src, first as u64, reject))
                        =~= log1.add(one.add(ext_diags(sext.skip(i as int + 1), src, first as u64, reject))));
                }
            }
            proof {
                lemma_inv_frame(e1, *self);
            }
            i += 1;
        }
        proof {
            if hyp {
                assert(sext.skip(i as int) =~= Seq::<ExtUse>::empty());
                assert(err_log(&self.stderr_writer).add(Seq::<u8>::empty()) =~= err_log(&self.stderr_writer));
            }
        }
    }

    /// Writes the diagnostic `<source> <line>: <message>` of a syntax error.
    #[allow(clippy::ptr_arg, reason = "the specification relates the message to the String")]
    #[allow(clippy::redundant_as_str, reason = "Verus specifies str::as_bytes and String::as_str, not String::as_bytes")]
    fn write_syntax_diag(&mut self, source: &str, first: usize, line: usize, message: &String)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            same_but_err(*old(self), *final(self)),
            err_log(&final(self).stderr_writer) == err_log(&old(self).stderr_writer)
                .add(at_line(source.spec_bytes(), first as u64, line as u64)).add(text_view(*message)).push(10u8),
    {
        let ghost log0 = err_log(&self.stderr_writer);
        self.write_at_line(source, first, line);
        self.stderr_writer.write_bytes(message.as_str().as_bytes());
        let nl: [u8; 1] = [10];
        self.stderr_writer.write_bytes(&nl);
        proof {
            assert(nl@ =~= seq![10u8]);
            assert(err_log(&self.stderr_writer) =~= log0.add(at_line(source.spec_bytes(), first as u64, line as u64)).add(text_view(*message)).push(10u8));
            lemma_inv_frame(*old(self), *self);
        }
    }

    /// The part of `run_unit` after parsing (the specification's `run_unit` after
    /// `parse_unit`): the `-w` / `-s` diagnostics, the statements, and the diagnostic of an
    /// error. Its postcondition is the refinement theorem of a unit, relative to the parser's
    /// correspondence `r_parsed`.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(50)]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn run_parsed(&mut self, parsed: Result<Vec<Stmt>, BcError>, ext: &Vec<(usize, String)>, source: &str, first_line: usize, Ghost(opts): Ghost<SpecOptions>, Ghost(rs): Ghost<SpecRun>, Ghost(u): Ghost<SpecUnit>) -> (r: UnitOutcome)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            (r_top(*old(self), rs.st) && r_opts(*old(self), opts) && u.line == first_line as u64
                && r_parsed(parsed, ext@, parse_unit(tokenize(u.text), unit_cfg(opts))))
                ==> r_outcome(r, *final(self), rs, run_parsed_unit(opts, rs, source.spec_bytes(), u)),
    {
        let ghost hyp = r_top(*self, rs.st) && r_opts(*self, opts) && u.line == first_line as u64
            && r_parsed(parsed, ext@, parse_unit(tokenize(u.text), unit_cfg(opts)));
        let ghost p = parse_unit(tokenize(u.text), unit_cfg(opts));
        let ghost src = source.spec_bytes();
        let ghost rs2 = run_parsed_unit(opts, rs, src, u);
        let ghost st0 = with_call(with_depth(rs.st, 0), rs.st.calls, false, rs.st.inv_ibase);
        let ghost e_old = *self;
        // A unit starts at the top level; this also recovers if a front end caught a panic in
        // the middle of the previous unit.
        self.eval_depth = 0;
        self.invocation_ibase = None;
        proof {
            lemma_inv_frame(e_old, *self);
            if hyp {
                assert(*self == (Evaluator { eval_depth: 0, invocation_ibase: None, ..e_old }));
                assert(r_state(*self, st0));
            }
        }
        let reject = matches!(self.extension_policy, ExtensionPolicy::Reject);
        self.write_ext_diags(ext, source, first_line, reject, Ghost(p.st.ext));
        let ghost st1 = with_err(st0, st0.err.add(ext_diags(p.st.ext, src, u.line, reject)));
        proof {
            if hyp {
                assert(r_state(*self, st1));
            }
        }
        if reject && !ext.is_empty() && parsed.is_ok() {
            self.flush_stderr();
            proof {
                if hyp {
                    lemma_r_top(*self, st1, 0);
                }
            }
            return UnitOutcome::Failed;
        }
        match parsed {
            Ok(stmts) => {
                let ghost e1 = *self;
                let r = self.exec_items_ref(&stmts, Ghost(p.st.nodes), Ghost(p.list), Ghost(st1));
                let ghost e_run = *self;
                self.flush_stdout();
                let ghost x = bc_spec::top::exec_items(p.st.nodes, p.list, st1, 0x4000_0000_0000_0000u64);
                match r {
                    Ok(()) => {
                        proof {
                            if hyp && !rs2.not_modeled {
                                assert(!p.err.out_of_fuel && p.ok);
                                assert(done(x));
                                assert(r_state(e1, st1));
                                assert(r_unit(r, e_run, x, 0));
                                lemma_r_top(*self, x.st, x.st.depth);
                            }
                        }
                        UnitOutcome::Completed
                    },
                    Err(BcError::Runtime { kind, func }) => {
                        self.clear_flags();
                        let ghost e2 = *self;
                        self.write_runtime_diag(&kind, &func);
                        self.flush_stderr();
                        proof {
                            if hyp && !rs2.not_modeled {
                                assert(!p.err.out_of_fuel && p.ok);
                                assert(done(x));
                                assert(r_state(e1, st1));
                                assert(r_unit(Err(BcError::Runtime { kind, func }), e_run, x, 0));
                                assert(r_err(BcError::Runtime { kind, func }, x.err));
                                let st2 = with_flags(x.st, false, false, x.st.ret_val);
                                assert(r_state(e2, with_depth(st2, 0)));
                                lemma_r_top(*self, with_err(st2, st2.err.add(bc_spec::top::runtime_diag(x.err))), 0);
                            }
                        }
                        UnitOutcome::Failed
                    },
                    Err(BcError::Quit) => UnitOutcome::Quit,
                    Err(BcError::Syntax { line, message, .. }) => {
                        // Not produced by execution.
                        self.write_syntax_diag(source, first_line, line, &message);
                        self.flush_stderr();
                        UnitOutcome::Failed
                    },
                }
            },
            Err(BcError::Quit) => {
                self.flush_stdout();
                proof {
                    if hyp {
                        lemma_r_top(*self, st1, 0);
                    }
                }
                UnitOutcome::Quit
            },
            Err(BcError::Syntax { line, message, .. }) => {
                self.flush_stdout();
                self.write_syntax_diag(source, first_line, line, &message);
                self.flush_stderr();
                proof {
                    if hyp {
                        lemma_r_top(*self, with_err(st1, st1.err.add(at_line(src, u.line, p.err.line)).add(p.err.msg).push(10u8)), 0);
                    }
                }
                UnitOutcome::Failed
            },
            Err(BcError::Runtime { kind, func }) => {
                // Not produced by the parser.
                self.flush_stdout();
                self.clear_flags();
                self.write_runtime_diag(&kind, &func);
                self.flush_stderr();
                UnitOutcome::Failed
            },
        }
    }
}

} // verus!

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
/// open brace, comment, or string (see `verified_repl_block_completeness`), or when it is longer
/// than `BC_UNIT_MAX`. Lines are bytes and need not be UTF-8.
#[derive(Debug, Clone, Default)]
pub struct UnitAccumulator {
    buf: Vec<u8>,
    start_line: usize,
    next_line: usize,
    /// `buf[..scanned]` is whole lines, already scanned to the state `scan`. A step of the scan
    /// looks ahead only within a line, so scanning can resume there and the result is that of
    /// scanning all of `buf`.
    scanned: usize,
    scan: (i32, bool, bool),
}

impl UnitAccumulator {
    /// Creates an empty accumulator whose first line is line 1.
    pub fn new() -> Self {
        Self {
            buf: Vec::new(),
            start_line: 1,
            next_line: 1,
            scanned: 0,
            scan: (0, false, false),
        }
    }

    /// Appends one line (with its trailing newline, if any). Returns the completed unit and the
    /// line number of its first line when the accumulated text forms a complete unit.
    pub fn push_line(&mut self, line: &[u8]) -> Option<(Vec<u8>, usize)> {
        if self.buf.is_empty() {
            self.start_line = self.next_line;
        }
        self.buf.extend_from_slice(line);
        if line.ends_with(b"\n") {
            self.next_line += 1;
        }
        // Text beyond the limit is passed on as it is, and `run_unit` rejects it.
        if verified_unit_within_limit(self.buf.len()) {
            if self.buf.ends_with(b"\\\n") || self.buf.ends_with(b"\\\r\n") {
                return None;
            }
            let scan = verified_repl_block_scan(&self.buf, self.scanned, self.scan);
            if scan.0 > 0 || scan.1 || scan.2 {
                if line.ends_with(b"\n") {
                    self.scanned = self.buf.len();
                    self.scan = scan;
                }
                return None;
            }
        }
        self.take()
    }

    /// Returns the incomplete text left at end of input, if any, so that it can be reported.
    pub fn finish(&mut self) -> Option<(Vec<u8>, usize)> {
        self.take()
    }

    /// Whether lines of an incomplete unit are waiting for more input (e.g. an open `{`).
    pub fn is_pending(&self) -> bool {
        !self.buf.is_empty()
    }

    /// Discards any partially accumulated unit (used after an interrupt).
    pub fn clear(&mut self) {
        self.buf.clear();
        self.reset_scan();
    }

    fn reset_scan(&mut self) {
        self.scanned = 0;
        self.scan = (0, false, false);
    }

    fn take(&mut self) -> Option<(Vec<u8>, usize)> {
        self.reset_scan();
        if self.buf.is_empty() {
            None
        } else {
            Some((core::mem::take(&mut self.buf), self.start_line))
        }
    }
}

verus! {

impl Evaluator {
    /// Parses and executes one input unit, reporting any error to `stderr_writer`.
    ///
    /// `source` names the input in syntax diagnostics (a file name, or [`STDIN_SOURCE`]) and
    /// `first_line` is the line number of the unit's first line within that source.
    ///
    /// Trusted glue: it only runs the parser (not verified) and passes its
    /// result to the verified `run_parsed`.
    #[verifier::external_body]
    pub fn run_unit(&mut self, unit: &[u8], source: &str, first_line: usize) -> UnitOutcome {
        if !verified_unit_within_limit(unit.len()) {
            let too_long = Err(BcError::Syntax { line: 1, message: String::from(UNIT_TOO_LONG) });
            return self.run_parsed(too_long, &Vec::new(), source, first_line, Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()));
        }
        let policy = self.extension_policy;
        let max_depth = self.max_depth;
        let mut extension_uses = Vec::new();
        let parsed = Parser::try_new(Lexer::new(unit)).and_then(|mut parser| {
            parser.set_extension_policy(policy);
            parser.set_max_depth(max_depth);
            let stmts = parser.try_parse_program();
            extension_uses = parser.take_extension_uses();
            stmts
        });

        self.run_parsed(parsed, &extension_uses, source, first_line, Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }

}

} // verus!

impl Evaluator {
    /// Splits `text` into units and runs each one, continuing after errors until the end of
    /// the text or `quit`. `text` is bytes and need not be UTF-8.
    pub fn run_source(&mut self, text: &[u8], source: &str) -> RunSummary {
        let mut summary = RunSummary::default();
        let mut acc = UnitAccumulator::new();
        let units = text
            .split_inclusive(|&b| b == b'\n')
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
    use crate::parser::DEFAULT_MAX_DEPTH;
    use alloc::boxed::Box;
    use alloc::rc::Rc;
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
        let summary = ev.run_source(text.as_bytes(), STDIN_SOURCE);
        let out = out.0.borrow().clone();
        let err = err.0.borrow().clone();
        (summary, out, err)
    }

    #[cfg(all(not(miri), target_pointer_width = "64"))]
    #[test]
    fn unit_beyond_the_limit_is_rejected_without_being_scanned() {
        use crate::verified_kernels::BC_UNIT_MAX;
        // An open brace and a final continuation would both keep the unit waiting, but the text
        // is over the limit. The rest of these bytes are NUL, illegal characters if ever lexed.
        let mut line = alloc::vec![0u8; BC_UNIT_MAX + 1];
        line[0] = b'{';
        line[BC_UNIT_MAX - 1] = b'\\';
        line[BC_UNIT_MAX] = b'\n';
        let mut acc = UnitAccumulator::new();
        let (unit, first_line) = acc.push_line(&line).expect("a complete unit");
        assert_eq!((unit.len(), first_line), (BC_UNIT_MAX + 1, 1));
        assert!(!acc.is_pending());

        let out = Shared::default();
        let err = Shared::default();
        let mut ev = Evaluator::new(false, Box::new(out.clone()), Box::new(err.clone()));
        assert_eq!(ev.run_unit(&unit, STDIN_SOURCE, 7), UnitOutcome::Failed);
        assert_eq!(out.0.borrow().as_str(), "");
        assert_eq!(
            err.0.borrow().as_str(),
            "(standard_in) 7: input unit too long\n"
        );
    }

    #[test]
    fn nesting_beyond_max_depth_is_an_error_not_an_overflow() {
        let rep = |s: &str, n: usize| s.repeat(n);
        let max = DEFAULT_MAX_DEPTH;
        // Each statement nests 3 levels before its expression (statement, expression, operand)
        // and a call nests 2 more, so these are the largest inputs within the limit.
        let max_parens = max - 3;
        let max_calls = max / 2 - 3;
        let recursion = |n: usize| {
            alloc::format!(
                "define f(n) {{\nif (n == 0) return (0)\nreturn (f(n - 1))\n}}\nf({n})\n"
            )
        };
        let cases = [
            (
                alloc::format!("{}1{}\n", rep("(", max_parens), rep(")", max_parens)),
                "1\n",
                "",
            ),
            (
                alloc::format!(
                    "{}1{}\n",
                    rep("(", max_parens + 1),
                    rep(")", max_parens + 1)
                ),
                "",
                "(standard_in) 1: nesting too deep\n",
            ),
            // A left-associative chain grows the tree without recursion in the parser.
            (
                alloc::format!("1{}\n", rep("+1", max_parens)),
                &alloc::format!("{}\n", max_parens + 1),
                "",
            ),
            (
                alloc::format!("1{}\n", rep("+1", max_parens + 1)),
                "",
                "(standard_in) 1: nesting too deep\n",
            ),
            (
                alloc::format!("{}1{}\n", rep("{", max_parens), rep("}", max_parens)),
                "1\n",
                "",
            ),
            (
                alloc::format!("{}1\n", rep("if (1) ", max_parens + 1)),
                "",
                "(standard_in) 1: nesting too deep\n",
            ),
            (recursion(max_calls), "0\n", ""),
            (
                recursion(max_calls + 1),
                "",
                "Runtime error (func=f): nesting too deep\n",
            ),
        ];
        for (text, out, err) in &cases {
            let (summary, actual_out, actual_err) = run(text);
            assert_eq!(
                (actual_out.as_str(), actual_err.as_str()),
                (*out, *err),
                "{text}"
            );
            assert_eq!(summary.errors, usize::from(!err.is_empty()));
        }

        // After an error the next unit starts at depth 0 again.
        let (_, out, _) = run(&alloc::format!("{}\n2\n", recursion(max_calls + 1)));
        assert_eq!(out, "2\n");
    }

    #[test]
    fn accumulator_groups_continuations_and_blocks() {
        let mut acc = UnitAccumulator::new();
        assert!(!acc.is_pending());
        assert_eq!(acc.push_line(b"1 + \\\n"), None);
        assert_eq!(
            acc.push_line(b"2\n"),
            Some(("1 + \\\n2\n".as_bytes().to_vec(), 1))
        );
        assert_eq!(acc.push_line(b"{\n"), None);
        assert!(acc.is_pending());
        assert_eq!(acc.push_line(b"3\n"), None);
        assert_eq!(
            acc.push_line(b"}\n"),
            Some(("{\n3\n}\n".as_bytes().to_vec(), 3))
        );
        assert!(!acc.is_pending());
        assert_eq!(acc.push_line(b"4"), Some(("4".as_bytes().to_vec(), 6)));
        assert_eq!(acc.finish(), None);

        assert_eq!(acc.push_line(b"/* open\n"), None);
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
        ev.run_source(b"scale = 5; obase = 8; ibase = 3\n", STDIN_SOURCE);
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
