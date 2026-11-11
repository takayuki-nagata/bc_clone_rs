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
use crate::parser::{Code, ExtensionPolicy, ascii_string, parse_unit_ref};
#[cfg(verus_keep_ghost)]
use crate::refine::{r_code, r_err, text_view};
use crate::verified_kernels::{verified_repl_block_scan, verified_unit_within_limit};
use alloc::rc::Rc;
#[cfg(verus_keep_ghost)]
use bc_spec::eval::{EState, bytes_add, with_call, with_depth, with_err, with_flags};
#[cfg(verus_keep_ghost)]
use bc_spec::fuel::done;
#[cfg(verus_keep_ghost)]
use bc_spec::lexer::{
    BlockScan, Unit, block_scan, split_units, split_units_from, take_line, tokenize, unit_pending,
};
#[cfg(verus_keep_ghost)]
use bc_spec::lexer_lemmas::lemma_block_scan_split;
#[cfg(verus_keep_ghost)]
use bc_spec::parser::{ExtUse, PCfg, PErr, PR, PState, parse_unit, pr_err};
#[cfg(verus_keep_ghost)]
use bc_spec::top::{
    Input, Options, RunState, at_line, ext_diags, initial, run, run_inputs, run_parse_result,
    run_parsed_unit, run_unit as spec_run_unit, run_units, unit_too_long_msg,
};
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

/// The diagnostic `input unit too long`.
fn unit_too_long_text() -> (r: String)
    ensures
        text_view(r) == unit_too_long_msg(),
{
    let m = [105u8, 110, 112, 117, 116, 32, 117, 110, 105, 116, 32, 116, 111, 111, 32, 108, 111, 110, 103];
    proof { assert(m@ =~= unit_too_long_msg()); }
    ascii_string(m.as_slice())
}

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
type SpecParse = PR;
#[cfg(not(verus_keep_ghost))]
type SpecParse = ();
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
    &&& r_settings(e.extension_policy, e.max_depth, opts)
    &&& opts.max_eval_depth == e.max_eval_depth as u64
}

/// The options of the specification are this extension policy and nesting limit.
pub(crate) open spec fn r_settings(policy: ExtensionPolicy, max_depth: usize, opts: Options) -> bool {
    &&& opts.reject_extensions == (policy == ExtensionPolicy::Reject)
    &&& opts.warn_extensions == (policy == ExtensionPolicy::Warn)
    &&& opts.max_depth == max_depth as u64
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

/// The statements, or the error, and the extension uses correspond to the specification's
/// result `p` of parsing the unit.
pub(crate) open spec fn r_parsed(parsed: Result<Vec<usize>, BcError>, ext: Seq<(usize, String)>, code: Code, p: PR) -> bool {
    &&& r_ext(ext, p.st.ext)
    &&& match parsed {
        Ok(stmts) => p.ok && r_code(code, p.st.nodes.s) && stmts@ == p.list,
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
        UnitOutcome::Quit => rs2.quit && rs2.errors == rs.errors,
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
    /// error. Its postcondition is the refinement theorem of a unit given the result `p` of
    /// parsing it (`r_parsed`, which `parse_unit_ref` establishes).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(50)]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn run_parsed(&mut self, parsed: Result<Vec<usize>, BcError>, ext: &Vec<(usize, String)>, code: Code, source: &str, first_line: usize, policy: ExtensionPolicy, Ghost(opts): Ghost<SpecOptions>, Ghost(rs): Ghost<SpecRun>, Ghost(p): Ghost<SpecParse>) -> (r: UnitOutcome)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            (r_top(*old(self), rs.st) && opts.reject_extensions == (policy == ExtensionPolicy::Reject) && r_parsed(parsed, ext@, code, p))
                ==> r_outcome(r, *final(self), rs, run_parse_result(opts, rs, source.spec_bytes(), first_line as u64, p)),
    {
        let ghost hyp = r_top(*self, rs.st) && opts.reject_extensions == (policy == ExtensionPolicy::Reject) && r_parsed(parsed, ext@, code, p);
        let ghost first = first_line as u64;
        let ghost src = source.spec_bytes();
        let ghost rs2 = run_parse_result(opts, rs, src, first, p);
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
        let reject = matches!(policy, ExtensionPolicy::Reject);
        self.write_ext_diags(ext, source, first_line, reject, Ghost(p.st.ext));
        let ghost st1 = with_err(st0, bytes_add(st0.err, ext_diags(p.st.ext, src, first, reject)));
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
                let code = Rc::new(code);
                let r = self.exec_items_ref(&code, &stmts, Ghost(p.st.nodes.s), Ghost(p.list), Ghost(st1));
                let ghost e_run = *self;
                self.flush_stdout();
                let ghost x = bc_spec::top::exec_items(p.st.nodes.s, p.list, st1, 0x4000_0000_0000_0000u64);
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
                                lemma_r_top(*self, with_err(st2, bytes_add(st2.err, bc_spec::top::runtime_diag(x.err))), 0);
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
                        lemma_r_top(*self, with_err(st1, bc_spec::eval::bytes_push(bytes_add(bytes_add(st1.err, at_line(src, first, p.err.line)), p.err.msg), 10u8)), 0);
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

verus! {

impl Evaluator {
    /// Parses and executes one input unit, reporting any error to `stderr_writer`.
    ///
    /// `source` names the input in syntax diagnostics (a file name, or [`STDIN_SOURCE`]) and
    /// `first_line` is the line number of the unit's first line within that source.
    #[verifier::external_body]
    pub fn run_unit(&mut self, unit: &[u8], source: &str, first_line: usize) -> UnitOutcome {
        let policy = self.extension_policy;
        let max_depth = self.max_depth;
        self.run_unit_ref(unit, source, first_line, policy, max_depth, Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }

    /// `run_unit`: the refinement theorem of one unit, against the specification's `run_unit`.
    /// A nesting limit that leaves no room to count is not a limit at all, and is lowered to one
    /// that is still out of reach.
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    pub(crate) fn run_unit_ref(&mut self, unit: &[u8], source: &str, first_line: usize, policy: ExtensionPolicy, limit: usize, Ghost(opts): Ghost<SpecOptions>, Ghost(rs): Ghost<SpecRun>, Ghost(u): Ghost<SpecUnit>) -> (r: UnitOutcome)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            (r_top(*old(self), rs.st) && r_settings(policy, limit, opts) && u.line == first_line as u64 && u.text == unit@
                && limit < usize::MAX - 2)
                ==> r_outcome(r, *final(self), rs, spec_run_unit(opts, rs, source.spec_bytes(), u)),
    {
        if !verified_unit_within_limit(unit.len()) {
            let ghost e0 = PState { cur: 0usize, depth: 0u64, last_line: 1u64, loop_depth: 0u64, in_function: false, ext: seq![], nodes: bc_spec::eval::arena_empty() };
            let ghost p = pr_err(e0, PErr { quit: false, out_of_fuel: false, line: 1u64, msg: unit_too_long_msg() });
            let too_long = Err(BcError::Syntax { line: 1, message: unit_too_long_text() });
            let none = Vec::new();
            proof { assert(r_ext(none@, e0.ext)); }
            let r = self.run_parsed(too_long, &none, Code { nodes: Vec::new() }, source, first_line, policy, Ghost(opts), Ghost(rs), Ghost(p));
            proof {
                let st0 = with_call(with_depth(rs.st, 0u64), rs.st.calls, false, rs.st.inv_ibase);
                let src = source.spec_bytes();
                assert(ext_diags(e0.ext, src, first_line as u64, opts.reject_extensions) == Seq::<u8>::empty());
                assert(st0.err.s.add(Seq::<u8>::empty()) =~= st0.err.s);
                assert(bytes_add(st0.err, Seq::<u8>::empty()) == st0.err);
                assert(with_err(st0, st0.err) == st0);
            }
            return r;
        }
        let max_depth = if limit < usize::MAX - 2 { limit } else { usize::MAX - 3 };
        let ghost cfg = PCfg { record_extensions: policy != ExtensionPolicy::Allow, max_depth: max_depth as u64 };
        let (parsed, extension_uses, code) = parse_unit_ref(unit, policy, max_depth, Ghost(cfg));
        let ghost p = parse_unit(tokenize(unit@), cfg);
        self.run_parsed(parsed, &extension_uses, code, source, first_line, policy, Ghost(opts), Ghost(rs), Ghost(p))
    }
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
/// open brace, comment, or string (see `verified_repl_block_completeness`), or when it is longer
/// than `BC_UNIT_MAX`. Lines are bytes and need not be UTF-8.
pub struct UnitAccumulator {
    buf: Vec<u8>,
    start_line: usize,
    next_line: usize,
    /// `buf[..scanned]` is whole lines, already scanned to the state `scan`. A step of the scan
    /// looks ahead only within a line, so scanning can resume there and the result is that of
    /// scanning all of `buf` (`lemma_block_scan_split`).
    scanned: usize,
    scan: (i32, bool, bool),
}

/// The state of a scan from the start of a unit.
pub(crate) open spec fn scan_start() -> BlockScan {
    BlockScan { count: 0i64, in_comment: false, in_string: false }
}

/// The accumulator's state after a line, as in the specification's `split_units_from`.
pub(crate) open spec fn acc_step(old: UnitAccumulator, new: UnitAccumulator, line: Seq<u8>, r: Option<(Vec<u8>, usize)>) -> bool {
    let b2 = old.buf_view().add(line);
    let start2 = if old.buf_view().len() == 0 { old.next_view() } else { old.start_view() };
    let next2 = if line.len() > 0 && line[line.len() - 1] == 10u8 && old.next_view() < 0xffff_ffff_ffff_ffffu64 { (old.next_view() + 1) as u64 } else { old.next_view() };
    &&& new.next_view() == next2
    &&& new.start_view() == start2
    &&& if unit_pending(b2) {
        new.buf_view() == b2 && r is None
    } else {
        new.buf_view().len() == 0 && (r matches Some((text, first)) && text@ == b2 && first as u64 == start2)
    }
}

impl UnitAccumulator {
    pub closed spec fn buf_view(self) -> Seq<u8> {
        self.buf@
    }

    pub closed spec fn start_view(self) -> u64 {
        self.start_line as u64
    }

    pub closed spec fn next_view(self) -> u64 {
        self.next_line as u64
    }

    /// Whether the line count can still grow without saturating.
    pub closed spec fn next_ok(self, n: int) -> bool {
        self.next_line + n < usize::MAX
    }

    /// The scan state is that of the whole lines at the start of the buffer.
    pub closed spec fn inv(self) -> bool {
        &&& self.scanned <= self.buf@.len()
        &&& self.scanned <= 1_000_000_000
        &&& -(self.scanned as int) <= (self.scan.0 as int) && (self.scan.0 as int) <= (self.scanned as int)
        &&& !(self.scan.1 && self.scan.2)
        &&& self.scanned == 0 || self.buf@[self.scanned - 1] == 10u8
        &&& (BlockScan { count: self.scan.0 as i64, in_comment: self.scan.1, in_string: self.scan.2 })
            == block_scan(self.buf@.subrange(0, self.scanned as int), scan_start())
    }

    /// Creates an empty accumulator whose first line is line 1.
    pub fn new() -> (r: Self)
        ensures
            r.inv(),
            r.buf_view().len() == 0,
            r.start_view() == 1,
            r.next_view() == 1,
            r.next_ok(0),
    {
        let r = Self { buf: Vec::new(), start_line: 1, next_line: 1, scanned: 0, scan: (0, false, false) };
        proof { assert(r.buf@.subrange(0, 0) =~= Seq::<u8>::empty()); }
        r
    }

    /// Appends one line (with its trailing newline, if any). Returns the completed unit and the
    /// line number of its first line when the accumulated text forms a complete unit.
    #[verifier::external_body]
    pub fn push_line(&mut self, line: &[u8]) -> Option<(Vec<u8>, usize)> {
        self.push_line_ref(line)
    }

    /// `push_line`: one step of the specification's `split_units_from`, for a line that is not
    /// empty.
    pub(crate) fn push_line_ref(&mut self, line: &[u8]) -> (r: Option<(Vec<u8>, usize)>)
        requires
            old(self).inv(),
            line@.len() > 0 ==> old(self).buf_view().len() + line@.len() < usize::MAX,
        ensures
            final(self).inv(),
            line@.len() > 0 && old(self).next_ok(0) ==> acc_step(*old(self), *final(self), line@, r),
            forall|n: int| old(self).next_ok(n + 1) ==> final(self).next_ok(n),
    {
        if self.buf.is_empty() {
            self.start_line = self.next_line;
        }
        let ghost before = self.buf@;
        append_bytes(&mut self.buf, line);
        proof {
            if self.scanned > 0 { assert(self.buf@[self.scanned - 1] == before[self.scanned - 1]); }
            assert(self.buf@.subrange(0, self.scanned as int) =~= before.subrange(0, self.scanned as int));
        }
        let ends_nl = !line.is_empty() && line[line.len() - 1] == b'\n';
        if ends_nl && self.next_line < usize::MAX {
            self.next_line += 1;
        }
        // Text beyond the limit is passed on as it is, and `run_unit` rejects it.
        if verified_unit_within_limit(self.buf.len()) {
            let n = self.buf.len();
            if (n >= 2 && self.buf[n - 1] == b'\n' && self.buf[n - 2] == b'\\')
                || (n >= 3 && self.buf[n - 1] == b'\n' && self.buf[n - 2] == b'\r' && self.buf[n - 3] == b'\\')
            {
                return None;
            }
            let scan = verified_repl_block_scan(self.buf.as_slice(), self.scanned, self.scan);
            proof {
                let k = self.scanned as int;
                let a = self.buf@.subrange(0, k);
                let b = self.buf@.skip(k);
                assert(a + b =~= self.buf@);
                if a.len() > 0 { assert(a[a.len() - 1] == self.buf@[k - 1]); }
                lemma_block_scan_split(a, b, scan_start());
            }
            if scan.0 > 0 || scan.1 || scan.2 {
                if ends_nl {
                    self.scanned = n;
                    self.scan = scan;
                    proof {
                        assert(self.buf@.subrange(0, n as int) =~= self.buf@);
                        assert(self.buf@.skip(0) =~= self.buf@);
                    }
                }
                return None;
            }
        }
        self.take()
    }

    /// Returns the incomplete text left at end of input, if any, so that it can be reported.
    #[verifier::external_body]
    pub fn finish(&mut self) -> Option<(Vec<u8>, usize)> {
        self.take()
    }

    /// Whether lines of an incomplete unit are waiting for more input (e.g. an open `{`).
    #[verifier::external_body]
    pub fn is_pending(&self) -> bool {
        !self.buf.is_empty()
    }

    /// Discards any partially accumulated unit (used after an interrupt).
    #[verifier::external_body]
    pub fn clear(&mut self) {
        self.buf.clear();
        self.scanned = 0;
        self.scan = (0, false, false);
    }

    fn take(&mut self) -> (r: Option<(Vec<u8>, usize)>)
        requires
            old(self).inv() || old(self).buf@.len() >= 0,
        ensures
            final(self).inv(),
            final(self).buf@.len() == 0,
            final(self).start_line == old(self).start_line,
            final(self).next_line == old(self).next_line,
            if old(self).buf@.len() == 0 {
                r is None
            } else {
                r matches Some((text, first)) && text@ == old(self).buf@ && first == old(self).start_line
            },
    {
        self.scanned = 0;
        self.scan = (0, false, false);
        let mut out = Vec::new();
        core::mem::swap(&mut self.buf, &mut out);
        proof { assert(self.buf@.subrange(0, 0) =~= Seq::<u8>::empty()); }
        if out.is_empty() {
            None
        } else {
            Some((out, self.start_line))
        }
    }

    /// `finish`, with its theorem.
    pub(crate) fn finish_ref(&mut self) -> (r: Option<(Vec<u8>, usize)>)
        ensures
            final(self).inv(),
            final(self).buf_view().len() == 0,
            final(self).start_view() == old(self).start_view(),
            final(self).next_view() == old(self).next_view(),
            forall|n: int| old(self).next_ok(n) ==> final(self).next_ok(n),
            if old(self).buf_view().len() == 0 {
                r is None
            } else {
                r matches Some((text, first)) && text@ == old(self).buf_view() && first as u64 == old(self).start_view()
            },
    {
        self.take()
    }
}

/// Trusted: `extend_from_slice` appends the slice.
#[verifier::external_body]
fn append_bytes(buf: &mut Vec<u8>, line: &[u8])
    ensures
        final(buf)@ == old(buf)@.add(line@),
{
    buf.extend_from_slice(line);
}

/// Trusted: the subslice of `text` from `a` to `b`.
#[verifier::external_body]
fn subslice(text: &[u8], a: usize, b: usize) -> (r: &[u8])
    requires
        a <= b <= text@.len(),
    ensures
        r@ == text@.subrange(a as int, b as int),
{
    &text[a..b]
}

/// The first line of the text from `pos`.
proof fn lemma_take_line(t: Seq<u8>, pos: int, end: int)
    requires
        0 <= pos < end <= t.len(),
        forall|k: int| pos <= k < end - 1 ==> t[k] != 10u8,
        t[end - 1] == 10u8 || end == t.len(),
    ensures
        take_line(t.skip(pos)) == (t.subrange(pos, end), t.skip(end)),
    decreases end - pos,
{
    let u = t.skip(pos);
    assert(u[0] == t[pos]);
    assert(u.drop_first() =~= t.skip(pos + 1));
    reveal_with_fuel(take_line, 2);
    if t[pos] == 10u8 {
        assert(end == pos + 1);
        assert(t.subrange(pos, end) =~= seq![10u8]);
    } else if pos + 1 == end {
        assert(end == t.len());
        assert(t.skip(end).len() == 0);
        assert(t.skip(end) =~= Seq::<u8>::empty());
        assert(t.subrange(pos, end) =~= seq![t[pos]].add(Seq::<u8>::empty()));
    } else {
        lemma_take_line(t, pos + 1, end);
        assert(t.subrange(pos, end) =~= seq![t[pos]].add(t.subrange(pos + 1, end)));
    }
}

/// A unit of the specification, from the text and first line of an implementation's unit.
pub(crate) open spec fn unit_of(u: (Vec<u8>, usize)) -> Unit {
    Unit { text: u.0@, line: u.1 as u64 }
}

/// The units already split off do not change the rest of the split.
proof fn lemma_split_out(t: Seq<u8>, buf: Seq<u8>, start: u64, next: u64, out: Seq<Unit>)
    ensures
        split_units_from(t, buf, start, next, out) == out + split_units_from(t, buf, start, next, seq![]),
    decreases t.len(),
{
    if t.len() == 0 {
        if buf.len() == 0 {
            assert(out + Seq::<Unit>::empty() =~= out);
        } else {
            assert(out.push(Unit { text: buf, line: start }) =~= out + seq![Unit { text: buf, line: start }]);
        }
    } else {
        let lr = take_line(t);
        if lr.1.len() < t.len() {
            let start2 = if buf.len() == 0 { next } else { start };
            let b2 = buf.add(lr.0);
            let ends_nl = lr.0.len() > 0 && lr.0[lr.0.len() - 1] == 10u8;
            let next2 = if ends_nl && next < 0xffff_ffff_ffff_ffffu64 { (next + 1) as u64 } else { next };
            if unit_pending(b2) {
                lemma_split_out(lr.1, b2, start2, next2, out);
            } else {
                let x = Unit { text: b2, line: start2 };
                let rest = split_units_from(lr.1, seq![], start2, next2, seq![]);
                lemma_split_out(lr.1, seq![], start2, next2, out.push(x));
                lemma_split_out(lr.1, seq![], start2, next2, seq![x]);
                assert(Seq::<Unit>::empty().push(x) =~= seq![x]);
                assert(out.push(x) + rest =~= out + (seq![x] + rest));
            }
        } else {
            assert(out + Seq::<Unit>::empty() =~= out);
        }
    }
}

/// A position in a text, with the lines read since the last unit: the state of splitting the
/// text into units.
pub(crate) struct UnitCursor {
    pos: usize,
    acc: UnitAccumulator,
}

impl UnitCursor {
    /// The cursor is at a place in the text `t` from which splitting can go on.
    pub(crate) closed spec fn inv(self, t: Seq<u8>) -> bool {
        &&& self.pos <= t.len()
        &&& t.len() < usize::MAX - 2
        &&& self.acc.inv()
        &&& self.acc.buf_view().len() <= self.pos
        &&& self.acc.next_ok(t.len() - self.pos)
    }

    /// The units of `t` not yet split off.
    pub(crate) closed spec fn rest(self, t: Seq<u8>) -> Seq<Unit> {
        split_units_from(t.skip(self.pos as int), self.acc.buf_view(), self.acc.start_view(), self.acc.next_view(), seq![])
    }

    /// The cursor at the start of a text.
    pub(crate) closed spec fn fresh(self) -> bool {
        &&& self.pos == 0
        &&& self.acc.inv()
        &&& self.acc.buf_view().len() == 0
        &&& self.acc.start_view() == 1
        &&& self.acc.next_view() == 1
    }

    /// A cursor at the start of a text.
    pub(crate) fn new() -> (r: Self)
        ensures
            r.fresh(),
    {
        UnitCursor { pos: 0, acc: UnitAccumulator::new() }
    }

    /// At the start of a text, the units not yet split off are all the units of the text.
    pub(crate) proof fn lemma_fresh(self, t: Seq<u8>)
        requires
            self.fresh(),
            t.len() < usize::MAX - 2,
        ensures
            self.inv(t),
            self.rest(t) == split_units(t),
    {
        bc_spec::lexer_lemmas::lemma_split_units(t);
        assert(t.skip(0) =~= t);
        assert(self.acc.buf_view() =~= Seq::<u8>::empty());
    }

    /// Splits off the next unit of `text`, or returns `None` at the end of the text.
    pub(crate) fn next_unit_ref(&mut self, text: &[u8]) -> (r: Option<(Vec<u8>, usize)>)
        requires
            old(self).inv(text@),
        ensures
            final(self).inv(text@),
            match r {
                Some(u) => old(self).rest(text@) == seq![unit_of(u)] + final(self).rest(text@),
                None => old(self).rest(text@).len() == 0 && final(self).rest(text@).len() == 0,
            },
    {
        let ghost r0 = self.rest(text@);
        let mut result: Option<(Vec<u8>, usize)> = None;
        let mut found = false;
        while !found && self.pos < text.len()
            invariant
                self.inv(text@),
                r0 == old(self).rest(text@),
                found ==> (result matches Some(u) && r0 == seq![unit_of(u)] + self.rest(text@)),
                !found ==> r0 == self.rest(text@),
            decreases text@.len() - self.pos,
        {
            let pos = self.pos;
            let mut end = pos + 1;
            while end < text.len() && text[end - 1] != b'\n'
                invariant
                    pos < end <= text@.len(),
                    forall|k: int| pos <= k < end - 1 ==> text@[k] != 10u8,
                decreases text@.len() - end,
            {
                end += 1;
            }
            let line = subslice(text, pos, end);
            let ghost b0 = self.acc.buf_view();
            let ghost a0 = self.acc;
            proof {
                lemma_take_line(text@, pos as int, end as int);
                assert(line@[line@.len() - 1] == text@[end - 1]);
            }
            // The position moves past the line first, so that a front end that recovers from a
            // panic inside the step goes on after the line instead of reading it again.
            self.pos = end;
            let r = self.acc.push_line_ref(line);
            proof {
                let t = text@.skip(pos as int);
                assert(t.len() > 0);
                assert(take_line(t).1.len() < t.len());
                assert(acc_step(a0, self.acc, line@, r));
                if !unit_pending(b0.add(line@)) {
                    assert(self.acc.buf_view() =~= Seq::<u8>::empty());
                    let x = Unit { text: b0.add(line@), line: self.acc.start_view() };
                    lemma_split_out(text@.skip(end as int), seq![], self.acc.start_view(), self.acc.next_view(), seq![x]);
                    assert(Seq::<Unit>::empty().push(x) =~= seq![x]);
                }
                assert(a0.next_ok((text@.len() - end) + 1));
            }
            if let Some(u) = r {
                result = Some(u);
                found = true;
            }
        }
        if !found {
            let ghost b0 = self.acc.buf_view();
            let ghost st0 = self.acc.start_view();
            proof { assert(text@.skip(self.pos as int).len() == 0); }
            result = self.acc.finish_ref();
            proof {
                assert(text@.skip(self.pos as int).len() == 0);
                assert(self.acc.buf_view() =~= Seq::<u8>::empty());
                if b0.len() > 0 {
                    assert(Seq::<Unit>::empty().push(Unit { text: b0, line: st0 }) =~= seq![Unit { text: b0, line: st0 }]);
                    assert(seq![Unit { text: b0, line: st0 }] + Seq::<Unit>::empty() =~= seq![Unit { text: b0, line: st0 }]);
                }
            }
        }
        result
    }
}

/// The units of a text, split off one at a time and run by [`Evaluator::run_next_unit`]. This
/// is the loop of [`Evaluator::run_source`] for a front end that runs each unit itself (`bc_clone`
/// guards each one against an internal panic).
pub struct SourceUnits {
    text: Vec<u8>,
    cur: UnitCursor,
}

impl SourceUnits {
    /// The cursor is at a place in the text from which splitting can go on.
    pub closed spec fn inv(self) -> bool {
        self.cur.inv(self.text@)
    }

    /// The units of the text not yet split off.
    pub closed spec fn rest(self) -> Seq<Unit> {
        self.cur.rest(self.text@)
    }

    /// The units of `text`, which is bytes and need not be UTF-8.
    #[verifier::external_body]
    pub fn new(text: Vec<u8>) -> Self {
        Self::new_ref(text)
    }

    /// `new`, for a text that is not too long to count.
    pub(crate) fn new_ref(text: Vec<u8>) -> (r: Self)
        requires
            text@.len() < usize::MAX - 2,
        ensures
            r.inv(),
            r.rest() == split_units(text@),
    {
        let cur = UnitCursor::new();
        proof { cur.lemma_fresh(text@); }
        SourceUnits { text, cur }
    }
}

/// `run_units` runs the first unit, then the others.
proof fn lemma_run_units_first(opts: Options, rs: RunState, src: Seq<u8>, us: Seq<Unit>)
    requires
        us.len() > 0,
        !rs.quit,
    ensures
        run_units(opts, rs, src, us) == run_units(opts, spec_run_unit(opts, rs, src, us[0]), src, us.drop_first()),
{
}

/// The hypothesis of the theorem of a step: the state corresponds to the specification's and the
/// settings to its options.
pub(crate) open spec fn r_step_pre(e: Evaluator, policy: ExtensionPolicy, limit: usize, opts: Options, rs: RunState) -> bool {
    &&& r_top(e, rs.st)
    &&& r_settings(policy, limit, opts)
    &&& limit < usize::MAX - 2
}

/// The theorem of a step: `None` at the end of the units, and otherwise the outcome of the first
/// unit.
pub(crate) open spec fn r_step(r: Option<UnitOutcome>, e0: Evaluator, e: Evaluator, rest0: Seq<Unit>, rest: Seq<Unit>, policy: ExtensionPolicy, limit: usize, opts: Options, rs: RunState, src: Seq<u8>) -> bool {
    match r {
        None => rest0.len() == 0 && rest.len() == 0 && e == e0,
        Some(o) => {
            &&& rest0.len() > 0
            &&& rest == rest0.drop_first()
            &&& r_step_pre(e0, policy, limit, opts, rs) ==> r_outcome(o, e, rs, spec_run_unit(opts, rs, src, rest0[0]))
        },
    }
}

impl Evaluator {
    /// Splits `text` into units and runs each one, continuing after errors until the end of
    /// the text or `quit`. `text` is bytes and need not be UTF-8.
    #[verifier::external_body]
    pub fn run_source(&mut self, text: &[u8], source: &str) -> RunSummary {
        self.run_source_ref(text, source, Ghost(arbitrary()), Ghost(arbitrary()))
    }

    /// Runs the next unit of `units`, or returns `None` after the last one. A front end that
    /// calls this until `None` or [`UnitOutcome::Quit`] runs the text as [`Evaluator::run_source`]
    /// does.
    #[verifier::external_body]
    pub fn run_next_unit(&mut self, units: &mut SourceUnits, source: &str) -> Option<UnitOutcome> {
        let policy = self.extension_policy;
        let limit = self.max_depth;
        self.run_next_source_unit_ref(units, source, policy, limit, Ghost(arbitrary()), Ghost(arbitrary()))
    }

    /// `run_next_unit`: one step of the specification's `run_units` on the units not yet run.
    pub(crate) fn run_next_source_unit_ref(&mut self, units: &mut SourceUnits, source: &str, policy: ExtensionPolicy, limit: usize, Ghost(opts): Ghost<SpecOptions>, Ghost(rs): Ghost<SpecRun>) -> (r: Option<UnitOutcome>)
        requires
            old(self).inv(),
            old(units).inv(),
        ensures
            final(self).inv(),
            final(units).inv(),
            r_step(r, *old(self), *final(self), old(units).rest(), final(units).rest(), policy, limit, opts, rs, source.spec_bytes()),
    {
        self.run_next_unit_ref(units.text.as_slice(), &mut units.cur, source, policy, limit, Ghost(opts), Ghost(rs))
    }

    /// One step of the specification's `run_units` on the units of `text` not yet split off.
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    pub(crate) fn run_next_unit_ref(&mut self, text: &[u8], cur: &mut UnitCursor, source: &str, policy: ExtensionPolicy, limit: usize, Ghost(opts): Ghost<SpecOptions>, Ghost(rs): Ghost<SpecRun>) -> (r: Option<UnitOutcome>)
        requires
            old(self).inv(),
            old(cur).inv(text@),
        ensures
            final(self).inv(),
            final(cur).inv(text@),
            r_step(r, *old(self), *final(self), old(cur).rest(text@), final(cur).rest(text@), policy, limit, opts, rs, source.spec_bytes()),
    {
        let ghost rest0 = cur.rest(text@);
        match cur.next_unit_ref(text) {
            None => None,
            Some(u) => {
                proof {
                    assert(rest0[0] == unit_of(u));
                    assert(rest0.drop_first() =~= cur.rest(text@));
                }
                let ghost su = unit_of(u);
                Some(self.run_unit_ref(u.0.as_slice(), source, u.1, policy, limit, Ghost(opts), Ghost(rs), Ghost(su)))
            },
        }
    }

    /// `run_source`: the refinement theorem of one input. The error count is related only as far
    /// as it matters for the exit status, because the specification's count saturates.
    pub(crate) fn run_source_ref(&mut self, text: &[u8], source: &str, Ghost(opts): Ghost<SpecOptions>, Ghost(rs): Ghost<SpecRun>) -> (r: RunSummary)
        requires
            old(self).inv(),
            text@.len() < usize::MAX - 2,
        ensures
            final(self).inv(),
            r_source(r, *old(self), *final(self), opts, rs, source.spec_bytes(), text@),
    {
        let ghost src = source.spec_bytes();
        let ghost goal = run_units(opts, rs, src, split_units(text@));
        let ghost hyp = r_source_pre(*self, opts, rs);
        let mut units = UnitCursor::new();
        proof { units.lemma_fresh(text@); }
        let policy = self.extension_policy;
        let limit = self.max_depth;
        let mut summary = RunSummary { errors: 0, quit: false };
        let ghost mut cur = rs;
        let mut done = false;
        while !done
            invariant
                self.inv(),
                units.inv(text@),
                !summary.quit,
                hyp == r_source_pre(*old(self), opts, rs),
                goal == run_units(opts, rs, src, split_units(text@)),
                src == source.spec_bytes(),
                hyp ==> r_settings(policy, limit, opts) && limit < usize::MAX - 2,
                done ==> units.rest(text@).len() == 0,
                (hyp && !goal.not_modeled) ==> r_top(*self, cur.st) && !cur.quit && !cur.not_modeled
                    && run_units(opts, cur, src, units.rest(text@)) == goal
                    && (cur.errors > 0) == (rs.errors > 0 || summary.errors > 0),
            decreases units.rest(text@).len(), if done { 0int } else { 1int },
        {
            let ghost rest0 = units.rest(text@);
            let ghost next = if rest0.len() > 0 { spec_run_unit(opts, cur, src, rest0[0]) } else { cur };
            match self.run_next_unit_ref(text, &mut units, source, policy, limit, Ghost(opts), Ghost(cur)) {
                None => {
                    done = true;
                },
                Some(outcome) => {
                    proof {
                        if hyp && !goal.not_modeled {
                            lemma_run_units_first(opts, cur, src, rest0);
                            if next.not_modeled {
                                lemma_run_units_stop(opts, next, src, units.rest(text@));
                            }
                        }
                    }
                    match outcome {
                        UnitOutcome::Completed => {},
                        UnitOutcome::Failed => {
                            if summary.errors < usize::MAX {
                                summary.errors += 1;
                            }
                        },
                        UnitOutcome::Quit => {
                            summary.quit = true;
                            proof {
                                if hyp && !goal.not_modeled {
                                    assert(!next.not_modeled);
                                    assert(next.quit);
                                    lemma_run_units_stop(opts, next, src, units.rest(text@));
                                    assert(goal == next);
                                    assert(next.errors == cur.errors);
                                }
                            }
                            return summary;
                        },
                    }
                    proof { if hyp && !goal.not_modeled { cur = next; } }
                },
            }
        }
        summary
    }
}

/// What the theorem of `run_source_ref` assumes of the state before a unit.
pub(crate) open spec fn r_source_pre(e: Evaluator, opts: Options, rs: RunState) -> bool {
    &&& r_top(e, rs.st)
    &&& r_opts(e, opts)
    &&& e.max_depth < usize::MAX - 2
    &&& !rs.quit
    &&& !rs.not_modeled
}

/// The theorem of `run_source_ref`: unless the specification leaves its model, the state and the
/// error status are those of `run_units` on the units of the text.
pub(crate) open spec fn r_source(r: RunSummary, e0: Evaluator, e: Evaluator, opts: Options, rs: RunState, src: Seq<u8>, text: Seq<u8>) -> bool {
    let goal = run_units(opts, rs, src, split_units(text));
    (r_source_pre(e0, opts, rs) && !goal.not_modeled) ==> {
        &&& r_top(e, goal.st)
        &&& goal.quit == r.quit
        &&& (goal.errors > 0) == (rs.errors > 0 || r.errors > 0)
    }
}

/// A front end may set the nesting limit of a new evaluator: the state is then the initial one
/// for that limit.
pub(crate) proof fn lemma_set_limit(e: Evaluator, d: u64, limit: usize, eval_limit: usize)
    requires
        r_top(e, initial(d)),
    ensures
        r_top(Evaluator { max_depth: limit, max_eval_depth: eval_limit, ..e }, initial(eval_limit as u64)),
{
}

/// The specification's `run_inputs` runs the units of each input in turn.
pub(crate) proof fn lemma_run_inputs_step(opts: Options, rs: RunState, inputs: Seq<Input>)
    requires
        inputs.len() > 0,
        !rs.quit,
    ensures
        run_inputs(opts, rs, inputs) == run_inputs(opts, run_units(opts, rs, inputs[0].name, split_units(inputs[0].text)), inputs.drop_first()),
{
}

/// Whether a source failed in these summaries.
pub(crate) open spec fn any_errors(ss: Seq<RunSummary>) -> bool
    decreases ss.len(),
{
    ss.len() > 0 && (ss[0].errors > 0 || any_errors(ss.drop_first()))
}

/// The evaluators `es`, with the summaries `ss`, went through `run_source_ref` on the inputs in
/// order, and stopped at the end of the inputs or at `quit`.
pub(crate) open spec fn r_sources(es: Seq<Evaluator>, ss: Seq<RunSummary>, opts: Options, rs: RunState, inputs: Seq<Input>) -> bool
    decreases ss.len(),
{
    &&& es.len() == ss.len() + 1
    &&& r_opts(es[0], opts)
    &&& es[0].max_depth < usize::MAX - 2
    &&& if ss.len() == 0 {
        inputs.len() == 0
    } else {
        &&& inputs.len() > 0
        &&& r_source(ss[0], es[0], es[1], opts, rs, inputs[0].name, inputs[0].text)
        &&& if ss[0].quit {
            ss.len() == 1
        } else {
            r_sources(es.drop_first(), ss.drop_first(), opts, run_units(opts, rs, inputs[0].name, split_units(inputs[0].text)), inputs.drop_first())
        }
    }
}

/// A run leaves the specification's model only by stopping.
proof fn lemma_units_stop(opts: Options, rs: RunState, src: Seq<u8>, us: Seq<Unit>)
    requires
        rs.not_modeled ==> rs.quit,
    ensures
        run_units(opts, rs, src, us).not_modeled ==> run_units(opts, rs, src, us).quit,
    decreases us.len(),
{
    if us.len() > 0 && !rs.quit {
        lemma_units_stop(opts, spec_run_unit(opts, rs, src, us[0]), src, us.drop_first());
    }
}

/// The theorem of `run_source_ref`, over the inputs in order.
proof fn lemma_sources(es: Seq<Evaluator>, ss: Seq<RunSummary>, opts: Options, rs: RunState, inputs: Seq<Input>)
    requires
        r_sources(es, ss, opts, rs, inputs),
        r_top(es[0], rs.st),
        !rs.quit,
        !rs.not_modeled,
    ensures
        ({
            let g = run_inputs(opts, rs, inputs);
            !g.not_modeled ==> {
                &&& r_top(es.last(), g.st)
                &&& g.quit == (ss.len() > 0 && ss.last().quit)
                &&& (g.errors > 0) == (rs.errors > 0 || any_errors(ss))
            }
        }),
    decreases ss.len(),
{
    if ss.len() > 0 {
        let next = run_units(opts, rs, inputs[0].name, split_units(inputs[0].text));
        lemma_run_inputs_step(opts, rs, inputs);
        lemma_units_stop(opts, rs, inputs[0].name, split_units(inputs[0].text));
        if next.quit {
            assert(run_inputs(opts, next, inputs.drop_first()) == next);
            if !next.not_modeled {
                assert(ss[0].quit);
                assert(es.last() == es[1]);
                assert(ss.last() == ss[0]);
                assert(any_errors(ss.drop_first()) == false);
            }
        } else if !next.not_modeled {
            assert(!ss[0].quit);
            lemma_sources(es.drop_first(), ss.drop_first(), opts, next, inputs.drop_first());
            assert(es.drop_first().last() == es.last());
            if ss.len() > 1 { assert(ss.drop_first().last() == ss.last()); }
        } else {
            assert(false);
        }
    }
}

/// The composition of the theorems. If evaluators start in the specification's initial state
/// (`with_streams`, with `lemma_set_limit` for the nesting limit) and go through `run_source_ref`
/// on the inputs in order, then the output, the diagnostics and the exit status are those of the
/// specification's `run`, unless it leaves its model. The front ends' own loops are not proved
/// to do this: the embedded targets call `run_source`, and `bc_clone` calls `run_next_unit` until
/// `None` or `quit` for a file or piped input, and `push_line` and `run_unit` in the REPL.
pub(crate) proof fn lemma_outcome(es: Seq<Evaluator>, ss: Seq<RunSummary>, opts: Options, inputs: Seq<Input>)
    requires
        r_top(es[0], initial(opts.max_eval_depth)),
        r_sources(es, ss, opts, RunState { st: initial(opts.max_eval_depth), errors: 0u64, quit: false, not_modeled: false }, inputs),
        !run(opts, inputs).not_modeled,
    ensures
        out_log(&es.last().stdout_writer) == run(opts, inputs).stdout,
        err_log(&es.last().stderr_writer) == run(opts, inputs).stderr,
        run(opts, inputs).status == (if any_errors(ss) { 1u8 } else { 0u8 }),
{
    let rs = RunState { st: initial(opts.max_eval_depth), errors: 0u64, quit: false, not_modeled: false };
    lemma_sources(es, ss, opts, rs, inputs);
    let g = run_inputs(opts, rs, inputs);
    assert(r_state(Evaluator { eval_depth: 0, invocation_ibase: None, ..es.last() }, with_call(with_depth(g.st, 0), g.st.calls, false, g.st.inv_ibase)));
}

/// `run_units` stops at `quit`.
proof fn lemma_run_units_stop(opts: Options, rs: RunState, src: Seq<u8>, us: Seq<Unit>)
    requires
        rs.quit,
    ensures
        run_units(opts, rs, src, us) == rs,
{
}

} // verus!

impl Default for UnitAccumulator {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for UnitAccumulator {
    fn clone(&self) -> Self {
        Self {
            buf: self.buf.clone(),
            start_line: self.start_line,
            next_line: self.next_line,
            scanned: self.scanned,
            scan: self.scan,
        }
    }
}

impl core::fmt::Debug for UnitAccumulator {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("UnitAccumulator")
            .field("buf", &self.buf)
            .field("start_line", &self.start_line)
            .field("next_line", &self.next_line)
            .finish()
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

    /// Texts whose units are split in every way the accumulator can: continuations (also after
    /// `\r`), blocks, comments and strings over several lines, a last line without a newline,
    /// an incomplete unit at the end, `quit`, and errors.
    const SPLIT_CASES: &[&[u8]] = &[
        b"",
        b"\n",
        b"1\n2\n",
        b"1\n2",
        b"1 + \\\n2\n3\n",
        b"1 + \\\r\n2\r\n",
        b"{\n1\n}\n2\n",
        b"define f(x) {\nreturn (x)\n}\nf(3)\n",
        b"/* a\nb */ 4\n\"x\ny\"\n",
        b"{\n1\n",
        b"1\nquit\n2\n",
        b"1 +\n2 +; 3\n4/0\n5\n",
        b"\xff\n6\n",
    ];

    /// The units of a text as the accumulator gives them line by line.
    fn units_by_lines(text: &[u8]) -> Vec<(Vec<u8>, usize)> {
        let mut acc = UnitAccumulator::new();
        let mut units: Vec<(Vec<u8>, usize)> = text
            .split_inclusive(|&b| b == b'\n')
            .filter_map(|l| acc.push_line(l))
            .collect();
        units.extend(acc.finish());
        units
    }

    #[test]
    fn the_cursor_splits_a_text_as_the_accumulator_does_line_by_line() {
        for &text in SPLIT_CASES {
            let mut cur = UnitCursor::new();
            let mut units = Vec::new();
            while let Some(u) = cur.next_unit_ref(text) {
                units.push(u);
            }
            assert_eq!(cur.next_unit_ref(text), None);
            assert_eq!(units, units_by_lines(text), "{:?}", text);
        }
    }

    #[test]
    fn running_the_units_one_at_a_time_is_running_the_source() {
        let run_bytes = |step: bool, text: &[u8]| {
            let out = Shared::default();
            let err = Shared::default();
            let mut ev = Evaluator::new(false, Box::new(out.clone()), Box::new(err.clone()));
            let summary = if step {
                let mut units = SourceUnits::new(text.to_vec());
                let mut summary = RunSummary::default();
                while let Some(outcome) = ev.run_next_unit(&mut units, STDIN_SOURCE) {
                    match outcome {
                        UnitOutcome::Completed => {}
                        UnitOutcome::Failed => summary.errors += 1,
                        UnitOutcome::Quit => {
                            summary.quit = true;
                            break;
                        }
                    }
                }
                summary
            } else {
                ev.run_source(text, STDIN_SOURCE)
            };
            (summary, out.0.borrow().clone(), err.0.borrow().clone())
        };
        for &text in SPLIT_CASES {
            assert_eq!(run_bytes(true, text), run_bytes(false, text), "{:?}", text);
        }
    }

    #[cfg(all(not(miri), target_pointer_width = "64"))]
    #[test]
    fn test_accumulator_clone_keeps_the_scan_and_debug_shows_the_lines() {
        let mut acc = UnitAccumulator::new();
        assert_eq!(acc.push_line(b"{\n"), None);
        let mut copy = acc.clone();
        assert_eq!(copy.push_line(b"}\n"), Some((b"{\n}\n".to_vec(), 1)));
        assert_eq!(acc.push_line(b"}\n"), Some((b"{\n}\n".to_vec(), 1)));
        assert_eq!(
            UnitAccumulator::default().push_line(b"1\n"),
            Some((b"1\n".to_vec(), 1))
        );
        assert!(alloc::format!("{:?}", copy).contains("next_line: 3"));
    }

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

    /// Runs `text` on an evaluator prepared by `setup`, with the math library if `math`.
    fn run_on(
        text: &str,
        math: bool,
        setup: impl FnOnce(&mut Evaluator),
    ) -> (RunSummary, String, String) {
        let out = Shared::default();
        let err = Shared::default();
        let mut ev = Evaluator::new(math, Box::new(out.clone()), Box::new(err.clone()));
        setup(&mut ev);
        let summary = ev.run_source(text.as_bytes(), STDIN_SOURCE);
        let out = out.0.borrow().clone();
        let err = err.0.borrow().clone();
        (summary, out, err)
    }

    /// Cutting a valid program after any of its tokens and adding an illegal character gives
    /// exactly that lexical error: the parser passes it on from wherever it reads the next
    /// token, and nothing of the prefix is an error.
    #[test]
    fn lexical_error_after_any_token_is_reported_as_itself() {
        let program: &[&str] = &[
            "define", "f", "(", "a", ",", "b", "[", "]", ",", "c", ")", "{", "\n", //
            "auto", "x", ",", "y", "[", "]", "\n", //
            "x", "=", "a", ";", "y", "[", "0", "]", "=", "c", ";", "++", "x", ";", "--", "y", "[",
            "0", "]", ";", "x", "++", ";", "y", "[", "0", "]", "--", "\n", //
            "x", "+=", "b", "[", "1", "]", "*", "-", "2", "^", "2", "%", "3", "/", "1", "-", "(",
            "1", ")", "\n", //
            "if", "(", "x", "<=", "1", ")", "x", "=", "1", "\n", //
            "while", "(", "x", ">", "9", ")", "break", "\n", //
            "for", "(", "x", "=", "0", ";", "x", "!=", "1", ";", "x", "++", ")", "{", "}", "\n",
            "return", "(", "sqrt", "(", "x", ")", "+", "length", "(", "x", ")", "+", "scale", "(",
            "x", ")", "+", "g", "(", ")", ")", "\n", //
            "}", "\n", //
            "define", "g", "(", ")", "{", "\n", "return", "\n", "return", "(", ")", "\n", "}",
            "\n", //
            "b", "[", "1", "]", "=", "1", ";", "z", "=", "f", "(", "1", ",", "b", "[", "]", ",",
            "2", ")", ";", "ibase", "=", "A", ";", "obase", ";", "scale", ";", "\"s\"", "\n",
        ];
        let (summary, _, err) = run(&alloc::format!("{}\n", program.join(" ")));
        assert_eq!((summary.errors, err.as_str()), (0, ""));
        for k in 0..=program.len() {
            let prefix = program[..k].join(" ");
            let line = 1 + program[..k].iter().filter(|t| **t == "\n").count();
            let (_, _, err) = run(&alloc::format!("{prefix} @\n"));
            assert_eq!(
                err,
                alloc::format!("(standard_in) {line}: illegal character: @\n"),
                "after {prefix:?}"
            );
        }
    }

    /// For every limit on the levels evaluated at once, a program with statements and calls
    /// nested in each other either runs to the end or stops at the limit, and a larger limit
    /// never stops it earlier.
    #[test]
    fn every_evaluation_limit_stops_cleanly_or_completes() {
        let program = "define f(n) {\nauto i\nif (n > 0) {\nfor (i = 0; i < 1; i++) {\n\
                       while (0) { }\nif (f(n - 1) == 0) { x = x + 1 }\n}\n}\nreturn (0)\n}\n\
                       f(3)\nx\n";
        let mut completed = false;
        for k in 1..=48 {
            let (summary, out, err) = run_on(program, false, |ev| ev.max_eval_depth = k);
            if summary.errors == 0 {
                assert_eq!((out.as_str(), err.as_str()), ("0\n3\n", ""), "k = {k}");
                completed = true;
            } else {
                // Under a small enough limit the last line, `x`, fails as well.
                assert!(
                    !completed,
                    "k = {k}: stopped after a smaller limit completed"
                );
                assert_eq!(summary.errors, err.lines().count(), "k = {k}: {err}");
                assert!(
                    err.lines().all(|l| l.ends_with(": nesting too deep")),
                    "k = {k}: {err}"
                );
            }
        }
        assert!(completed);
    }

    /// For every limit on the depth of the syntax tree, a relational expression with nested
    /// operands either parses or is rejected as too deep.
    #[test]
    fn every_parse_depth_limit_accepts_or_rejects_cleanly() {
        let mut accepted = false;
        for k in 1..=16 {
            let (_, out, err) = run_on("if (((1)) < ((((2))))) 3\n", false, |ev| ev.max_depth = k);
            if err.is_empty() {
                assert_eq!(out, "3\n", "k = {k}");
                accepted = true;
            } else {
                assert!(
                    !accepted,
                    "k = {k}: rejected after a smaller limit accepted"
                );
                assert_eq!(err, "(standard_in) 1: nesting too deep\n", "k = {k}");
            }
        }
        assert!(accepted);
    }

    #[test]
    fn runtime_diagnostics_of_less_common_errors() {
        let cases: &[(&str, &str, &str)] = &[
            (
                "define f(a[]) {\nreturn (0)\n}\nf(1)\n",
                "",
                "Runtime error (func=(main)): Parameter type mismatch parameter a.\n",
            ),
            (
                "define f(a) {\nreturn (0)\n}\nf(b[])\n",
                "",
                "Runtime error (func=(main)): Parameter type mismatch parameter a.\n",
            ),
            // A subscript computed by a call is evaluated on the machine, not the fast path.
            (
                "define f() {\nreturn (-1)\n}\na[f()]++\n",
                "",
                "Runtime error (func=(main)): Array a subscript out of bounds.\n",
            ),
            (
                "for (x = 1/0; x < 1; x++) 5\n",
                "",
                "Runtime error (func=(main)): Divide by zero\n",
            ),
            (
                "for (x = 0; 1/0; x++) 5\n",
                "",
                "Runtime error (func=(main)): Divide by zero\n",
            ),
            (
                "for (x = 0; x < 1; x = 1/0) 5\n",
                "5\n",
                "Runtime error (func=(main)): Divide by zero\n",
            ),
            (
                "define f() {\nibase = 99\nreturn (ibase)\n}\nf()\n",
                "16\n",
                "Runtime warning (func=f): ibase too large, set to 16\n",
            ),
            (
                "scale = 2; .1 ^ 2000000000\n",
                "",
                "Runtime error (func=(main)): scale too large\n",
            ),
        ];
        for (text, out, err) in cases {
            let (_, actual_out, actual_err) = run(text);
            assert_eq!(
                (actual_out.as_str(), actual_err.as_str()),
                (*out, *err),
                "{text}"
            );
        }
        let (_, out, err) = run_on("j(1, 10000000000)\n", true, |_| {});
        assert_eq!(
            (out.as_str(), err.as_str()),
            ("", "Runtime error (func=(main)): argument too large\n")
        );
    }

    #[test]
    fn diagnostic_stream_flushes_its_writer() {
        let (_, _, _) = run_on("", false, |ev| {
            assert_eq!(ev.stderr_writer().flush(), Ok(()));
        });
    }
}
