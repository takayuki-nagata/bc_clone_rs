// SPDX-License-Identifier: MIT

//! Top level of the specification: options, inputs, units and the observable outcome
//! (`bc_cli::run_app` with `run_non_interactive_block`, and `Evaluator::run_unit`).

use crate::eval::*;
use crate::lexer::*;
use crate::num::*;
use crate::output::*;
use crate::parser::*;
use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

/// Exit status of the oracle for inputs outside the specification (see the crate docs).
pub const NOT_MODELED: u8 = 125;

exec_spec_verified! {

/// Command-line options that the specification models (`-s` and `-w`), and the nesting limits
/// of the front end: `Evaluator::max_depth` (parsing) and `Evaluator::max_eval_depth`.
pub struct Options {
    pub reject_extensions: bool,
    pub warn_extensions: bool,
    pub max_depth: u64,
    pub max_eval_depth: u64,
}

/// One input source: a file operand, or standard input (named `(standard_in)`), as bytes.
pub struct Input {
    pub name: Seq<u8>,
    pub text: Seq<u8>,
}

/// Everything a run of `bc_clone` makes observable. `not_modeled` marks a run that left the
/// specification (it ran out of fuel).
pub struct Outcome {
    pub stdout: Seq<u8>,
    pub stderr: Seq<u8>,
    pub status: u8,
    pub not_modeled: bool,
}

/// The state between units: the evaluator, the number of failed units, and whether `quit` was
/// read or the run left the specification.
pub struct RunState {
    pub st: EState,
    pub errors: u64,
    pub quit: bool,
    pub not_modeled: bool,
}

/// The initial evaluator: `scale = 0`, `ibase = obase = 10`, no names, no output.
pub open spec fn initial(max_depth: u64) -> EState {
    EState {
        vars: seq![], arrays: seq![], funcs: seq![],
        scale: 0u32, ibase: 10u32, obase: 10u32,
        out: seq![], err: seq![], col: 0u64,
        brk: false, ret: false, ret_val: zero_num(),
        calls: seq![], depth: 0u64, max_depth: max_depth, has_inv: false, inv_ibase: 10u32,
    }
}

pub open spec fn failed(rs: RunState, st: EState) -> RunState {
    RunState { st: st, errors: if rs.errors < 0xffff_ffffu64 { (rs.errors + 1) as u64 } else { rs.errors }, quit: false, not_modeled: false }
}

/// `<source> <line>: ` for a line of a unit that starts at line `first`.
pub open spec fn at_line(source: Seq<u8>, first: u64, line: u64) -> Seq<u8> {
    let l = if line >= 1 && first <= 0xffff_ffffu64 && line <= 0xffff_ffffu64 { (first + line - 1) as u64 } else { first };
    source.push(32u8).add(dec_str(l)).add(seq![58u8, 32])
}

/// The `-w` / `-s` diagnostics of the extension uses `ext`.
pub open spec fn ext_diags(ext: Seq<ExtUse>, source: Seq<u8>, first: u64, reject: bool) -> Seq<u8>
    decreases ext.len()
{
    if ext.len() == 0 { seq![] }
    else {
        let prefix = if reject { seq![69u8, 114, 114, 111, 114, 58, 32] } else { seq![40u8, 87, 97, 114, 110, 105, 110, 103, 41, 32] };
        at_line(source, first, ext[0].line).add(prefix).add(ext[0].desc).push(10u8)
            .add(ext_diags(ext.drop_first(), source, first, reject))
    }
}

/// `Runtime error (func=<f>): <msg>`.
pub open spec fn runtime_diag(e: RErr) -> Seq<u8> {
    seq![82u8, 117, 110, 116, 105, 109, 101, 32, 101, 114, 114, 111, 114, 32, 40, 102, 117, 110, 99, 61].add(if e.has_func { e.func } else { seq![40u8, 109, 97, 105, 110, 41] }).add(seq![41u8, 58, 32]).add(e.msg).push(10u8)
}

/// Executes the items of a parsed unit in order.
pub open spec fn exec_items(nodes: Seq<Node>, items: Seq<usize>, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else if items.len() == 0 { er_ok(st, zero_num()) }
    else {
        let r = exec(nodes, items[0], st, (fuel - 1) as u64);
        if !r.ok { r } else { exec_items(nodes, items.drop_first(), r.st, (fuel - 1) as u64) }
    }
}

/// `input unit too long`.
pub open spec fn unit_too_long_msg() -> Seq<u8> {
    seq![105u8, 110, 112, 117, 116, 32, 117, 110, 105, 116, 32, 116, 111, 111, 32, 108, 111, 110, 103]
}

/// `Evaluator::run_unit`: a unit longer than `BC_UNIT_MAX` fails without being parsed.
pub open spec fn run_unit(opts: Options, rs: RunState, source: Seq<u8>, u: Unit) -> RunState {
    if u.text.len() > 1000000000 {
        let st0 = with_call(with_depth(rs.st, 0u64), rs.st.calls, false, rs.st.inv_ibase);
        failed(rs, with_err(st0, st0.err.add(at_line(source, u.line, 1u64)).add(unit_too_long_msg()).push(10u8)))
    } else {
        run_parsed_unit(opts, rs, source, u)
    }
}

/// `Evaluator::run_unit` after the length check.
pub open spec fn run_parsed_unit(opts: Options, rs: RunState, source: Seq<u8>, u: Unit) -> RunState {
    let cfg = PCfg { record_extensions: opts.reject_extensions || opts.warn_extensions, max_depth: opts.max_depth };
    run_parse_result(opts, rs, source, u.line, parse_unit(tokenize(u.text), cfg))
}

/// What a unit that starts at line `first` does, given the result `p` of parsing it.
pub open spec fn run_parse_result(opts: Options, rs: RunState, source: Seq<u8>, first: u64, p: PR) -> RunState {
    let st0 = with_call(with_depth(rs.st, 0u64), rs.st.calls, false, rs.st.inv_ibase);
    let reject = opts.reject_extensions;
    let st1 = with_err(st0, st0.err.add(ext_diags(p.st.ext, source, first, reject)));
    if p.err.out_of_fuel {
        RunState { st: st1, errors: rs.errors, quit: true, not_modeled: true }
    } else if reject && p.st.ext.len() > 0 && p.ok {
        failed(rs, st1)
    } else if !p.ok {
        if p.err.quit {
            RunState { st: st1, errors: rs.errors, quit: true, not_modeled: false }
        } else {
            failed(rs, with_err(st1, st1.err.add(at_line(source, first, p.err.line)).add(p.err.msg).push(10u8)))
        }
    } else {
        let r = exec_items(p.st.nodes, p.list, st1, 0x4000_0000_0000_0000u64);
        if r.ok {
            RunState { st: r.st, errors: rs.errors, quit: false, not_modeled: false }
        } else if r.err.out_of_fuel {
            RunState { st: r.st, errors: rs.errors, quit: true, not_modeled: true }
        } else {
            let st2 = with_flags(r.st, false, false, r.st.ret_val);
            failed(rs, with_err(st2, st2.err.add(runtime_diag(r.err))))
        }
    }
}

/// Runs the units of one input, stopping at `quit`.
pub open spec fn run_units(opts: Options, rs: RunState, source: Seq<u8>, units: Seq<Unit>) -> RunState
    decreases units.len()
{
    if units.len() == 0 || rs.quit { rs }
    else { run_units(opts, run_unit(opts, rs, source, units[0]), source, units.drop_first()) }
}

/// Runs the inputs in order, stopping at `quit`.
pub open spec fn run_inputs(opts: Options, rs: RunState, inputs: Seq<Input>) -> RunState
    decreases inputs.len()
{
    if inputs.len() == 0 || rs.quit { rs }
    else {
        let i = inputs[0];
        run_inputs(opts, run_units(opts, rs, i.name, split_units(i.text)), inputs.drop_first())
    }
}

/// The meaning of `bc_clone` with `opts` on `inputs` (the file operands in order, then
/// standard input): exit status 1 if any unit failed.
pub open spec fn run(opts: Options, inputs: Seq<Input>) -> Outcome {
    let rs = run_inputs(opts, RunState { st: initial(opts.max_eval_depth), errors: 0u64, quit: false, not_modeled: false }, inputs);
    Outcome { stdout: rs.st.out, stderr: rs.st.err, status: if rs.errors > 0 { 1u8 } else { 0u8 }, not_modeled: rs.not_modeled }
}

} // exec_spec_verified!

} // verus!
