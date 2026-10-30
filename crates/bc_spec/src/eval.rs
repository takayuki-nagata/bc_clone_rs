// SPDX-License-Identifier: MIT

//! The evaluator (`bc_core::eval::Evaluator`): state, scopes, expressions, statements and
//! function calls.
//!
//! Variables and arrays are association lists from a name to its scope stack (the last entry
//! is the innermost frame); a name gets its global frame (0, or an empty array) when first
//! used, as in production. Functions keep the arena of the unit that defined them. Every
//! evaluation and execution step counts against `max_depth` like `Evaluator::enter_eval`, and
//! every function takes `fuel` like the parser (`ER::err.out_of_fuel`).

use crate::convert::*;
use crate::num::*;
use crate::output::*;
use crate::parser::*;
use crate::power::*;
use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

exec_spec_verified! {

pub struct VarBind {
    pub name: Seq<u8>,
    pub stack: Seq<Num>,
}

pub struct Elem {
    pub idx: u32,
    pub val: Num,
}

/// One frame of an array: its set elements (unset elements are 0).
pub struct ArrFrame {
    pub elems: Seq<Elem>,
}

pub struct ArrBind {
    pub name: Seq<u8>,
    pub stack: Seq<ArrFrame>,
}

/// A defined function, with the arena of the unit that defined it.
pub struct Func {
    pub name: Seq<u8>,
    pub params: Seq<Param>,
    pub autos: Seq<Param>,
    pub body: Seq<usize>,
    pub nodes: Seq<Node>,
}

pub struct EState {
    pub vars: Seq<VarBind>,
    pub arrays: Seq<ArrBind>,
    pub funcs: Seq<Func>,
    pub scale: u32,
    pub ibase: u32,
    pub obase: u32,
    pub out: Seq<u8>,
    pub err: Seq<u8>,
    pub col: u64,
    pub brk: bool,
    pub ret: bool,
    pub ret_val: Num,
    /// Names of the executing functions, innermost last.
    pub calls: Seq<Seq<u8>>,
    pub depth: u64,
    pub max_depth: u64,
    /// `invocation_ibase`: `Some(inv_ibase)` inside a function.
    pub has_inv: bool,
    pub inv_ibase: u32,
}

/// A runtime error: its message, and the function it is attributed to (`(main)` if none).
pub struct RErr {
    pub out_of_fuel: bool,
    pub msg: Seq<u8>,
    pub has_func: bool,
    pub func: Seq<u8>,
}

/// The result of evaluating or executing: the state after it and, for an expression, its value.
pub struct ER {
    pub ok: bool,
    pub err: RErr,
    pub st: EState,
    pub val: Num,
}

// ---------------------------------------------------------------------------------------------
// Messages
// ---------------------------------------------------------------------------------------------

/// `Divide by zero`
pub open spec fn msg_divide_by_zero() -> Seq<u8> { seq![68u8, 105, 118, 105, 100, 101, 32, 98, 121, 32, 122, 101, 114, 111] }
/// `divide by zero` (zero to a negative power)
pub open spec fn msg_negative_power_of_zero() -> Seq<u8> { seq![100u8, 105, 118, 105, 100, 101, 32, 98, 121, 32, 122, 101, 114, 111] }
/// `Modulo by zero`
pub open spec fn msg_modulo_by_zero() -> Seq<u8> { seq![77u8, 111, 100, 117, 108, 111, 32, 98, 121, 32, 122, 101, 114, 111] }
/// `Square root of a negative number`
pub open spec fn msg_negative_sqrt() -> Seq<u8> { seq![83u8, 113, 117, 97, 114, 101, 32, 114, 111, 111, 116, 32, 111, 102, 32, 97, 32, 110, 101, 103, 97, 116, 105, 118, 101, 32, 110, 117, 109, 98, 101, 114] }
/// `exponent too large in raise`
pub open spec fn msg_exponent_too_large() -> Seq<u8> { seq![101u8, 120, 112, 111, 110, 101, 110, 116, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 32, 105, 110, 32, 114, 97, 105, 115, 101] }
/// `scale too large`
pub open spec fn msg_scale_too_large() -> Seq<u8> { seq![115u8, 99, 97, 108, 101, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101] }
/// `nesting too deep`
pub open spec fn msg_nesting_too_deep() -> Seq<u8> { seq![110u8, 101, 115, 116, 105, 110, 103, 32, 116, 111, 111, 32, 100, 101, 101, 112] }
/// `Parameter number mismatch`
pub open spec fn msg_parameter_mismatch() -> Seq<u8> { seq![80u8, 97, 114, 97, 109, 101, 116, 101, 114, 32, 110, 117, 109, 98, 101, 114, 32, 109, 105, 115, 109, 97, 116, 99, 104] }
/// `Function <name> not defined.`
pub open spec fn msg_undefined_function(name: Seq<u8>) -> Seq<u8> { seq![70u8, 117, 110, 99, 116, 105, 111, 110, 32].add(name).add(seq![32u8, 110, 111, 116, 32, 100, 101, 102, 105, 110, 101, 100, 46]) }
/// `Parameter type mismatch parameter <name>.`
pub open spec fn msg_parameter_type(name: Seq<u8>) -> Seq<u8> { seq![80u8, 97, 114, 97, 109, 101, 116, 101, 114, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32].add(name).add(seq![46u8]) }
/// `Array <name> subscript out of bounds.`
pub open spec fn msg_subscript(name: Seq<u8>) -> Seq<u8> { seq![65u8, 114, 114, 97, 121, 32].add(name).add(seq![32u8, 115, 117, 98, 115, 99, 114, 105, 112, 116, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 46]) }

pub open spec fn num_err_msg(e: NumErr) -> Seq<u8> {
    match e {
        NumErr::DivideByZero => msg_divide_by_zero(),
        NumErr::ModuloByZero => msg_modulo_by_zero(),
        NumErr::NegativePowerOfZero => msg_negative_power_of_zero(),
        NumErr::ExponentTooLarge => msg_exponent_too_large(),
        NumErr::ScaleTooLarge => msg_scale_too_large(),
        NumErr::NegativeSqrt => msg_negative_sqrt(),
    }
}

/// The name of the innermost executing function, or `(main)`.
pub open spec fn current_func(st: EState) -> Seq<u8> {
    if st.calls.len() > 0 { st.calls[st.calls.len() - 1] } else { seq![40u8, 109, 97, 105, 110, 41] }
}

// ---------------------------------------------------------------------------------------------
// Results and state updates
// ---------------------------------------------------------------------------------------------

pub open spec fn zero_num() -> Num {
    Num { neg: false, mag: seq![], scale: 0u32 }
}

pub open spec fn num_u64(x: u64) -> Num {
    Num { neg: false, mag: u64_mag(x), scale: 0u32 }
}

pub open spec fn no_rerr() -> RErr {
    RErr { out_of_fuel: false, msg: seq![], has_func: false, func: seq![] }
}

pub open spec fn er_ok(st: EState, val: Num) -> ER {
    ER { ok: true, err: no_rerr(), st: st, val: val }
}

pub open spec fn er_err(st: EState, msg: Seq<u8>) -> ER {
    ER { ok: false, err: RErr { out_of_fuel: false, msg: msg, has_func: false, func: seq![] }, st: st, val: zero_num() }
}

pub open spec fn er_fuel(st: EState) -> ER {
    ER { ok: false, err: RErr { out_of_fuel: true, msg: seq![], has_func: false, func: seq![] }, st: st, val: zero_num() }
}

pub open spec fn with_vars(st: EState, vars: Seq<VarBind>) -> EState {
    EState { vars: vars, arrays: st.arrays, funcs: st.funcs, scale: st.scale, ibase: st.ibase, obase: st.obase, out: st.out, err: st.err, col: st.col, brk: st.brk, ret: st.ret, ret_val: st.ret_val, calls: st.calls, depth: st.depth, max_depth: st.max_depth, has_inv: st.has_inv, inv_ibase: st.inv_ibase }
}

pub open spec fn with_arrays(st: EState, arrays: Seq<ArrBind>) -> EState {
    EState { vars: st.vars, arrays: arrays, funcs: st.funcs, scale: st.scale, ibase: st.ibase, obase: st.obase, out: st.out, err: st.err, col: st.col, brk: st.brk, ret: st.ret, ret_val: st.ret_val, calls: st.calls, depth: st.depth, max_depth: st.max_depth, has_inv: st.has_inv, inv_ibase: st.inv_ibase }
}

pub open spec fn with_funcs(st: EState, funcs: Seq<Func>) -> EState {
    EState { vars: st.vars, arrays: st.arrays, funcs: funcs, scale: st.scale, ibase: st.ibase, obase: st.obase, out: st.out, err: st.err, col: st.col, brk: st.brk, ret: st.ret, ret_val: st.ret_val, calls: st.calls, depth: st.depth, max_depth: st.max_depth, has_inv: st.has_inv, inv_ibase: st.inv_ibase }
}

pub open spec fn with_regs(st: EState, scale: u32, ibase: u32, obase: u32) -> EState {
    EState { vars: st.vars, arrays: st.arrays, funcs: st.funcs, scale: scale, ibase: ibase, obase: obase, out: st.out, err: st.err, col: st.col, brk: st.brk, ret: st.ret, ret_val: st.ret_val, calls: st.calls, depth: st.depth, max_depth: st.max_depth, has_inv: st.has_inv, inv_ibase: st.inv_ibase }
}

pub open spec fn with_out(st: EState, out: Seq<u8>, col: u64) -> EState {
    EState { vars: st.vars, arrays: st.arrays, funcs: st.funcs, scale: st.scale, ibase: st.ibase, obase: st.obase, out: out, err: st.err, col: col, brk: st.brk, ret: st.ret, ret_val: st.ret_val, calls: st.calls, depth: st.depth, max_depth: st.max_depth, has_inv: st.has_inv, inv_ibase: st.inv_ibase }
}

pub open spec fn with_err(st: EState, err: Seq<u8>) -> EState {
    EState { vars: st.vars, arrays: st.arrays, funcs: st.funcs, scale: st.scale, ibase: st.ibase, obase: st.obase, out: st.out, err: err, col: st.col, brk: st.brk, ret: st.ret, ret_val: st.ret_val, calls: st.calls, depth: st.depth, max_depth: st.max_depth, has_inv: st.has_inv, inv_ibase: st.inv_ibase }
}

pub open spec fn with_flags(st: EState, brk: bool, ret: bool, ret_val: Num) -> EState {
    EState { vars: st.vars, arrays: st.arrays, funcs: st.funcs, scale: st.scale, ibase: st.ibase, obase: st.obase, out: st.out, err: st.err, col: st.col, brk: brk, ret: ret, ret_val: ret_val, calls: st.calls, depth: st.depth, max_depth: st.max_depth, has_inv: st.has_inv, inv_ibase: st.inv_ibase }
}

pub open spec fn with_depth(st: EState, depth: u64) -> EState {
    EState { vars: st.vars, arrays: st.arrays, funcs: st.funcs, scale: st.scale, ibase: st.ibase, obase: st.obase, out: st.out, err: st.err, col: st.col, brk: st.brk, ret: st.ret, ret_val: st.ret_val, calls: st.calls, depth: depth, max_depth: st.max_depth, has_inv: st.has_inv, inv_ibase: st.inv_ibase }
}

pub open spec fn with_call(st: EState, calls: Seq<Seq<u8>>, has_inv: bool, inv_ibase: u32) -> EState {
    EState { vars: st.vars, arrays: st.arrays, funcs: st.funcs, scale: st.scale, ibase: st.ibase, obase: st.obase, out: st.out, err: st.err, col: st.col, brk: st.brk, ret: st.ret, ret_val: st.ret_val, calls: calls, depth: st.depth, max_depth: st.max_depth, has_inv: has_inv, inv_ibase: inv_ibase }
}

/// Writes to standard output through the wrapping writer.
pub open spec fn print(st: EState, s: Seq<u8>) -> EState {
    let w = write_wrapped(st.out, st.col, s);
    with_out(st, w.0, w.1)
}

/// `Runtime warning (func=<f>): <msg>` on standard error.
pub open spec fn warn(st: EState, msg: Seq<u8>) -> EState {
    with_err(st, st.err.add(seq![82u8, 117, 110, 116, 105, 109, 101, 32, 119, 97, 114, 110, 105, 110, 103, 32, 40, 102, 117, 110, 99, 61]).add(current_func(st)).add(seq![41u8, 58, 32]).add(msg).push(10u8))
}

// ---------------------------------------------------------------------------------------------
// Variables and arrays
// ---------------------------------------------------------------------------------------------

/// The innermost value of variable `name` (0 if it has none).
pub open spec fn var_get(vars: Seq<VarBind>, name: Seq<u8>) -> Num
    decreases vars.len()
{
    if vars.len() == 0 { zero_num() }
    else if vars[0].name == name {
        let s = vars[0].stack;
        if s.len() > 0 { s[s.len() - 1] } else { zero_num() }
    } else { var_get(vars.drop_first(), name) }
}

/// The new stack of a variable after `op` (0 set the top, 1 push, 2 pop) with `v`.
pub open spec fn stack_op(s: Seq<Num>, op: u8, v: Num) -> Seq<Num> {
    if op == 0 {
        if s.len() > 0 { s.drop_last().push(v) } else { s.push(v) }
    } else if op == 1 {
        s.push(v)
    } else {
        if s.len() > 0 { s.drop_last() } else { s }
    }
}

/// Applies `stack_op` to variable `name`, after the bindings `acc`; a new name starts with its
/// global frame 0 (so setting it gives `[v]` and pushing gives `[0, v]`).
pub open spec fn var_update(vars: Seq<VarBind>, name: Seq<u8>, op: u8, v: Num, acc: Seq<VarBind>) -> Seq<VarBind>
    decreases vars.len()
{
    if vars.len() == 0 {
        if op == 2 { acc } else { acc.push(VarBind { name: name, stack: stack_op(seq![zero_num()], op, v) }) }
    } else if vars[0].name == name {
        acc.push(VarBind { name: name, stack: stack_op(vars[0].stack, op, v) }).add(vars.drop_first())
    } else {
        var_update(vars.drop_first(), name, op, v, acc.push(vars[0]))
    }
}

/// The value of element `idx` (0 if unset).
pub open spec fn elem_get(elems: Seq<Elem>, idx: u32) -> Num
    decreases elems.len()
{
    if elems.len() == 0 { zero_num() }
    else if elems[0].idx == idx { elems[0].val }
    else { elem_get(elems.drop_first(), idx) }
}

/// Sets element `idx` to `v`, after the elements `acc`.
pub open spec fn elem_set(elems: Seq<Elem>, idx: u32, v: Num, acc: Seq<Elem>) -> Seq<Elem>
    decreases elems.len()
{
    if elems.len() == 0 { acc.push(Elem { idx: idx, val: v }) }
    else if elems[0].idx == idx { acc.push(Elem { idx: idx, val: v }).add(elems.drop_first()) }
    else { elem_set(elems.drop_first(), idx, v, acc.push(elems[0])) }
}

pub open spec fn empty_frame() -> ArrFrame {
    ArrFrame { elems: seq![] }
}

/// The innermost frame of array `name` (empty if it has none).
pub open spec fn arr_top(arrays: Seq<ArrBind>, name: Seq<u8>) -> ArrFrame
    decreases arrays.len()
{
    if arrays.len() == 0 { ArrFrame { elems: seq![] } }
    else if arrays[0].name == name {
        let s = arrays[0].stack;
        if s.len() > 0 { s[s.len() - 1] } else { ArrFrame { elems: seq![] } }
    } else { arr_top(arrays.drop_first(), name) }
}

/// The new stack of an array after `op` (0 set the top frame, 1 push, 2 pop) with `f`.
pub open spec fn frame_op(s: Seq<ArrFrame>, op: u8, f: ArrFrame) -> Seq<ArrFrame> {
    if op == 0 {
        if s.len() > 0 { s.drop_last().push(f) } else { s.push(f) }
    } else if op == 1 {
        s.push(f)
    } else {
        if s.len() > 0 { s.drop_last() } else { s }
    }
}

/// Applies `frame_op` to array `name`, after the bindings `acc`; a new name starts with its
/// empty global frame.
pub open spec fn arr_update(arrays: Seq<ArrBind>, name: Seq<u8>, op: u8, f: ArrFrame, acc: Seq<ArrBind>) -> Seq<ArrBind>
    decreases arrays.len()
{
    if arrays.len() == 0 {
        if op == 2 { acc } else { acc.push(ArrBind { name: name, stack: frame_op(seq![empty_frame()], op, f) }) }
    } else if arrays[0].name == name {
        acc.push(ArrBind { name: name, stack: frame_op(arrays[0].stack, op, f) }).add(arrays.drop_first())
    } else {
        arr_update(arrays.drop_first(), name, op, f, acc.push(arrays[0]))
    }
}

pub open spec fn set_var(st: EState, name: Seq<u8>, v: Num) -> EState {
    with_vars(st, var_update(st.vars, name, 0u8, v, seq![]))
}

pub open spec fn set_elem(st: EState, name: Seq<u8>, idx: u32, v: Num) -> EState {
    let f = arr_top(st.arrays, name);
    with_arrays(st, arr_update(st.arrays, name, 0u8, ArrFrame { elems: elem_set(f.elems, idx, v, seq![]) }, seq![]))
}

/// The function named `name`, if defined.
pub open spec fn find_func(funcs: Seq<Func>, name: Seq<u8>) -> Option<Func>
    decreases funcs.len()
{
    if funcs.len() == 0 { None }
    else if funcs[0].name == name { Some(funcs[0]) }
    else { find_func(funcs.drop_first(), name) }
}

/// Defines (or redefines) a function, after the functions `acc`.
pub open spec fn define_func(funcs: Seq<Func>, f: Func, acc: Seq<Func>) -> Seq<Func>
    decreases funcs.len()
{
    if funcs.len() == 0 { acc.push(f) }
    else if funcs[0].name == f.name { acc.push(f).add(funcs.drop_first()) }
    else { define_func(funcs.drop_first(), f, acc.push(funcs[0])) }
}

/// `Evaluator::array_index`: the subscript truncated to an integer; negative values and values
/// of at least `BC_DIM_MAX` (16777216) are errors. `(ok, index)`.
pub open spec fn array_index(v: Num) -> (bool, u32) {
    let ip = drop_mag(v.mag, v.scale);
    let neg = v.neg && !is_zero_mag(v.mag);
    if neg || cmp_mag(ip, u64_mag(16777216u64)) >= 0 { (false, 0u32) }
    else { (true, mag_to_u64(ip) as u32) }
}

// ---------------------------------------------------------------------------------------------
// Registers and constants
// ---------------------------------------------------------------------------------------------

pub open spec fn reg_get(st: EState, r: u8) -> u32 {
    if r == 0 { st.scale } else if r == 1 { st.ibase } else { st.obase }
}

pub open spec fn reg_name(r: u8) -> Seq<u8> {
    if r == 0 { seq![115u8, 99, 97, 108, 101] } else if r == 1 { seq![105u8, 98, 97, 115, 101] } else { seq![111u8, 98, 97, 115, 101] }
}

pub open spec fn reg_min(r: u8) -> u32 {
    if r == 0 { 0u32 } else { 2u32 }
}

pub open spec fn reg_max(r: u8) -> u32 {
    if r == 0 { 1000000000u32 } else if r == 1 { 16u32 } else { 2147483647u32 }
}

/// `Evaluator::store_register`: the value truncated to an integer and clamped with
/// `verified_clamp_register`, warning when clamped. The stored value is in `ER::val`.
pub open spec fn store_register(st: EState, r: u8, v: Num) -> ER {
    let m = mag_to_u64(drop_mag(v.mag, v.scale));
    let neg = v.neg && !is_zero_mag(v.mag);
    let min = reg_min(r);
    let max = reg_max(r);
    let clamped = if neg { min as u64 } else if m < min as u64 { min as u64 } else if m > max as u64 { max as u64 } else { m };
    let st2 = if neg {
        warn(st, seq![110u8, 101, 103, 97, 116, 105, 118, 101, 32].add(reg_name(r)).add(seq![44u8, 32, 115, 101, 116, 32, 116, 111, 32]).add(dec_str(min as u64)))
    } else if m < min as u64 {
        warn(st, reg_name(r).add(seq![32u8, 116, 111, 111, 32, 115, 109, 97, 108, 108, 44, 32, 115, 101, 116, 32, 116, 111, 32]).add(dec_str(min as u64)))
    } else if m > max as u64 {
        warn(st, reg_name(r).add(seq![32u8, 116, 111, 111, 32, 108, 97, 114, 103, 101, 44, 32, 115, 101, 116, 32, 116, 111, 32]).add(dec_str(max as u64)))
    } else { st };
    let c = clamped as u32;
    let st3 = if r == 0 { with_regs(st2, c, st2.ibase, st2.obase) }
        else if r == 1 { with_regs(st2, st2.scale, c, st2.obase) }
        else { with_regs(st2, st2.scale, st2.ibase, c) };
    er_ok(st3, num_u64(clamped))
}

/// The value of a constant's digit character (`0-9`, `A-F`).
pub open spec fn digit_val(c: u8) -> u8 {
    if c <= 57u8 { if c >= 48u8 { (c - 48) as u8 } else { 0u8 } } else if c >= 65u8 { (c - 55) as u8 } else { 0u8 }
}

/// The digit values of `t` up to its `.` (`want_int`) or after it.
pub open spec fn literal_digits(t: Seq<u8>, want_int: bool, seen_dot: bool, acc: Seq<u8>) -> Seq<u8>
    decreases t.len()
{
    if t.len() == 0 { acc }
    else if t[0] == 46u8 { literal_digits(t.drop_first(), want_int, true, acc) }
    else if seen_dot != want_int { literal_digits(t.drop_first(), want_int, seen_dot, acc.push(digit_val(t[0]))) }
    else { literal_digits(t.drop_first(), want_int, seen_dot, acc) }
}

/// `Evaluator::literal`: a constant in the `ibase` of the current invocation.
pub open spec fn literal(st: EState, t: Seq<u8>) -> ER {
    let ib = if st.has_inv { st.inv_ibase } else { st.ibase };
    let fs = literal_digits(t, false, false, seq![]);
    if fs.len() > 1000000000 { er_err(st, msg_scale_too_large()) }
    else {
        let ib8 = if 2 <= ib && ib <= 16 { ib as u8 } else { 10u8 };
        er_ok(st, num_from_digits(literal_digits(t, true, false, seq![]), fs, ib8))
    }
}

// ---------------------------------------------------------------------------------------------
// Arithmetic with runtime errors
// ---------------------------------------------------------------------------------------------

/// `l <op> r` for the binary operator codes of `Node::Binary` (and the operator part of
/// compound assignments), at the current `scale`.
pub open spec fn arith(st: EState, op: u8, l: Num, r: Num) -> ER {
    if op == 0 { er_ok(st, num_add(l, r)) }
    else if op == 1 { er_ok(st, num_sub(l, r)) }
    else if op == 2 { er_ok(st, num_mul(l, r, st.scale)) }
    else if op == 3 {
        if is_zero_mag(r.mag) { er_err(st, msg_divide_by_zero()) } else { er_ok(st, num_div(l, r, st.scale)) }
    } else if op == 4 {
        if is_zero_mag(r.mag) { er_err(st, msg_modulo_by_zero()) }
        else if st.scale as u64 + r.scale as u64 > 1000000000 { er_err(st, msg_scale_too_large()) }
        else { er_ok(st, num_mod(l, r, st.scale)) }
    } else {
        let st2 = if r.scale > 0 { warn(st, seq![110u8, 111, 110, 45, 122, 101, 114, 111, 32, 115, 99, 97, 108, 101, 32, 105, 110, 32, 101, 120, 112, 111, 110, 101, 110, 116]) } else { st };
        match num_pow(l, r, st2.scale) {
            NumRes::Ok(v) => er_ok(st2, v),
            NumRes::Err(e) => er_err(st2, num_err_msg(e)),
        }
    }
}

/// The relational operator codes of `Node::Rel` on the sign of `l - r`.
pub open spec fn rel_holds(op: u8, c: i8) -> bool {
    if op == 0 { c == 0 } else if op == 1 { c != 0 } else if op == 2 { c < 0 }
    else if op == 3 { c <= 0 } else if op == 4 { c > 0 } else { c >= 0 }
}

pub open spec fn negate(v: Num) -> Num {
    mk_num(!v.neg, v.mag, v.scale)
}

pub open spec fn one_num() -> Num {
    Num { neg: false, mag: seq![1u8], scale: 0u32 }
}

// ---------------------------------------------------------------------------------------------
// Assignment targets
// ---------------------------------------------------------------------------------------------

/// A resolved assignment target (`eval::Place`): `kind` 0 variable, 1 array element, 2 register.
pub struct Place {
    pub kind: u8,
    pub name: Seq<u8>,
    pub idx: u32,
    pub reg: u8,
}

pub struct PlaceR {
    pub r: ER,
    pub place: Place,
}

pub open spec fn load(st: EState, p: Place) -> Num {
    if p.kind == 0 { var_get(st.vars, p.name) }
    else if p.kind == 1 { elem_get(arr_top(st.arrays, p.name).elems, p.idx) }
    else { num_u64(reg_get(st, p.reg) as u64) }
}

/// `Evaluator::store`: the value now held in `ER::val` (registers clamp it).
pub open spec fn store(st: EState, p: Place, v: Num) -> ER {
    if p.kind == 0 { er_ok(set_var(st, p.name, v), v) }
    else if p.kind == 1 { er_ok(set_elem(st, p.name, p.idx, v), v) }
    else { store_register(st, p.reg, v) }
}

/// `Evaluator::resolve_place`: evaluates an array subscript once.
pub open spec fn resolve(nodes: Seq<Node>, n: usize, st: EState, fuel: u64) -> PlaceR
    decreases fuel
{
    let none = Place { kind: 0u8, name: seq![], idx: 0u32, reg: 0u8 };
    if fuel == 0 { PlaceR { r: er_fuel(st), place: none } }
    else if n >= nodes.len() { PlaceR { r: er_ok(st, zero_num()), place: none } }
    else {
        match nodes[n as int] {
            Node::Var(name) => PlaceR { r: er_ok(st, zero_num()), place: Place { kind: 0u8, name: name, idx: 0u32, reg: 0u8 } },
            Node::Reg(r) => PlaceR { r: er_ok(st, zero_num()), place: Place { kind: 2u8, name: seq![], idx: 0u32, reg: r } },
            Node::Array(name, i) => {
                let x = ev(nodes, i, st, (fuel - 1) as u64);
                if !x.ok { PlaceR { r: x, place: none } }
                else {
                    let ai = array_index(x.val);
                    if !ai.0 { PlaceR { r: er_err(x.st, msg_subscript(name)), place: none } }
                    else { PlaceR { r: er_ok(x.st, zero_num()), place: Place { kind: 1u8, name: name, idx: ai.1, reg: 0u8 } } }
                }
            },
            _ => PlaceR { r: er_ok(st, zero_num()), place: none },
        }
    }
}

/// `verified_hex_char_val`.
pub open spec fn hex_val(c: u8) -> u64 {
    if 48 <= c && c <= 57 { (c - 48) as u64 }
    else if 65 <= c && c <= 70 { (c - 55) as u64 }
    else if 97 <= c && c <= 102 { (c - 87) as u64 }
    else { 0u64 }
}

/// Whether `ibase = D` / `obase = D` assigns a single-digit constant, read as hexadecimal.
pub open spec fn single_digit_base(nodes: Seq<Node>, p: Place, op: u8, value: usize) -> bool {
    p.kind == 2 && (p.reg == 1 || p.reg == 2) && op == 0 && value < nodes.len()
        && match nodes[value as int] { Node::Number(t) => t.len() == 1, _ => false }
}

pub open spec fn number_text(nodes: Seq<Node>, value: usize) -> Seq<u8> {
    if value < nodes.len() { match nodes[value as int] { Node::Number(t) => t, _ => seq![] } } else { seq![] }
}

// ---------------------------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------------------------

/// `Evaluator::try_evaluate`: one nesting level around `ev_node`.
pub open spec fn ev(nodes: Seq<Node>, n: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else if !within(st.depth, 1u64, st.max_depth) { er_err(st, msg_nesting_too_deep()) }
    else {
        let r = ev_node(nodes, n, with_depth(st, (st.depth + 1) as u64), (fuel - 1) as u64);
        if !r.ok { r } else { er_ok(with_depth(r.st, st.depth), r.val) }
    }
}

/// `Evaluator::evaluate_node`.
pub open spec fn ev_node(nodes: Seq<Node>, n: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else if n >= nodes.len() { er_ok(st, zero_num()) }
    else {
        let f = (fuel - 1) as u64;
        match nodes[n as int] {
            Node::Number(t) => literal(st, t),
            Node::Var(name) => er_ok(st, var_get(st.vars, name)),
            Node::Array(name, i) => ev_array(nodes, name, i, st, f),
            Node::Reg(r) => er_ok(st, num_u64(reg_get(st, r) as u64)),
            Node::Neg(e) => ev_unary(nodes, 0u8, e, st, f),
            Node::Binary(op, l, r) => ev_binary(nodes, op, l, r, st, f),
            Node::Rel(op, l, r) => ev_rel(nodes, op, l, r, st, f),
            Node::Assign(op, t, v) => ev_assign(nodes, op, t, v, st, f),
            Node::Update(is_inc, prefix, t) => ev_update(nodes, is_inc, prefix, t, st, f),
            Node::Call(name, args) => ev_call(nodes, name, args, st, f),
            Node::Length(e) => ev_unary(nodes, 1u8, e, st, f),
            Node::Sqrt(e) => ev_unary(nodes, 2u8, e, st, f),
            Node::ScaleOf(e) => ev_unary(nodes, 3u8, e, st, f),
            Node::Paren(e) => ev(nodes, e, st, f),
            _ => er_ok(st, zero_num()),
        }
    }
}

/// `-e` (0), `length(e)` (1), `sqrt(e)` (2) and `scale(e)` (3).
pub open spec fn ev_unary(nodes: Seq<Node>, which: u8, e: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let x = ev(nodes, e, st, (fuel - 1) as u64);
        if !x.ok { x }
        else if which == 0 { er_ok(x.st, negate(x.val)) }
        else if which == 1 { er_ok(x.st, num_length(x.val)) }
        else if which == 3 { er_ok(x.st, num_scale(x.val)) }
        else {
            match num_sqrt(x.val, x.st.scale) {
                NumRes::Ok(v) => er_ok(x.st, v),
                NumRes::Err(e) => er_err(x.st, num_err_msg(e)),
            }
        }
    }
}

pub open spec fn ev_array(nodes: Seq<Node>, name: Seq<u8>, i: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let x = ev(nodes, i, st, (fuel - 1) as u64);
        if !x.ok { x } else {
            let ai = array_index(x.val);
            if !ai.0 { er_err(x.st, msg_subscript(name)) }
            else { er_ok(x.st, elem_get(arr_top(x.st.arrays, name).elems, ai.1)) }
        }
    }
}

pub open spec fn ev_binary(nodes: Seq<Node>, op: u8, l: usize, r: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let a = ev(nodes, l, st, (fuel - 1) as u64);
        if !a.ok { a } else {
            let b = ev(nodes, r, a.st, (fuel - 1) as u64);
            if !b.ok { b } else { arith(b.st, op, a.val, b.val) }
        }
    }
}

pub open spec fn ev_rel(nodes: Seq<Node>, op: u8, l: usize, r: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let a = ev(nodes, l, st, (fuel - 1) as u64);
        if !a.ok { a } else {
            let b = ev(nodes, r, a.st, (fuel - 1) as u64);
            if !b.ok { b }
            else if rel_holds(op, num_cmp(a.val, b.val)) { er_ok(b.st, one_num()) }
            else { er_ok(b.st, zero_num()) }
        }
    }
}

/// An assignment: the target is resolved before the right-hand side is evaluated; its value is
/// the value assigned (even when a register clamps it).
pub open spec fn ev_assign(nodes: Seq<Node>, op: u8, t: usize, v: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let pr = resolve(nodes, t, st, f);
        if !pr.r.ok { pr.r }
        else {
            let p = pr.place;
            let x = if single_digit_base(nodes, p, op, v) {
                let txt = number_text(nodes, v);
                er_ok(pr.r.st, num_u64(hex_val(if txt.len() > 0 { txt[0] } else { 0u8 })))
            } else if op == 0 {
                ev(nodes, v, pr.r.st, f)
            } else {
                let old = load(pr.r.st, p);
                let rhs = ev(nodes, v, pr.r.st, f);
                if !rhs.ok { rhs } else { arith(rhs.st, (op - 1) as u8, old, rhs.val) }
            };
            if !x.ok { x } else {
                let s = store(x.st, p, x.val);
                er_ok(s.st, x.val)
            }
        }
    }
}

/// `++` / `--`: a prefix form gives the stored value, a postfix form the old one.
pub open spec fn ev_update(nodes: Seq<Node>, is_inc: bool, prefix: bool, t: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let pr = resolve(nodes, t, st, (fuel - 1) as u64);
        if !pr.r.ok { pr.r }
        else {
            let old = load(pr.r.st, pr.place);
            let new = if is_inc { num_add(old, one_num()) } else { num_sub(old, one_num()) };
            let s = store(pr.r.st, pr.place, new);
            if prefix { s } else { er_ok(s.st, old) }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Function calls
// ---------------------------------------------------------------------------------------------

/// An evaluated argument: an array frame (copied) or a value, for parameter `name`.
pub struct ArgVal {
    pub is_array: bool,
    pub name: Seq<u8>,
    pub val: Num,
    pub frame: ArrFrame,
}

pub struct ArgsR {
    pub r: ER,
    pub vals: Seq<ArgVal>,
}

/// Evaluates the arguments `args` for the parameters `params` (same length) in order, after
/// the values `acc`, checking that array parameters get arrays and the others expressions.
pub open spec fn ev_args(nodes: Seq<Node>, args: Seq<Arg>, params: Seq<Param>, st: EState, acc: Seq<ArgVal>, fuel: u64) -> ArgsR
    decreases fuel
{
    if fuel == 0 { ArgsR { r: er_fuel(st), vals: acc } }
    else if args.len() == 0 || params.len() == 0 { ArgsR { r: er_ok(st, zero_num()), vals: acc } }
    else {
        let a = args[0];
        let p = params[0];
        if p.is_array != a.is_array {
            ArgsR { r: er_err(st, msg_parameter_type(p.name)), vals: acc }
        } else if p.is_array {
            let v = ArgVal { is_array: true, name: p.name, val: zero_num(), frame: arr_top(st.arrays, a.name) };
            ev_args(nodes, args.drop_first(), params.drop_first(), st, acc.push(v), (fuel - 1) as u64)
        } else {
            let x = ev(nodes, a.expr, st, (fuel - 1) as u64);
            if !x.ok { ArgsR { r: x, vals: acc } }
            else {
                let v = ArgVal { is_array: false, name: p.name, val: x.val, frame: empty_frame() };
                ev_args(nodes, args.drop_first(), params.drop_first(), x.st, acc.push(v), (fuel - 1) as u64)
            }
        }
    }
}

/// Pushes the parameter frames, in order.
pub open spec fn push_args(st: EState, vals: Seq<ArgVal>) -> EState
    decreases vals.len()
{
    if vals.len() == 0 { st }
    else {
        let v = vals[0];
        let st2 = if v.is_array { with_arrays(st, arr_update(st.arrays, v.name, 1u8, v.frame, seq![])) }
            else { with_vars(st, var_update(st.vars, v.name, 1u8, v.val, seq![])) };
        push_args(st2, vals.drop_first())
    }
}

/// Pushes the `auto` frames (0, or an empty array), in order.
pub open spec fn push_autos(st: EState, autos: Seq<Param>) -> EState
    decreases autos.len()
{
    if autos.len() == 0 { st }
    else {
        let a = autos[0];
        let st2 = if a.is_array { with_arrays(st, arr_update(st.arrays, a.name, 1u8, empty_frame(), seq![])) }
            else { with_vars(st, var_update(st.vars, a.name, 1u8, zero_num(), seq![])) };
        push_autos(st2, autos.drop_first())
    }
}

/// Pops the frames of `ps`, last first (as `Evaluator::leave_call` does).
pub open spec fn pop_frames(st: EState, ps: Seq<Param>) -> EState
    decreases ps.len()
{
    if ps.len() == 0 { st }
    else {
        let p = ps[ps.len() - 1];
        let st2 = if p.is_array { with_arrays(st, arr_update(st.arrays, p.name, 2u8, empty_frame(), seq![])) }
            else { with_vars(st, var_update(st.vars, p.name, 2u8, zero_num(), seq![])) };
        pop_frames(st2, ps.drop_last())
    }
}

/// The caller's context saved at a call (the `saved_*` arguments of `Evaluator::leave_call`).
pub struct Saved {
    pub ret: bool,
    pub ret_val: Num,
    pub has_inv: bool,
    pub inv_ibase: u32,
}

/// `Evaluator::leave_call`: pops the call, restores the caller's return state and invocation
/// `ibase`, and pops the `auto` frames and then the parameter frames.
pub open spec fn leave_call(st: EState, f: Func, s: Saved) -> EState {
    let calls = if st.calls.len() > 0 { st.calls.drop_last() } else { st.calls };
    let st1 = with_call(st, calls, s.has_inv, s.inv_ibase);
    let st2 = with_flags(st1, st1.brk, s.ret, s.ret_val);
    pop_frames(pop_frames(st2, f.autos), f.params)
}

/// Attributes an error to function `name` unless an inner call already claimed it.
pub open spec fn in_function(e: RErr, name: Seq<u8>) -> RErr {
    if e.has_func { e } else { RErr { out_of_fuel: e.out_of_fuel, msg: e.msg, has_func: true, func: name } }
}

/// A call of a user function (`-l` is not modeled, so other names are undefined).
pub open spec fn ev_call(nodes: Seq<Node>, name: Seq<u8>, args: Seq<Arg>, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        match find_func(st.funcs, name) {
            None => er_err(st, msg_undefined_function(name)),
            Some(f) => {
                if args.len() != f.params.len() { er_err(st, msg_parameter_mismatch()) }
                else {
                    let a = ev_args(nodes, args, f.params, st, seq![], (fuel - 1) as u64);
                    if !a.r.ok { a.r } else { run_call(f, a.vals, a.r.st, (fuel - 1) as u64) }
                }
            },
        }
    }
}

/// Enters function `f` with the evaluated arguments, runs its body and leaves it.
pub open spec fn run_call(f: Func, vals: Seq<ArgVal>, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let s = Saved { ret: st.ret, ret_val: st.ret_val, has_inv: st.has_inv, inv_ibase: st.inv_ibase };
        let st1 = push_autos(push_args(st, vals), f.autos);
        let st2 = with_flags(st1, st1.brk, false, zero_num());
        let st3 = with_call(st2, st2.calls.push(f.name), true, st2.ibase);
        let r = exec_body(f.nodes, f.body, st3, (fuel - 1) as u64);
        if !r.ok {
            ER { ok: false, err: in_function(r.err, f.name), st: leave_call(r.st, f, s), val: zero_num() }
        } else {
            er_ok(leave_call(r.st, f, s), r.st.ret_val)
        }
    }
}

/// The statements of a function body, stopping after `return`.
pub open spec fn exec_body(nodes: Seq<Node>, body: Seq<usize>, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else if body.len() == 0 { er_ok(st, zero_num()) }
    else {
        let r = exec(nodes, body[0], st, (fuel - 1) as u64);
        if !r.ok { r }
        else if r.st.ret { r }
        else { exec_body(nodes, body.drop_first(), r.st, (fuel - 1) as u64) }
    }
}

// ---------------------------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------------------------

/// `Evaluator::is_assignment`: an assignment, possibly under unary minus.
pub open spec fn is_assignment(nodes: Seq<Node>, n: usize, fuel: u64) -> bool
    decreases fuel
{
    if fuel == 0 || n >= nodes.len() { false }
    else {
        match nodes[n as int] {
            Node::Assign(_, _, _) => true,
            Node::Neg(e) => is_assignment(nodes, e, (fuel - 1) as u64),
            _ => false,
        }
    }
}

/// `Evaluator::try_execute`: one nesting level around `exec_node`.
pub open spec fn exec(nodes: Seq<Node>, n: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else if !within(st.depth, 1u64, st.max_depth) { er_err(st, msg_nesting_too_deep()) }
    else {
        let r = exec_node(nodes, n, with_depth(st, (st.depth + 1) as u64), (fuel - 1) as u64);
        if !r.ok { r } else { er_ok(with_depth(r.st, st.depth), r.val) }
    }
}

/// `Evaluator::execute_node`: nothing runs while a `break` or `return` is pending.
pub open spec fn exec_node(nodes: Seq<Node>, n: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else if st.brk || st.ret || n >= nodes.len() { er_ok(st, zero_num()) }
    else {
        let f = (fuel - 1) as u64;
        match nodes[n as int] {
            Node::Block(list) => exec_list(nodes, list, st, f),
            Node::ExprStmt(e) => exec_expr_stmt(nodes, e, st, f),
            Node::Str(s) => er_ok(print(st, s), zero_num()),
            Node::Break => er_ok(with_flags(st, true, st.ret, st.ret_val), zero_num()),
            Node::Return(has_value, e) => exec_return(nodes, has_value, e, st, f),
            Node::If(c, b) => exec_if(nodes, c, b, st, f),
            Node::While(c, b) => exec_loop(nodes, c, 0usize, false, b, st, f),
            Node::For(i, c, p, b) => exec_for(nodes, i, c, p, b, st, f),
            Node::Define(name, params, autos, body) => exec_define(nodes, name, params, autos, body, st),
            _ => er_ok(st, zero_num()),
        }
    }
}

/// `return` and `return (e)`.
pub open spec fn exec_return(nodes: Seq<Node>, has_value: bool, e: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else if !has_value { er_ok(with_flags(st, st.brk, true, zero_num()), zero_num()) }
    else {
        let x = ev(nodes, e, st, (fuel - 1) as u64);
        if !x.ok { x } else { er_ok(with_flags(x.st, x.st.brk, true, x.val), zero_num()) }
    }
}

pub open spec fn exec_if(nodes: Seq<Node>, c: usize, b: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let x = ev(nodes, c, st, (fuel - 1) as u64);
        if !x.ok { x }
        else if is_zero_mag(x.val.mag) { er_ok(x.st, zero_num()) }
        else { exec(nodes, b, x.st, (fuel - 1) as u64) }
    }
}

pub open spec fn exec_for(nodes: Seq<Node>, i: usize, c: usize, p: usize, b: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let x = ev(nodes, i, st, (fuel - 1) as u64);
        if !x.ok { x } else { exec_loop(nodes, c, p, true, b, x.st, (fuel - 1) as u64) }
    }
}

/// A function definition, which takes effect when executed.
pub open spec fn exec_define(nodes: Seq<Node>, name: Seq<u8>, params: Seq<Param>, autos: Seq<Param>, body: Seq<usize>, st: EState) -> ER {
    let func = Func { name: name, params: params, autos: autos, body: body, nodes: nodes };
    er_ok(with_funcs(st, define_func(st.funcs, func, seq![])), zero_num())
}

/// The statements of a block, stopping when a `break` or `return` is pending.
pub open spec fn exec_list(nodes: Seq<Node>, list: Seq<usize>, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else if list.len() == 0 { er_ok(st, zero_num()) }
    else {
        let r = exec(nodes, list[0], st, (fuel - 1) as u64);
        if !r.ok { r }
        else if r.st.brk || r.st.ret { r }
        else { exec_list(nodes, list.drop_first(), r.st, (fuel - 1) as u64) }
    }
}

/// An expression statement: the value is printed unless it is an assignment.
pub open spec fn exec_expr_stmt(nodes: Seq<Node>, e: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let x = ev(nodes, e, st, (fuel - 1) as u64);
        if !x.ok { x }
        else if is_assignment(nodes, e, fuel) { er_ok(x.st, zero_num()) }
        else { er_ok(print(x.st, format_num(x.val, x.st.obase).push(10u8)), zero_num()) }
    }
}

/// A `while` loop (`has_post` false) or the loop of a `for` statement with post-expression
/// `post`: after the body, a pending `break` or `return` ends the loop and `break` is cleared
/// (`verified_loop_post_body_action`).
pub open spec fn exec_loop(nodes: Seq<Node>, c: usize, post: usize, has_post: bool, b: usize, st: EState, fuel: u64) -> ER
    decreases fuel
{
    if fuel == 0 { er_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let x = ev(nodes, c, st, f);
        if !x.ok { x }
        else if is_zero_mag(x.val.mag) { er_ok(x.st, zero_num()) }
        else {
            let r = exec(nodes, b, x.st, f);
            if !r.ok { r }
            else {
                let stop = r.st.brk || r.st.ret;
                let st2 = with_flags(r.st, false, r.st.ret, r.st.ret_val);
                if stop { er_ok(st2, zero_num()) }
                else if has_post {
                    let p = ev(nodes, post, st2, f);
                    if !p.ok { p } else { exec_loop(nodes, c, post, has_post, b, p.st, f) }
                } else {
                    exec_loop(nodes, c, post, has_post, b, st2, f)
                }
            }
        }
    }
}

} // exec_spec_verified!

} // verus!
