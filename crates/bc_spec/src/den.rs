// SPDX-License-Identifier: MIT

//! The big-step semantics without fuel, and the meaning of a stack of continuations, for the
//! proof of `bc_core`'s evaluator, which runs on an explicit stack instead of recursing.
//!
//! `bs_ev(nodes, n, st)` is `ev(nodes, n, st, f)` for any fuel `f` with which `ev` finishes
//! (`bc_spec::fuel` shows they are all equal), and an out-of-fuel result if there is none.
//! A frame `K` is what remains to do of one syntactic form once a sub-computation has a result:
//! `apply(k, x)`. `den(ks, x)` applies a whole stack, so `den(ks, bs_ev(nodes, n, st))` is the
//! meaning of a machine about to evaluate `n` under the frames `ks`.
//!
//! Each `lemma_step_*` shows that a form is its frame applied to its first sub-computation. A
//! machine step therefore keeps `den`, and no fuel appears in its proof. A sub-computation that
//! does not finish gives an out-of-fuel result, which every frame passes on (`lemma_den_done`),
//! so a finishing `den` has finishing parts. Compiled only under Verus.

use crate::eval::{array_index, *};
use crate::fuel::*;
use crate::num::*;
use crate::parser::*;
use crate::power::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Results without fuel
// ---------------------------------------------------------------------------------------------

pub open spec fn bs_ev(nodes: Seq<Node>, n: usize, st: EState) -> ER {
    if exists|f: u64| done(#[trigger] ev(nodes, n, st, f)) { ev(nodes, n, st, choose|f: u64| done(#[trigger] ev(nodes, n, st, f))) } else { er_fuel(st) }
}

pub proof fn lemma_bs_ev(nodes: Seq<Node>, n: usize, st: EState, f: u64)
    requires done(ev(nodes, n, st, f)),
    ensures bs_ev(nodes, n, st) == ev(nodes, n, st, f),
{
    let g = choose|f: u64| done(#[trigger] ev(nodes, n, st, f));
    if f <= g { lemma_ev_mono(nodes, n, st, f, g); } else { lemma_ev_mono(nodes, n, st, g, f); }
}

pub open spec fn bs_ev_node(nodes: Seq<Node>, n: usize, st: EState) -> ER {
    if exists|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) { ev_node(nodes, n, st, choose|f: u64| done(#[trigger] ev_node(nodes, n, st, f))) } else { er_fuel(st) }
}

pub proof fn lemma_bs_ev_node(nodes: Seq<Node>, n: usize, st: EState, f: u64)
    requires done(ev_node(nodes, n, st, f)),
    ensures bs_ev_node(nodes, n, st) == ev_node(nodes, n, st, f),
{
    let g = choose|f: u64| done(#[trigger] ev_node(nodes, n, st, f));
    if f <= g { lemma_ev_node_mono(nodes, n, st, f, g); } else { lemma_ev_node_mono(nodes, n, st, g, f); }
}

pub open spec fn bs_exec(nodes: Seq<Node>, n: usize, st: EState) -> ER {
    if exists|f: u64| done(#[trigger] exec(nodes, n, st, f)) { exec(nodes, n, st, choose|f: u64| done(#[trigger] exec(nodes, n, st, f))) } else { er_fuel(st) }
}

pub proof fn lemma_bs_exec(nodes: Seq<Node>, n: usize, st: EState, f: u64)
    requires done(exec(nodes, n, st, f)),
    ensures bs_exec(nodes, n, st) == exec(nodes, n, st, f),
{
    let g = choose|f: u64| done(#[trigger] exec(nodes, n, st, f));
    if f <= g { lemma_exec_mono(nodes, n, st, f, g); } else { lemma_exec_mono(nodes, n, st, g, f); }
}

pub open spec fn bs_exec_node(nodes: Seq<Node>, n: usize, st: EState) -> ER {
    if exists|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) { exec_node(nodes, n, st, choose|f: u64| done(#[trigger] exec_node(nodes, n, st, f))) } else { er_fuel(st) }
}

pub proof fn lemma_bs_exec_node(nodes: Seq<Node>, n: usize, st: EState, f: u64)
    requires done(exec_node(nodes, n, st, f)),
    ensures bs_exec_node(nodes, n, st) == exec_node(nodes, n, st, f),
{
    let g = choose|f: u64| done(#[trigger] exec_node(nodes, n, st, f));
    if f <= g { lemma_exec_node_mono(nodes, n, st, f, g); } else { lemma_exec_node_mono(nodes, n, st, g, f); }
}

pub open spec fn bs_loop(nodes: Seq<Node>, c: usize, p: usize, hp: bool, b: usize, st: EState) -> ER {
    if exists|f: u64| done(#[trigger] exec_loop(nodes, c, p, hp, b, st, f)) { exec_loop(nodes, c, p, hp, b, st, choose|f: u64| done(#[trigger] exec_loop(nodes, c, p, hp, b, st, f))) } else { er_fuel(st) }
}

pub proof fn lemma_bs_loop(nodes: Seq<Node>, c: usize, p: usize, hp: bool, b: usize, st: EState, f: u64)
    requires done(exec_loop(nodes, c, p, hp, b, st, f)),
    ensures bs_loop(nodes, c, p, hp, b, st) == exec_loop(nodes, c, p, hp, b, st, f),
{
    let g = choose|f: u64| done(#[trigger] exec_loop(nodes, c, p, hp, b, st, f));
    if f <= g { lemma_exec_loop_mono(nodes, c, p, hp, b, st, f, g); } else { lemma_exec_loop_mono(nodes, c, p, hp, b, st, g, f); }
}

pub open spec fn bs_body(nodes: Seq<Node>, l: Seq<usize>, st: EState) -> ER {
    if exists|f: u64| done(#[trigger] exec_body(nodes, l, st, f)) { exec_body(nodes, l, st, choose|f: u64| done(#[trigger] exec_body(nodes, l, st, f))) } else { er_fuel(st) }
}

pub proof fn lemma_bs_body(nodes: Seq<Node>, l: Seq<usize>, st: EState, f: u64)
    requires done(exec_body(nodes, l, st, f)),
    ensures bs_body(nodes, l, st) == exec_body(nodes, l, st, f),
{
    let g = choose|f: u64| done(#[trigger] exec_body(nodes, l, st, f));
    if f <= g { lemma_exec_body_mono(nodes, l, st, f, g); } else { lemma_exec_body_mono(nodes, l, st, g, f); }
}

pub open spec fn bs_list(nodes: Seq<Node>, l: Seq<usize>, st: EState) -> ER {
    if exists|f: u64| done(#[trigger] exec_list(nodes, l, st, f)) { exec_list(nodes, l, st, choose|f: u64| done(#[trigger] exec_list(nodes, l, st, f))) } else { er_fuel(st) }
}

pub proof fn lemma_bs_list(nodes: Seq<Node>, l: Seq<usize>, st: EState, f: u64)
    requires done(exec_list(nodes, l, st, f)),
    ensures bs_list(nodes, l, st) == exec_list(nodes, l, st, f),
{
    let g = choose|f: u64| done(#[trigger] exec_list(nodes, l, st, f));
    if f <= g { lemma_exec_list_mono(nodes, l, st, f, g); } else { lemma_exec_list_mono(nodes, l, st, g, f); }
}

pub open spec fn args_done(nodes: Seq<Node>, a: Seq<Arg>, p: Seq<Param>, st: EState, acc: Seq<ArgVal>, f: u64) -> bool {
    done(ev_args(nodes, a, p, st, acc, f).r)
}

pub open spec fn bs_args(nodes: Seq<Node>, a: Seq<Arg>, p: Seq<Param>, st: EState, acc: Seq<ArgVal>) -> ArgsR {
    if exists|f: u64| #[trigger] args_done(nodes, a, p, st, acc, f) { ev_args(nodes, a, p, st, acc, choose|f: u64| #[trigger] args_done(nodes, a, p, st, acc, f)) } else { ArgsR { r: er_fuel(st), vals: acc } }
}

pub proof fn lemma_bs_args(nodes: Seq<Node>, a: Seq<Arg>, p: Seq<Param>, st: EState, acc: Seq<ArgVal>, f: u64)
    requires done(ev_args(nodes, a, p, st, acc, f).r),
    ensures bs_args(nodes, a, p, st, acc) == ev_args(nodes, a, p, st, acc, f),
{
    assert(args_done(nodes, a, p, st, acc, f));
    let g = choose|f: u64| #[trigger] args_done(nodes, a, p, st, acc, f);
    if f <= g { lemma_ev_args_mono(nodes, a, p, st, acc, f, g); } else { lemma_ev_args_mono(nodes, a, p, st, acc, g, f); }
}

/// `is_assignment` with enough fuel for any expression that evaluates
/// (`lemma_is_assignment_stable`).
pub open spec fn is_asg(nodes: Seq<Node>, e: usize) -> bool {
    is_assignment(nodes, e, 0xFFFF_FFFF_FFFF_FFFFu64)
}

// ---------------------------------------------------------------------------------------------
// Frames
// ---------------------------------------------------------------------------------------------

pub enum K {
    /// The level that `ev` and `exec` add: the depth to restore.
    Depth(u64),
    /// `-e` (0), `length(e)` (1), `sqrt(e)` (2) and `scale(e)` (3).
    Unary(u8),
    BinL(Seq<Node>, u8, usize),
    BinR(u8, Num),
    RelL(Seq<Node>, u8, usize),
    RelR(u8, Num),
    ArrayIdx(Seq<u8>),
    /// The subscript of the target of an assignment `(nodes, name, op, value)`.
    AssignIdx(Seq<Node>, Seq<u8>, u8, usize),
    /// The subscript of the target of `++`/`--`.
    UpdateIdx(Seq<u8>, bool, bool),
    /// The value of `=`.
    Store(Place),
    /// The value of `op=`: the operator and the old value.
    OpStore(Place, u8, Num),
    /// The value argument for parameter `name`: `(nodes, function, rest of the arguments, rest of
    /// the parameters, name, values so far)`.
    ArgVal(Seq<Node>, Func, Seq<Arg>, Seq<Param>, Seq<u8>, Seq<ArgVal>),
    /// A running function body, and the arena of its caller.
    Call(Func, Saved, Seq<Node>),
    Body(Seq<Node>, Seq<usize>),
    List(Seq<Node>, Seq<usize>),
    /// An expression statement.
    ExprStmt(Seq<Node>, usize),
    Return,
    IfCond(Seq<Node>, usize),
    ForInit(Seq<Node>, usize, usize, usize),
    LoopCond(Seq<Node>, usize, usize, bool, usize),
    LoopBody(Seq<Node>, usize, usize, bool, usize),
    LoopPost(Seq<Node>, usize, usize, bool, usize),
}

pub open spec fn saved_of(st: EState) -> Saved {
    Saved { ret: st.ret, ret_val: st.ret_val, has_inv: st.has_inv, inv_ibase: st.inv_ibase }
}

/// The state in which the body of `f` starts.
pub open spec fn enter(f: Func, vals: Seq<ArgVal>, st: EState) -> EState {
    let st1 = push_autos(push_args(st, vals), f.autos);
    let st2 = with_flags(st1, st1.brk, false, zero_num());
    with_call(st2, st2.calls.push(f.name), true, st2.ibase)
}

pub open spec fn leave(f: Func, s: Saved, x: ER) -> ER {
    if !x.ok { ER { ok: false, err: in_function(x.err, f.name), st: leave_call(x.st, f, s), val: zero_num() } }
    else { er_ok(leave_call(x.st, f, s), x.st.ret_val) }
}

/// The rest of a call once its arguments are known.
pub open spec fn after_args(f: Func, a: ArgsR) -> ER {
    if !a.r.ok { a.r } else { leave(f, saved_of(a.r.st), bs_body(f.nodes, f.body, enter(f, a.vals, a.r.st))) }
}

pub open spec fn bin_r(op: u8, a: Num, x: ER) -> ER {
    if !x.ok { x } else { arith(x.st, op, a, x.val) }
}

pub open spec fn rel_r(op: u8, a: Num, x: ER) -> ER {
    if !x.ok { x }
    else if rel_holds(op, num_cmp(a, x.val)) { er_ok(x.st, one_num()) }
    else { er_ok(x.st, zero_num()) }
}

pub open spec fn store_k(p: Place, x: ER) -> ER {
    if !x.ok { x } else {
        let s = store(x.st, p, x.val);
        er_ok(s.st, x.val)
    }
}

pub open spec fn op_store(p: Place, op: u8, old: Num, x: ER) -> ER {
    store_k(p, bin_r(op, old, x))
}

/// An assignment once its target is known.
pub open spec fn assign_to(nodes: Seq<Node>, op: u8, v: usize, p: Place, st: EState) -> ER {
    if single_digit_base(nodes, p, op, v) {
        let txt = number_text(nodes, v);
        store_k(p, er_ok(st, num_u64(hex_val(if txt.len() > 0 { txt[0] } else { 0u8 }))))
    } else if op == 0 {
        store_k(p, bs_ev(nodes, v, st))
    } else {
        op_store(p, (op - 1) as u8, load(st, p), bs_ev(nodes, v, st))
    }
}

/// `++`/`--` once its target is known.
pub open spec fn update_at(is_inc: bool, prefix: bool, p: Place, st: EState) -> ER {
    let old = load(st, p);
    let new = if is_inc { num_add(old, one_num()) } else { num_sub(old, one_num()) };
    let s = store(st, p, new);
    if prefix { s } else { er_ok(s.st, old) }
}

pub open spec fn elem_place(name: Seq<u8>, x: ER) -> Place {
    Place { kind: 1u8, name: name, idx: array_index(x.val).1, reg: 0u8 }
}

pub open spec fn loop_body(nodes: Seq<Node>, c: usize, p: usize, hp: bool, b: usize, r: ER) -> ER {
    if !r.ok { r }
    else {
        let st2 = with_flags(r.st, false, r.st.ret, r.st.ret_val);
        if r.st.brk || r.st.ret { er_ok(st2, zero_num()) }
        else if hp { let q = bs_ev(nodes, p, st2); if !q.ok { q } else { bs_loop(nodes, c, p, hp, b, q.st) } }
        else { bs_loop(nodes, c, p, hp, b, st2) }
    }
}

pub open spec fn loop_cond(nodes: Seq<Node>, c: usize, p: usize, hp: bool, b: usize, x: ER) -> ER {
    if !x.ok { x }
    else if is_zero_mag(x.val.mag) { er_ok(x.st, zero_num()) }
    else { loop_body(nodes, c, p, hp, b, bs_exec(nodes, b, x.st)) }
}

/// What a frame does with the result of its sub-computation.
pub open spec fn apply(k: K, x: ER) -> ER {
    match k {
        K::Depth(d) => if !x.ok { x } else { er_ok(with_depth(x.st, d), x.val) },
        K::Unary(which) => if !x.ok { x }
            else if which == 0 { er_ok(x.st, negate(x.val)) }
            else if which == 1 { er_ok(x.st, crate::convert::num_length(x.val)) }
            else if which == 3 { er_ok(x.st, crate::convert::num_scale(x.val)) }
            else {
                match num_sqrt(x.val, x.st.scale) {
                    NumRes::Ok(v) => er_ok(x.st, v),
                    NumRes::Err(e) => er_err(x.st, num_err_msg(e)),
                }
            },
        K::BinL(nodes, op, r) => if !x.ok { x } else { bin_r(op, x.val, bs_ev(nodes, r, x.st)) },
        K::BinR(op, a) => bin_r(op, a, x),
        K::RelL(nodes, op, r) => if !x.ok { x } else { rel_r(op, x.val, bs_ev(nodes, r, x.st)) },
        K::RelR(op, a) => rel_r(op, a, x),
        K::ArrayIdx(name) => if !x.ok { x } else {
            let ai = array_index(x.val);
            if !ai.0 { er_err(x.st, msg_subscript(name)) }
            else { er_ok(x.st, elem_get(arr_top(x.st.arrays, name).elems, ai.1)) }
        },
        K::AssignIdx(nodes, name, op, v) => if !x.ok { x }
            else if !array_index(x.val).0 { er_err(x.st, msg_subscript(name)) }
            else { assign_to(nodes, op, v, elem_place(name, x), x.st) },
        K::UpdateIdx(name, is_inc, prefix) => if !x.ok { x }
            else if !array_index(x.val).0 { er_err(x.st, msg_subscript(name)) }
            else { update_at(is_inc, prefix, elem_place(name, x), x.st) },
        K::Store(p) => store_k(p, x),
        K::OpStore(p, op, old) => op_store(p, op, old, x),
        K::ArgVal(nodes, f, a, p, name, acc) => if !x.ok { x } else {
            let v = ArgVal { is_array: false, name: name, val: x.val, frame: empty_frame() };
            after_args(f, bs_args(nodes, a, p, x.st, acc.push(v)))
        },
        K::Call(f, s, _) => leave(f, s, x),
        K::Body(nodes, rest) => if !x.ok { x } else if x.st.ret { x } else { bs_body(nodes, rest, x.st) },
        K::List(nodes, rest) => if !x.ok { x } else if x.st.brk || x.st.ret { x } else { bs_list(nodes, rest, x.st) },
        K::ExprStmt(nodes, e) => if !x.ok { x }
            else if is_asg(nodes, e) { er_ok(x.st, zero_num()) }
            else { er_ok(print(x.st, format_num_nl(x)), zero_num()) },
        K::Return => if !x.ok { x } else { er_ok(with_flags(x.st, x.st.brk, true, x.val), zero_num()) },
        K::IfCond(nodes, b) => if !x.ok { x }
            else if is_zero_mag(x.val.mag) { er_ok(x.st, zero_num()) }
            else { bs_exec(nodes, b, x.st) },
        K::ForInit(nodes, c, p, b) => if !x.ok { x } else { bs_loop(nodes, c, p, true, b, x.st) },
        K::LoopCond(nodes, c, p, hp, b) => loop_cond(nodes, c, p, hp, b, x),
        K::LoopBody(nodes, c, p, hp, b) => loop_body(nodes, c, p, hp, b, x),
        K::LoopPost(nodes, c, p, hp, b) => if !x.ok { x } else { bs_loop(nodes, c, p, hp, b, x.st) },
    }
}

pub open spec fn format_num_nl(x: ER) -> Seq<u8> {
    crate::output::format_num(x.val, x.st.obase).push(10u8)
}

/// The result of the whole stack, the innermost frame last, on the result `x`.
pub open spec fn den(ks: Seq<K>, x: ER) -> ER
    decreases ks.len(),
{
    if ks.len() == 0 { x } else { den(ks.drop_last(), apply(ks.last(), x)) }
}

pub proof fn lemma_den_push(ks: Seq<K>, k: K, x: ER)
    ensures den(ks.push(k), x) == den(ks, apply(k, x)),
{
    assert(ks.push(k).drop_last() =~= ks);
}

pub proof fn lemma_apply_not_done(k: K, x: ER)
    requires !done(x),
    ensures !done(apply(k, x)),
{}

/// A stack that finishes has a finishing result under it.
pub proof fn lemma_den_done(ks: Seq<K>, x: ER)
    requires done(den(ks, x)),
    ensures done(x),
    decreases ks.len(),
{
    if ks.len() > 0 {
        lemma_den_done(ks.drop_last(), apply(ks.last(), x));
        if !done(x) { lemma_apply_not_done(ks.last(), x); }
    }
}

// ---------------------------------------------------------------------------------------------
// A form is its frame applied to its first sub-computation
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_step_ev(nodes: Seq<Node>, n: usize, st: EState)
    requires done(bs_ev(nodes, n, st)), within(st.depth, 1u64, st.max_depth),
    ensures bs_ev(nodes, n, st) == apply(K::Depth(st.depth), bs_ev_node(nodes, n, with_depth(st, (st.depth + 1) as u64))),
{
    let f = choose|f: u64| done(#[trigger] ev(nodes, n, st, f));
    assert(f > 0);
    lemma_bs_ev_node(nodes, n, with_depth(st, (st.depth + 1) as u64), (f - 1) as u64);
}

pub proof fn lemma_ev_too_deep(nodes: Seq<Node>, n: usize, st: EState)
    requires !within(st.depth, 1u64, st.max_depth),
    ensures bs_ev(nodes, n, st) == er_err(st, msg_nesting_too_deep()),
{
    lemma_bs_ev(nodes, n, st, 1);
}

pub proof fn lemma_step_exec(nodes: Seq<Node>, n: usize, st: EState)
    requires done(bs_exec(nodes, n, st)), within(st.depth, 1u64, st.max_depth),
    ensures bs_exec(nodes, n, st) == apply(K::Depth(st.depth), bs_exec_node(nodes, n, with_depth(st, (st.depth + 1) as u64))),
{
    let f = choose|f: u64| done(#[trigger] exec(nodes, n, st, f));
    assert(f > 0);
    lemma_bs_exec_node(nodes, n, with_depth(st, (st.depth + 1) as u64), (f - 1) as u64);
}

pub proof fn lemma_exec_too_deep(nodes: Seq<Node>, n: usize, st: EState)
    requires !within(st.depth, 1u64, st.max_depth),
    ensures bs_exec(nodes, n, st) == er_err(st, msg_nesting_too_deep()),
{
    lemma_bs_exec(nodes, n, st, 1);
}

/// The fuel with which a finishing node finishes.
pub proof fn lemma_ev_node_fuel(nodes: Seq<Node>, n: usize, st: EState) -> (f: u64)
    requires done(bs_ev_node(nodes, n, st)),
    ensures done(ev_node(nodes, n, st, f)), f > 0, bs_ev_node(nodes, n, st) == ev_node(nodes, n, st, f),
{
    choose|f: u64| done(#[trigger] ev_node(nodes, n, st, f))
}

pub proof fn lemma_step_unary(nodes: Seq<Node>, n: usize, which: u8, e: usize, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(),
        (which == 0 && nodes[n as int] == Node::Neg(e)) || (which == 1 && nodes[n as int] == Node::Length(e))
            || (which == 2 && nodes[n as int] == Node::Sqrt(e)) || (which == 3 && nodes[n as int] == Node::ScaleOf(e)),
    ensures bs_ev_node(nodes, n, st) == apply(K::Unary(which), bs_ev(nodes, e, st)),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    assert(ev_node(nodes, n, st, f) == ev_unary(nodes, which, e, st, (f - 1) as u64));
    assert(done(ev(nodes, e, st, (f - 2) as u64)));
    lemma_bs_ev(nodes, e, st, (f - 2) as u64);
}

pub proof fn lemma_step_paren(nodes: Seq<Node>, n: usize, e: usize, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Paren(e),
    ensures bs_ev_node(nodes, n, st) == bs_ev(nodes, e, st),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    lemma_bs_ev(nodes, e, st, (f - 1) as u64);
}

pub proof fn lemma_step_binary(nodes: Seq<Node>, n: usize, op: u8, l: usize, r: usize, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Binary(op, l, r),
    ensures bs_ev_node(nodes, n, st) == apply(K::BinL(nodes, op, r), bs_ev(nodes, l, st)),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    let g = (f - 2) as u64;
    assert(ev_node(nodes, n, st, f) == ev_binary(nodes, op, l, r, st, (f - 1) as u64));
    let a = ev(nodes, l, st, g);
    assert(done(a));
    lemma_bs_ev(nodes, l, st, g);
    if a.ok {
        assert(done(ev(nodes, r, a.st, g)));
        lemma_bs_ev(nodes, r, a.st, g);
    }
}

pub proof fn lemma_step_rel(nodes: Seq<Node>, n: usize, op: u8, l: usize, r: usize, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Rel(op, l, r),
    ensures bs_ev_node(nodes, n, st) == apply(K::RelL(nodes, op, r), bs_ev(nodes, l, st)),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    let g = (f - 2) as u64;
    assert(ev_node(nodes, n, st, f) == ev_rel(nodes, op, l, r, st, (f - 1) as u64));
    let a = ev(nodes, l, st, g);
    assert(done(a));
    lemma_bs_ev(nodes, l, st, g);
    if a.ok {
        assert(done(ev(nodes, r, a.st, g)));
        lemma_bs_ev(nodes, r, a.st, g);
    }
}

pub proof fn lemma_step_array(nodes: Seq<Node>, n: usize, name: Seq<u8>, i: usize, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Array(name, i),
    ensures bs_ev_node(nodes, n, st) == apply(K::ArrayIdx(name), bs_ev(nodes, i, st)),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    assert(ev_node(nodes, n, st, f) == ev_array(nodes, name, i, st, (f - 1) as u64));
    assert(done(ev(nodes, i, st, (f - 2) as u64)));
    lemma_bs_ev(nodes, i, st, (f - 2) as u64);
}

/// The assignment once its target resolved, with fuel.
proof fn lemma_assign_rest(nodes: Seq<Node>, op: u8, v: usize, p: Place, st: EState, g: u64)
    requires
        ({
            let x = if single_digit_base(nodes, p, op, v) {
                let txt = number_text(nodes, v);
                er_ok(st, num_u64(hex_val(if txt.len() > 0 { txt[0] } else { 0u8 })))
            } else if op == 0 { ev(nodes, v, st, g) }
            else {
                let old = load(st, p);
                let rhs = ev(nodes, v, st, g);
                if !rhs.ok { rhs } else { arith(rhs.st, (op - 1) as u8, old, rhs.val) }
            };
            done(if !x.ok { x } else { let s = store(x.st, p, x.val); er_ok(s.st, x.val) })
        }),
    ensures
        ({
            let x = if single_digit_base(nodes, p, op, v) {
                let txt = number_text(nodes, v);
                er_ok(st, num_u64(hex_val(if txt.len() > 0 { txt[0] } else { 0u8 })))
            } else if op == 0 { ev(nodes, v, st, g) }
            else {
                let old = load(st, p);
                let rhs = ev(nodes, v, st, g);
                if !rhs.ok { rhs } else { arith(rhs.st, (op - 1) as u8, old, rhs.val) }
            };
            assign_to(nodes, op, v, p, st) == if !x.ok { x } else { let s = store(x.st, p, x.val); er_ok(s.st, x.val) }
        }),
{
    if !single_digit_base(nodes, p, op, v) {
        let rhs = ev(nodes, v, st, g);
        if !done(rhs) {
            assert(false);
        }
        lemma_bs_ev(nodes, v, st, g);
    }
}

/// A target that needs no evaluation: every fuel above 0 resolves it to the same place.
pub open spec fn plain_place(nodes: Seq<Node>, t: usize) -> Place {
    let none = Place { kind: 0u8, name: seq![], idx: 0u32, reg: 0u8 };
    if t >= nodes.len() { none } else {
        match nodes[t as int] {
            Node::Var(name) => Place { kind: 0u8, name: name, idx: 0u32, reg: 0u8 },
            Node::Reg(r) => Place { kind: 2u8, name: seq![], idx: 0u32, reg: r },
            _ => none,
        }
    }
}

pub open spec fn is_subscript(nodes: Seq<Node>, t: usize) -> bool {
    t < nodes.len() && nodes[t as int] is Array
}

pub proof fn lemma_step_assign_plain(nodes: Seq<Node>, n: usize, op: u8, t: usize, v: usize, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Assign(op, t, v), !is_subscript(nodes, t),
    ensures bs_ev_node(nodes, n, st) == assign_to(nodes, op, v, plain_place(nodes, t), st),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    let g = (f - 2) as u64;
    assert(ev_node(nodes, n, st, f) == ev_assign(nodes, op, t, v, st, (f - 1) as u64));
    assert(g > 0);
    assert(resolve(nodes, t, st, g).place == plain_place(nodes, t) && resolve(nodes, t, st, g).r.st == st && resolve(nodes, t, st, g).r.ok);
    lemma_assign_rest(nodes, op, v, plain_place(nodes, t), st, g);
}

pub proof fn lemma_step_assign_elem(nodes: Seq<Node>, n: usize, op: u8, name: Seq<u8>, i: usize, t: usize, v: usize, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Assign(op, t, v), t < nodes.len(), nodes[t as int] == Node::Array(name, i),
    ensures bs_ev_node(nodes, n, st) == apply(K::AssignIdx(nodes, name, op, v), bs_ev(nodes, i, st)),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    let g = (f - 2) as u64;
    assert(ev_node(nodes, n, st, f) == ev_assign(nodes, op, t, v, st, (f - 1) as u64));
    assert(g > 0);
    let pr = resolve(nodes, t, st, g);
    let x = ev(nodes, i, st, (g - 1) as u64);
    assert(done(pr.r));
    assert(done(x));
    lemma_bs_ev(nodes, i, st, (g - 1) as u64);
    if x.ok && array_index(x.val).0 {
        assert(pr.place == elem_place(name, x) && pr.r.st == x.st);
        lemma_assign_rest(nodes, op, v, pr.place, x.st, g);
    }
}

pub proof fn lemma_step_update_plain(nodes: Seq<Node>, n: usize, is_inc: bool, prefix: bool, t: usize, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Update(is_inc, prefix, t), !is_subscript(nodes, t),
    ensures bs_ev_node(nodes, n, st) == update_at(is_inc, prefix, plain_place(nodes, t), st),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    assert(ev_node(nodes, n, st, f) == ev_update(nodes, is_inc, prefix, t, st, (f - 1) as u64));
    assert(f >= 3);
    let pr = resolve(nodes, t, st, (f - 2) as u64);
    assert(pr.place == plain_place(nodes, t) && pr.r.st == st && pr.r.ok);
}

pub proof fn lemma_step_update_elem(nodes: Seq<Node>, n: usize, is_inc: bool, prefix: bool, name: Seq<u8>, i: usize, t: usize, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Update(is_inc, prefix, t), t < nodes.len(), nodes[t as int] == Node::Array(name, i),
    ensures bs_ev_node(nodes, n, st) == apply(K::UpdateIdx(name, is_inc, prefix), bs_ev(nodes, i, st)),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    let g = (f - 2) as u64;
    assert(ev_node(nodes, n, st, f) == ev_update(nodes, is_inc, prefix, t, st, (f - 1) as u64));
    assert(g > 0);
    let pr = resolve(nodes, t, st, g);
    let x = ev(nodes, i, st, (g - 1) as u64);
    assert(done(pr.r));
    assert(done(x));
    lemma_bs_ev(nodes, i, st, (g - 1) as u64);
    if x.ok && array_index(x.val).0 {
        assert(pr.place == elem_place(name, x) && pr.r.st == x.st);
    }
}

/// The call: arguments, then the body.
pub proof fn lemma_step_call(nodes: Seq<Node>, n: usize, name: Seq<u8>, args: Seq<Arg>, st: EState, g: Func)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Call(name, args),
        find_func(st.funcs, name) == Some(g), args.len() == g.params.len(),
    ensures bs_ev_node(nodes, n, st) == after_args(g, bs_args(nodes, args, g.params, st, seq![])),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    let h = (f - 2) as u64;
    assert(ev_node(nodes, n, st, f) == ev_call(nodes, name, args, st, (f - 1) as u64));
    let a = ev_args(nodes, args, g.params, st, seq![], h);
    assert(done(a.r));
    lemma_bs_args(nodes, args, g.params, st, seq![], h);
    if a.r.ok {
        let s3 = enter(g, a.vals, a.r.st);
        assert(h > 0);
        let r = exec_body(g.nodes, g.body, s3, (h - 1) as u64);
        assert(done(r));
        lemma_bs_body(g.nodes, g.body, s3, (h - 1) as u64);
    }
}

/// A call of a function that is not defined.
pub proof fn lemma_step_call_undefined(nodes: Seq<Node>, n: usize, name: Seq<u8>, args: Seq<Arg>, st: EState)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Call(name, args), find_func(st.funcs, name) is None,
    ensures bs_ev_node(nodes, n, st) == er_err(st, msg_undefined_function(name)),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    assert(ev_node(nodes, n, st, f) == ev_call(nodes, name, args, st, (f - 1) as u64));
}

/// A call with the wrong number of arguments.
pub proof fn lemma_step_call_mismatch(nodes: Seq<Node>, n: usize, name: Seq<u8>, args: Seq<Arg>, st: EState, g: Func)
    requires done(bs_ev_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Call(name, args),
        find_func(st.funcs, name) == Some(g), args.len() != g.params.len(),
    ensures bs_ev_node(nodes, n, st) == er_err(st, msg_parameter_mismatch()),
{
    let f = lemma_ev_node_fuel(nodes, n, st);
    assert(f >= 2);
    assert(ev_node(nodes, n, st, f) == ev_call(nodes, name, args, st, (f - 1) as u64));
}

/// The value arguments are its frame applied to the first one.
pub proof fn lemma_step_arg(nodes: Seq<Node>, f: Func, a: Seq<Arg>, p: Seq<Param>, st: EState, acc: Seq<ArgVal>)
    requires done(bs_args(nodes, a, p, st, acc).r), a.len() > 0, p.len() > 0, !p[0].is_array, !a[0].is_array,
    ensures after_args(f, bs_args(nodes, a, p, st, acc)) == apply(K::ArgVal(nodes, f, a.drop_first(), p.drop_first(), p[0].name, acc), bs_ev(nodes, a[0].expr, st)),
{
    if !exists|h: u64| #[trigger] args_done(nodes, a, p, st, acc, h) {
        assert(!done(bs_args(nodes, a, p, st, acc).r));
    }
    let h = choose|h: u64| #[trigger] args_done(nodes, a, p, st, acc, h);
    assert(h >= 1);
    let g = (h - 1) as u64;
    let x = ev(nodes, a[0].expr, st, g);
    assert(done(x));
    lemma_bs_ev(nodes, a[0].expr, st, g);
    if x.ok {
        let v = ArgVal { is_array: false, name: p[0].name, val: x.val, frame: empty_frame() };
        assert(done(ev_args(nodes, a.drop_first(), p.drop_first(), x.st, acc.push(v), g).r));
        lemma_bs_args(nodes, a.drop_first(), p.drop_first(), x.st, acc.push(v), g);
    }
}

/// An array argument: a copy of the current frame, and nothing to evaluate.
pub proof fn lemma_step_arg_array(nodes: Seq<Node>, a: Seq<Arg>, p: Seq<Param>, st: EState, acc: Seq<ArgVal>)
    requires done(bs_args(nodes, a, p, st, acc).r), a.len() > 0, p.len() > 0, p[0].is_array, a[0].is_array,
    ensures bs_args(nodes, a, p, st, acc) == bs_args(nodes, a.drop_first(), p.drop_first(), st, acc.push(ArgVal { is_array: true, name: p[0].name, val: zero_num(), frame: arr_top(st.arrays, a[0].name) })),
{
    if !exists|h: u64| #[trigger] args_done(nodes, a, p, st, acc, h) {
        assert(!done(bs_args(nodes, a, p, st, acc).r));
    }
    let h = choose|h: u64| #[trigger] args_done(nodes, a, p, st, acc, h);
    assert(h >= 1);
    let v = ArgVal { is_array: true, name: p[0].name, val: zero_num(), frame: arr_top(st.arrays, a[0].name) };
    lemma_bs_args(nodes, a.drop_first(), p.drop_first(), st, acc.push(v), (h - 1) as u64);
}

/// The cases of `ev_args` that need no evaluation.
pub proof fn lemma_args_end(nodes: Seq<Node>, a: Seq<Arg>, p: Seq<Param>, st: EState, acc: Seq<ArgVal>)
    ensures
        (a.len() == 0 || p.len() == 0) ==> bs_args(nodes, a, p, st, acc) == (ArgsR { r: er_ok(st, zero_num()), vals: acc }),
        (a.len() > 0 && p.len() > 0 && p[0].is_array != a[0].is_array) ==> bs_args(nodes, a, p, st, acc) == (ArgsR { r: er_err(st, msg_parameter_type(p[0].name)), vals: acc }),
{
    if a.len() == 0 || p.len() == 0 || p[0].is_array != a[0].is_array {
        lemma_bs_args(nodes, a, p, st, acc, 1);
    }
}

pub proof fn lemma_exec_node_fuel(nodes: Seq<Node>, n: usize, st: EState) -> (f: u64)
    requires done(bs_exec_node(nodes, n, st)),
    ensures done(exec_node(nodes, n, st, f)), f > 0, bs_exec_node(nodes, n, st) == exec_node(nodes, n, st, f),
{
    choose|f: u64| done(#[trigger] exec_node(nodes, n, st, f))
}

pub proof fn lemma_step_block(nodes: Seq<Node>, n: usize, list: Seq<usize>, st: EState)
    requires done(bs_exec_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Block(list), !st.brk, !st.ret,
    ensures bs_exec_node(nodes, n, st) == bs_list(nodes, list, st),
{
    let f = lemma_exec_node_fuel(nodes, n, st);
    lemma_bs_list(nodes, list, st, (f - 1) as u64);
}

pub proof fn lemma_step_list(nodes: Seq<Node>, l: Seq<usize>, st: EState)
    requires done(bs_list(nodes, l, st)), l.len() > 0,
    ensures bs_list(nodes, l, st) == apply(K::List(nodes, l.drop_first()), bs_exec(nodes, l[0], st)),
{
    let f = choose|f: u64| done(#[trigger] exec_list(nodes, l, st, f));
    assert(f >= 1);
    let g = (f - 1) as u64;
    let r = exec(nodes, l[0], st, g);
    assert(done(r));
    lemma_bs_exec(nodes, l[0], st, g);
    if r.ok && !(r.st.brk || r.st.ret) {
        lemma_bs_list(nodes, l.drop_first(), r.st, g);
    }
}

pub proof fn lemma_list_end(nodes: Seq<Node>, l: Seq<usize>, st: EState)
    requires l.len() == 0,
    ensures bs_list(nodes, l, st) == er_ok(st, zero_num()),
{
    lemma_bs_list(nodes, l, st, 1);
}

pub proof fn lemma_step_body(nodes: Seq<Node>, l: Seq<usize>, st: EState)
    requires done(bs_body(nodes, l, st)), l.len() > 0,
    ensures bs_body(nodes, l, st) == apply(K::Body(nodes, l.drop_first()), bs_exec(nodes, l[0], st)),
{
    let f = choose|f: u64| done(#[trigger] exec_body(nodes, l, st, f));
    assert(f >= 1);
    let g = (f - 1) as u64;
    let r = exec(nodes, l[0], st, g);
    assert(done(r));
    lemma_bs_exec(nodes, l[0], st, g);
    if r.ok && !r.st.ret {
        lemma_bs_body(nodes, l.drop_first(), r.st, g);
    }
}

pub proof fn lemma_body_end(nodes: Seq<Node>, l: Seq<usize>, st: EState)
    requires l.len() == 0,
    ensures bs_body(nodes, l, st) == er_ok(st, zero_num()),
{
    lemma_bs_body(nodes, l, st, 1);
}

pub proof fn lemma_step_expr_stmt(nodes: Seq<Node>, n: usize, e: usize, st: EState)
    requires done(bs_exec_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::ExprStmt(e), !st.brk, !st.ret,
    ensures bs_exec_node(nodes, n, st) == apply(K::ExprStmt(nodes, e), bs_ev(nodes, e, st)),
{
    let f = lemma_exec_node_fuel(nodes, n, st);
    assert(f >= 2);
    let g = (f - 2) as u64;
    assert(exec_node(nodes, n, st, f) == exec_expr_stmt(nodes, e, st, (f - 1) as u64));
    let x = ev(nodes, e, st, g);
    assert(done(x));
    lemma_bs_ev(nodes, e, st, g);
    if x.ok {
        lemma_is_assignment_stable(nodes, e, st, g, 0xFFFF_FFFF_FFFF_FFFFu64, (f - 1) as u64);
    }
}

pub proof fn lemma_step_return(nodes: Seq<Node>, n: usize, e: usize, st: EState)
    requires done(bs_exec_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::Return(true, e), !st.brk, !st.ret,
    ensures bs_exec_node(nodes, n, st) == apply(K::Return, bs_ev(nodes, e, st)),
{
    let f = lemma_exec_node_fuel(nodes, n, st);
    assert(f >= 2);
    assert(exec_node(nodes, n, st, f) == exec_return(nodes, true, e, st, (f - 1) as u64));
    assert(done(ev(nodes, e, st, (f - 2) as u64)));
    lemma_bs_ev(nodes, e, st, (f - 2) as u64);
}

pub proof fn lemma_step_if(nodes: Seq<Node>, n: usize, c: usize, b: usize, st: EState)
    requires done(bs_exec_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::If(c, b), !st.brk, !st.ret,
    ensures bs_exec_node(nodes, n, st) == apply(K::IfCond(nodes, b), bs_ev(nodes, c, st)),
{
    let f = lemma_exec_node_fuel(nodes, n, st);
    assert(f >= 2);
    let g = (f - 2) as u64;
    assert(exec_node(nodes, n, st, f) == exec_if(nodes, c, b, st, (f - 1) as u64));
    let x = ev(nodes, c, st, g);
    assert(done(x));
    lemma_bs_ev(nodes, c, st, g);
    if x.ok && !is_zero_mag(x.val.mag) {
        lemma_bs_exec(nodes, b, x.st, g);
    }
}

pub proof fn lemma_step_while(nodes: Seq<Node>, n: usize, c: usize, b: usize, st: EState)
    requires done(bs_exec_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::While(c, b), !st.brk, !st.ret,
    ensures bs_exec_node(nodes, n, st) == bs_loop(nodes, c, 0usize, false, b, st),
{
    let f = lemma_exec_node_fuel(nodes, n, st);
    lemma_bs_loop(nodes, c, 0usize, false, b, st, (f - 1) as u64);
}

pub proof fn lemma_step_for(nodes: Seq<Node>, n: usize, i: usize, c: usize, p: usize, b: usize, st: EState)
    requires done(bs_exec_node(nodes, n, st)), n < nodes.len(), nodes[n as int] == Node::For(i, c, p, b), !st.brk, !st.ret,
    ensures bs_exec_node(nodes, n, st) == apply(K::ForInit(nodes, c, p, b), bs_ev(nodes, i, st)),
{
    let f = lemma_exec_node_fuel(nodes, n, st);
    assert(f >= 2);
    let g = (f - 2) as u64;
    assert(exec_node(nodes, n, st, f) == exec_for(nodes, i, c, p, b, st, (f - 1) as u64));
    let x = ev(nodes, i, st, g);
    assert(done(x));
    lemma_bs_ev(nodes, i, st, g);
    if x.ok {
        lemma_bs_loop(nodes, c, p, true, b, x.st, g);
    }
}

pub proof fn lemma_step_loop(nodes: Seq<Node>, c: usize, p: usize, hp: bool, b: usize, st: EState)
    requires done(bs_loop(nodes, c, p, hp, b, st)),
    ensures bs_loop(nodes, c, p, hp, b, st) == apply(K::LoopCond(nodes, c, p, hp, b), bs_ev(nodes, c, st)),
{
    let f = choose|f: u64| done(#[trigger] exec_loop(nodes, c, p, hp, b, st, f));
    assert(f >= 1);
    let g = (f - 1) as u64;
    let x = ev(nodes, c, st, g);
    assert(done(x));
    lemma_bs_ev(nodes, c, st, g);
    if x.ok && !is_zero_mag(x.val.mag) {
        let r = exec(nodes, b, x.st, g);
        assert(done(r));
        lemma_bs_exec(nodes, b, x.st, g);
        if r.ok && !(r.st.brk || r.st.ret) {
            let st2 = with_flags(r.st, false, r.st.ret, r.st.ret_val);
            if hp {
                let q = ev(nodes, p, st2, g);
                assert(done(q));
                lemma_bs_ev(nodes, p, st2, g);
                if q.ok { lemma_bs_loop(nodes, c, p, hp, b, q.st, g); }
            } else {
                lemma_bs_loop(nodes, c, p, hp, b, st2, g);
            }
        }
    }
}

} // verus!
