// SPDX-License-Identifier: MIT

//! Fuel monotonicity of the evaluator: a result that did not run out of fuel stays the same with
//! more fuel.
//!
//! The refinement proofs of `bc_core` state that `bc_clone` computes
//! `ev(nodes, n, st, fuel)` for *some* fuel. Each sub-evaluation comes with its own fuel, and
//! these lemmas let a proof raise them all to their maximum.
//!
//! One function needs more than induction: `exec_expr_stmt` calls `is_assignment` with the same
//! fuel as the expression. `lemma_is_assignment_stable` shows that once the expression evaluated,
//! `is_assignment` has enough fuel to give the same answer with any larger fuel.

use crate::eval::*;
use crate::num::*;
use crate::parser::*;
use vstd::prelude::*;

verus! {

/// The evaluation finished: it succeeded, or it failed with an error other than running out of
/// fuel.
pub open spec fn done(r: ER) -> bool {
    r.ok || !r.err.out_of_fuel
}

/// Once the expression `n` evaluated with fuel `f`, `is_assignment(nodes, n, h)` is the same for
/// every `h > f`: each unary minus costs `ev` three levels of fuel and `is_assignment` one.
pub proof fn lemma_is_assignment_stable(nodes: Seq<Node>, n: usize, st: EState, f: u64, h1: u64, h2: u64)
    requires
        ev(nodes, n, st, f).ok,
        f < h1,
        f < h2,
    ensures
        is_assignment(nodes, n, h1) == is_assignment(nodes, n, h2),
    decreases f,
{
    if n < nodes.len() {
        match nodes[n as int] {
            Node::Neg(e) => {
                let st1 = with_depth(st, (st.depth + 1) as u64);
                assert(ev_node(nodes, n, st1, (f - 1) as u64).ok);
                assert(ev_unary(nodes, 0u8, e, st1, (f - 2) as u64).ok);
                lemma_is_assignment_stable(nodes, e, st1, (f - 3) as u64, (h1 - 1) as u64, (h2 - 1) as u64);
            },
            _ => {},
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_ev_mono(nodes: Seq<Node>, n: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(ev(nodes, n, st, f)),
    ensures
        ev(nodes, n, st, g) == ev(nodes, n, st, f),
    decreases f,
{
    if f > 0 && within(st.depth, 1u64, st.max_depth) {
        lemma_ev_node_mono(nodes, n, with_depth(st, (st.depth + 1) as u64), (f - 1) as u64, (g - 1) as u64);
    }
}

pub proof fn lemma_ev_node_mono(nodes: Seq<Node>, n: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(ev_node(nodes, n, st, f)),
    ensures
        ev_node(nodes, n, st, g) == ev_node(nodes, n, st, f),
    decreases f,
{
    if f > 0 && n < nodes.len() {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        match nodes[n as int] {
            Node::Array(name, i) => lemma_ev_array_mono(nodes, name, i, st, f1, g1),
            Node::Neg(e) => lemma_ev_unary_mono(nodes, 0u8, e, st, f1, g1),
            Node::Binary(op, l, r) => lemma_ev_binary_mono(nodes, op, l, r, st, f1, g1),
            Node::Rel(op, l, r) => lemma_ev_rel_mono(nodes, op, l, r, st, f1, g1),
            Node::Assign(op, t, v) => lemma_ev_assign_mono(nodes, op, t, v, st, f1, g1),
            Node::Update(is_inc, prefix, t) => lemma_ev_update_mono(nodes, is_inc, prefix, t, st, f1, g1),
            Node::Call(name, args) => lemma_ev_call_mono(nodes, name, args, st, f1, g1),
            Node::Length(e) => lemma_ev_unary_mono(nodes, 1u8, e, st, f1, g1),
            Node::Sqrt(e) => lemma_ev_unary_mono(nodes, 2u8, e, st, f1, g1),
            Node::ScaleOf(e) => lemma_ev_unary_mono(nodes, 3u8, e, st, f1, g1),
            Node::Paren(e) => lemma_ev_mono(nodes, e, st, f1, g1),
            _ => {},
        }
    }
}

pub proof fn lemma_ev_unary_mono(nodes: Seq<Node>, which: u8, e: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(ev_unary(nodes, which, e, st, f)),
    ensures
        ev_unary(nodes, which, e, st, g) == ev_unary(nodes, which, e, st, f),
    decreases f,
{
    if f > 0 {
        lemma_ev_mono(nodes, e, st, (f - 1) as u64, (g - 1) as u64);
    }
}

pub proof fn lemma_ev_array_mono(nodes: Seq<Node>, name: Seq<u8>, i: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(ev_array(nodes, name, i, st, f)),
    ensures
        ev_array(nodes, name, i, st, g) == ev_array(nodes, name, i, st, f),
    decreases f,
{
    if f > 0 {
        lemma_ev_mono(nodes, i, st, (f - 1) as u64, (g - 1) as u64);
    }
}

pub proof fn lemma_ev_binary_mono(nodes: Seq<Node>, op: u8, l: usize, r: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(ev_binary(nodes, op, l, r, st, f)),
    ensures
        ev_binary(nodes, op, l, r, st, g) == ev_binary(nodes, op, l, r, st, f),
    decreases f,
{
    if f > 0 {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        lemma_ev_mono(nodes, l, st, f1, g1);
        let a = ev(nodes, l, st, f1);
        if a.ok {
            lemma_ev_mono(nodes, r, a.st, f1, g1);
        }
    }
}

pub proof fn lemma_ev_rel_mono(nodes: Seq<Node>, op: u8, l: usize, r: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(ev_rel(nodes, op, l, r, st, f)),
    ensures
        ev_rel(nodes, op, l, r, st, g) == ev_rel(nodes, op, l, r, st, f),
    decreases f,
{
    if f > 0 {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        lemma_ev_mono(nodes, l, st, f1, g1);
        let a = ev(nodes, l, st, f1);
        if a.ok {
            lemma_ev_mono(nodes, r, a.st, f1, g1);
        }
    }
}

pub proof fn lemma_resolve_mono(nodes: Seq<Node>, n: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(resolve(nodes, n, st, f).r),
    ensures
        resolve(nodes, n, st, g) == resolve(nodes, n, st, f),
    decreases f,
{
    if f > 0 && n < nodes.len() {
        match nodes[n as int] {
            Node::Array(name, i) => lemma_ev_mono(nodes, i, st, (f - 1) as u64, (g - 1) as u64),
            _ => {},
        }
    }
}

pub proof fn lemma_ev_assign_mono(nodes: Seq<Node>, op: u8, t: usize, v: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(ev_assign(nodes, op, t, v, st, f)),
    ensures
        ev_assign(nodes, op, t, v, st, g) == ev_assign(nodes, op, t, v, st, f),
    decreases f,
{
    if f > 0 {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        lemma_resolve_mono(nodes, t, st, f1, g1);
        let pr = resolve(nodes, t, st, f1);
        if pr.r.ok && !single_digit_base(nodes, pr.place, op, v) {
            lemma_ev_mono(nodes, v, pr.r.st, f1, g1);
        }
    }
}

pub proof fn lemma_ev_update_mono(nodes: Seq<Node>, is_inc: bool, prefix: bool, t: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(ev_update(nodes, is_inc, prefix, t, st, f)),
    ensures
        ev_update(nodes, is_inc, prefix, t, st, g) == ev_update(nodes, is_inc, prefix, t, st, f),
    decreases f,
{
    if f > 0 {
        lemma_resolve_mono(nodes, t, st, (f - 1) as u64, (g - 1) as u64);
    }
}

// ---------------------------------------------------------------------------------------------
// Function calls
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_ev_args_mono(nodes: Seq<Node>, args: Seq<Arg>, params: Seq<Param>, st: EState, acc: Seq<ArgVal>, f: u64, g: u64)
    requires
        f <= g,
        done(ev_args(nodes, args, params, st, acc, f).r),
    ensures
        ev_args(nodes, args, params, st, acc, g) == ev_args(nodes, args, params, st, acc, f),
    decreases f,
{
    if f > 0 && args.len() > 0 && params.len() > 0 {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        let a = args[0];
        let p = params[0];
        if p.is_array == a.is_array {
            if p.is_array {
                let v = ArgVal { is_array: true, name: p.name, val: zero_num(), frame: arr_top(st.arrays, a.name) };
                lemma_ev_args_mono(nodes, args.drop_first(), params.drop_first(), st, acc.push(v), f1, g1);
            } else {
                lemma_ev_mono(nodes, a.expr, st, f1, g1);
                let x = ev(nodes, a.expr, st, f1);
                if x.ok {
                    let v = ArgVal { is_array: false, name: p.name, val: x.val, frame: empty_frame() };
                    lemma_ev_args_mono(nodes, args.drop_first(), params.drop_first(), x.st, acc.push(v), f1, g1);
                }
            }
        }
    }
}

pub proof fn lemma_ev_call_mono(nodes: Seq<Node>, name: Seq<u8>, args: Seq<Arg>, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(ev_call(nodes, name, args, st, f)),
    ensures
        ev_call(nodes, name, args, st, g) == ev_call(nodes, name, args, st, f),
    decreases f,
{
    if f > 0 {
        match find_func(st.funcs, name) {
            Some(func) => {
                if args.len() == func.params.len() {
                    let f1 = (f - 1) as u64;
                    let g1 = (g - 1) as u64;
                    lemma_ev_args_mono(nodes, args, func.params, st, seq![], f1, g1);
                    let a = ev_args(nodes, args, func.params, st, seq![], f1);
                    if a.r.ok {
                        lemma_run_call_mono(func, a.vals, a.r.st, f1, g1);
                    }
                }
            },
            None => {},
        }
    }
}

pub proof fn lemma_run_call_mono(func: Func, vals: Seq<ArgVal>, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(run_call(func, vals, st, f)),
    ensures
        run_call(func, vals, st, g) == run_call(func, vals, st, f),
    decreases f,
{
    if f > 0 {
        let st1 = push_autos(push_args(st, vals), func.autos);
        let st2 = with_flags(st1, st1.brk, false, zero_num());
        let st3 = with_call(st2, names_push(st2.calls, func.name), true, st2.ibase);
        let r = exec_body(func.nodes.s, func.body, st3, (f - 1) as u64);
        // An error keeps whether it ran out of fuel when it is attributed to the function.
        assert(done(r));
        lemma_exec_body_mono(func.nodes.s, func.body, st3, (f - 1) as u64, (g - 1) as u64);
    }
}

pub proof fn lemma_exec_body_mono(nodes: Seq<Node>, body: Seq<usize>, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(exec_body(nodes, body, st, f)),
    ensures
        exec_body(nodes, body, st, g) == exec_body(nodes, body, st, f),
    decreases f,
{
    if f > 0 && body.len() > 0 {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        lemma_exec_mono(nodes, body[0], st, f1, g1);
        let r = exec(nodes, body[0], st, f1);
        if r.ok && !r.st.ret {
            lemma_exec_body_mono(nodes, body.drop_first(), r.st, f1, g1);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_exec_mono(nodes: Seq<Node>, n: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(exec(nodes, n, st, f)),
    ensures
        exec(nodes, n, st, g) == exec(nodes, n, st, f),
    decreases f,
{
    if f > 0 && within(st.depth, 1u64, st.max_depth) {
        lemma_exec_node_mono(nodes, n, with_depth(st, (st.depth + 1) as u64), (f - 1) as u64, (g - 1) as u64);
    }
}

pub proof fn lemma_exec_node_mono(nodes: Seq<Node>, n: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(exec_node(nodes, n, st, f)),
    ensures
        exec_node(nodes, n, st, g) == exec_node(nodes, n, st, f),
    decreases f,
{
    if f > 0 && !(st.brk || st.ret) && n < nodes.len() {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        match nodes[n as int] {
            Node::Block(list) => lemma_exec_list_mono(nodes, list, st, f1, g1),
            Node::ExprStmt(e) => lemma_exec_expr_stmt_mono(nodes, e, st, f1, g1),
            Node::Return(has_value, e) => lemma_exec_return_mono(nodes, has_value, e, st, f1, g1),
            Node::If(c, b) => lemma_exec_if_mono(nodes, c, b, st, f1, g1),
            Node::While(c, b) => lemma_exec_loop_mono(nodes, c, 0usize, false, b, st, f1, g1),
            Node::For(i, c, p, b) => lemma_exec_for_mono(nodes, i, c, p, b, st, f1, g1),
            _ => {},
        }
    }
}

pub proof fn lemma_exec_return_mono(nodes: Seq<Node>, has_value: bool, e: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(exec_return(nodes, has_value, e, st, f)),
    ensures
        exec_return(nodes, has_value, e, st, g) == exec_return(nodes, has_value, e, st, f),
    decreases f,
{
    if f > 0 && has_value {
        lemma_ev_mono(nodes, e, st, (f - 1) as u64, (g - 1) as u64);
    }
}

pub proof fn lemma_exec_if_mono(nodes: Seq<Node>, c: usize, b: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(exec_if(nodes, c, b, st, f)),
    ensures
        exec_if(nodes, c, b, st, g) == exec_if(nodes, c, b, st, f),
    decreases f,
{
    if f > 0 {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        lemma_ev_mono(nodes, c, st, f1, g1);
        let x = ev(nodes, c, st, f1);
        if x.ok && !is_zero_mag(x.val.mag) {
            lemma_exec_mono(nodes, b, x.st, f1, g1);
        }
    }
}

pub proof fn lemma_exec_for_mono(nodes: Seq<Node>, i: usize, c: usize, p: usize, b: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(exec_for(nodes, i, c, p, b, st, f)),
    ensures
        exec_for(nodes, i, c, p, b, st, g) == exec_for(nodes, i, c, p, b, st, f),
    decreases f,
{
    if f > 0 {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        lemma_ev_mono(nodes, i, st, f1, g1);
        let x = ev(nodes, i, st, f1);
        if x.ok {
            lemma_exec_loop_mono(nodes, c, p, true, b, x.st, f1, g1);
        }
    }
}

pub proof fn lemma_exec_list_mono(nodes: Seq<Node>, list: Seq<usize>, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(exec_list(nodes, list, st, f)),
    ensures
        exec_list(nodes, list, st, g) == exec_list(nodes, list, st, f),
    decreases f,
{
    if f > 0 && list.len() > 0 {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        lemma_exec_mono(nodes, list[0], st, f1, g1);
        let r = exec(nodes, list[0], st, f1);
        if r.ok && !(r.st.brk || r.st.ret) {
            lemma_exec_list_mono(nodes, list.drop_first(), r.st, f1, g1);
        }
    }
}

pub proof fn lemma_exec_expr_stmt_mono(nodes: Seq<Node>, e: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(exec_expr_stmt(nodes, e, st, f)),
    ensures
        exec_expr_stmt(nodes, e, st, g) == exec_expr_stmt(nodes, e, st, f),
    decreases f,
{
    if f > 0 {
        let f1 = (f - 1) as u64;
        lemma_ev_mono(nodes, e, st, f1, (g - 1) as u64);
        if ev(nodes, e, st, f1).ok {
            lemma_is_assignment_stable(nodes, e, st, f1, f, g);
        }
    }
}

pub proof fn lemma_exec_loop_mono(nodes: Seq<Node>, c: usize, post: usize, has_post: bool, b: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(exec_loop(nodes, c, post, has_post, b, st, f)),
    ensures
        exec_loop(nodes, c, post, has_post, b, st, g) == exec_loop(nodes, c, post, has_post, b, st, f),
    decreases f,
{
    if f > 0 {
        let f1 = (f - 1) as u64;
        let g1 = (g - 1) as u64;
        lemma_ev_mono(nodes, c, st, f1, g1);
        let x = ev(nodes, c, st, f1);
        if x.ok && !is_zero_mag(x.val.mag) {
            lemma_exec_mono(nodes, b, x.st, f1, g1);
            let r = exec(nodes, b, x.st, f1);
            if r.ok && !(r.st.brk || r.st.ret) {
                let st2 = with_flags(r.st, false, r.st.ret, r.st.ret_val);
                if has_post {
                    lemma_ev_mono(nodes, post, st2, f1, g1);
                    let p = ev(nodes, post, st2, f1);
                    if p.ok {
                        lemma_exec_loop_mono(nodes, c, post, has_post, b, p.st, f1, g1);
                    }
                } else {
                    lemma_exec_loop_mono(nodes, c, post, has_post, b, st2, f1, g1);
                }
            }
        }
    }
}

} // verus!
