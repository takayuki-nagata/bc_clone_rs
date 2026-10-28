// SPDX-License-Identifier: MIT

//! Relations between `bc_core` and the executable specification (`crates/bc_spec`), for the
//! refinement proofs of the evaluator. Compiled only under Verus.
//!
//! - `r_num`: a `BCNum` has the L0 value of a specification `Num` (numbers are related by value;
//!   `bc_spec::values` and `bc_spec::format` show that the specification uses numbers only
//!   through their values).
//! - `r_expr` / `r_stmt`: a production syntax tree (`Box` and `Vec`) is the subtree at index `n`
//!   of a specification arena (`Seq<Node>` with `usize` children). Names and string texts are
//!   related through their UTF-8 bytes (`text_view`); operators through the specification's
//!   operator codes, which the production enums list in the same order.
//! - `r_vars`, `r_arrays`, `r_funcs`: the evaluator's maps against the specification's
//!   association lists, by lookup: a name has a binding in one exactly when it has one in the
//!   other, and the scope stacks (or function definitions) correspond.
//! - `Evaluator::r_state` (in `eval.rs`, where the evaluator's fields are visible): the whole
//!   evaluator state (registers, flags, call stack, depth, invocation `ibase`, and the output
//!   streams through `out_log`/`out_col`/`err_log`).
//!
//! The refinement theorem will state: if `r_state(e, st)` and `r_expr(x, nodes, n)`, and
//! evaluating `x` returns, then some fuel `f` gives a specification result `ev(nodes, n, st, f)`
//! that did not run out of fuel and corresponds to it (`bc_spec::fuel` combines the fuels of
//! sub-evaluations).

use crate::error::{BcError, RuntimeError};
use crate::math::BCNum;
use crate::parser::{
    AssignOp, BinOp, Expr, ExprOrArray, FunctionDef, Param, Register, RelOp, Stmt,
};
use crate::spec_num::*;
use crate::verified_kernels::BC_SCALE_MAX;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use bc_spec::eval::*;
use bc_spec::num::{Num, to_l0, wf_num};
use bc_spec::parser::{Arg, Node};
use vstd::prelude::*;
use vstd::utf8::encode_utf8;

verus! {

broadcast use vstd::std_specs::vec::group_vec_axioms;

// ---------------------------------------------------------------------------------------------
// Values, names and operators
// ---------------------------------------------------------------------------------------------

/// The UTF-8 bytes of a name or a string's text.
pub open spec fn text_view(s: String) -> Seq<u8> {
    encode_utf8(s@)
}

/// A production number has the L0 value of a specification number, and its scale is within
/// `BC_SCALE_MAX` (the value is below `2^value_bits()` by `axiom_bigint_size`).
pub open spec fn r_num(b: BCNum, x: Num) -> bool {
    &&& wf_num(x)
    &&& b.val() == to_l0(x)
    &&& b.scale <= BC_SCALE_MAX
}

pub open spec fn reg_code(r: Register) -> u8 {
    match r {
        Register::Scale => 0,
        Register::Ibase => 1,
        Register::Obase => 2,
    }
}

/// `bc_spec::parser::binop_code`'s codes.
pub open spec fn bin_code(op: BinOp) -> u8 {
    match op {
        BinOp::Add => 0,
        BinOp::Sub => 1,
        BinOp::Mul => 2,
        BinOp::Div => 3,
        BinOp::Mod => 4,
        BinOp::Pow => 5,
    }
}

/// `bc_spec::parser::rel_code`'s codes.
pub open spec fn rel_code(op: RelOp) -> u8 {
    match op {
        RelOp::Eq => 0,
        RelOp::Ne => 1,
        RelOp::Lt => 2,
        RelOp::Le => 3,
        RelOp::Gt => 4,
        RelOp::Ge => 5,
    }
}

/// `bc_spec::parser::assign_code`'s codes: 0 for `=`, 1 + the binary code for `op=`.
pub open spec fn assign_code(op: AssignOp) -> u8 {
    match op {
        AssignOp::Assign => 0,
        AssignOp::Compound(b) => (bin_code(b) + 1) as u8,
    }
}

pub open spec fn r_param(p: Param, q: bc_spec::parser::Param) -> bool {
    q.name == text_view(p.name) && q.is_array == p.is_array
}

pub open spec fn r_params(ps: Seq<Param>, qs: Seq<bc_spec::parser::Param>) -> bool {
    ps.len() == qs.len() && forall|i: int| 0 <= i < ps.len() ==> #[trigger] r_param(ps[i], qs[i])
}

// ---------------------------------------------------------------------------------------------
// Syntax trees
// ---------------------------------------------------------------------------------------------

/// Production expression `e` is the arena subtree at `n`.
pub open spec fn r_expr(e: Expr, nodes: Seq<Node>, n: usize) -> bool
    decreases e,
{
    n < nodes.len() && match e {
        Expr::Number(t) => nodes[n as int] == Node::Number(text_view(t)),
        Expr::Variable(x) => nodes[n as int] == Node::Var(text_view(x)),
        Expr::ArrayAccess(x, i) => match nodes[n as int] {
            Node::Array(y, j) => y == text_view(x) && r_expr(*i, nodes, j),
            _ => false,
        },
        Expr::RegisterAccess(r) => nodes[n as int] == Node::Reg(reg_code(r)),
        Expr::Negate(a) => match nodes[n as int] {
            Node::Neg(j) => r_expr(*a, nodes, j),
            _ => false,
        },
        Expr::BinaryOp(op, l, r) => match nodes[n as int] {
            Node::Binary(c, a, b) => c == bin_code(op) && r_expr(*l, nodes, a) && r_expr(*r, nodes, b),
            _ => false,
        },
        Expr::RelationalOp(op, l, r) => match nodes[n as int] {
            Node::Rel(c, a, b) => c == rel_code(op) && r_expr(*l, nodes, a) && r_expr(*r, nodes, b),
            _ => false,
        },
        Expr::Update(inc, prefix, t) => match nodes[n as int] {
            Node::Update(i2, p2, j) => i2 == inc && p2 == prefix && r_expr(*t, nodes, j),
            _ => false,
        },
        Expr::AssignOp(op, t, v) => match nodes[n as int] {
            Node::Assign(c, a, b) => c == assign_code(op) && r_expr(*t, nodes, a) && r_expr(*v, nodes, b),
            _ => false,
        },
        Expr::Call(name, args) => match nodes[n as int] {
            Node::Call(m, sargs) => m == text_view(name) && args.len() == sargs.len()
                && forall|i: int| 0 <= i < args.len() ==> #[trigger] r_arg(args[i], nodes, sargs[i]),
            _ => false,
        },
        Expr::LengthCall(a) => match nodes[n as int] {
            Node::Length(j) => r_expr(*a, nodes, j),
            _ => false,
        },
        Expr::SqrtCall(a) => match nodes[n as int] {
            Node::Sqrt(j) => r_expr(*a, nodes, j),
            _ => false,
        },
        Expr::ScaleCall(a) => match nodes[n as int] {
            Node::ScaleOf(j) => r_expr(*a, nodes, j),
            _ => false,
        },
        Expr::Paren(a) => match nodes[n as int] {
            Node::Paren(j) => r_expr(*a, nodes, j),
            _ => false,
        },
    }
}

/// A call argument: an expression, or a whole array `name[]`.
pub open spec fn r_arg(a: ExprOrArray, nodes: Seq<Node>, s: Arg) -> bool
    decreases a,
{
    match a {
        ExprOrArray::Expr(e) => !s.is_array && r_expr(e, nodes, s.expr),
        ExprOrArray::ArrayArg(name) => s.is_array && s.name == text_view(name),
    }
}

/// Production statement `s` is the arena subtree at `n`. `Stmt::Quit` has no counterpart: the
/// parser stops at `quit` (it never builds the statement).
pub open spec fn r_stmt(s: Stmt, nodes: Seq<Node>, n: usize) -> bool
    decreases s,
{
    n < nodes.len() && match s {
        Stmt::Block(list) => match nodes[n as int] {
            Node::Block(ns) => r_stmts(list@, nodes, ns),
            _ => false,
        },
        Stmt::Expr(e) => match nodes[n as int] {
            Node::ExprStmt(j) => r_expr(e, nodes, j),
            _ => false,
        },
        Stmt::StringLiteral(t) => nodes[n as int] == Node::Str(text_view(t)),
        Stmt::Break => nodes[n as int] == Node::Break,
        Stmt::Quit => false,
        Stmt::Return(v) => match nodes[n as int] {
            Node::Return(hv, j) => match v {
                Some(e) => hv && r_expr(e, nodes, j),
                None => !hv,
            },
            _ => false,
        },
        Stmt::If(c, b) => match nodes[n as int] {
            Node::If(i, j) => r_expr(c, nodes, i) && r_stmt(*b, nodes, j),
            _ => false,
        },
        Stmt::While(c, b) => match nodes[n as int] {
            Node::While(i, j) => r_expr(c, nodes, i) && r_stmt(*b, nodes, j),
            _ => false,
        },
        Stmt::For(i, c, p, b) => match nodes[n as int] {
            Node::For(a, d, e, f) => r_expr(i, nodes, a) && r_expr(c, nodes, d) && r_expr(p, nodes, e)
                && r_stmt(*b, nodes, f),
            _ => false,
        },
        Stmt::FunctionDef(fd) => match nodes[n as int] {
            Node::Define(name, ps, autos, body) => name == text_view(fd.name) && r_params(fd.params@, ps)
                && r_params(fd.autos@, autos) && r_stmts(fd.body@, nodes, body),
            _ => false,
        },
    }
}

/// The statements `list` are the arena subtrees at `ns`.
pub open spec fn r_stmts(list: Seq<Stmt>, nodes: Seq<Node>, ns: Seq<usize>) -> bool
    decreases list,
{
    list.len() == ns.len() && forall|i: int| 0 <= i < list.len() ==> #[trigger] r_stmt(list[i], nodes, ns[i])
}

// ---------------------------------------------------------------------------------------------
// Evaluator state
// ---------------------------------------------------------------------------------------------

/// The scope stack of `name` in the specification's association list (first binding), if any.
pub open spec fn var_lookup(vars: Seq<VarBind>, name: Seq<u8>) -> Option<Seq<Num>>
    decreases vars.len(),
{
    if vars.len() == 0 {
        None
    } else if vars[0].name == name {
        Some(vars[0].stack)
    } else {
        var_lookup(vars.drop_first(), name)
    }
}

pub open spec fn arr_lookup(arrays: Seq<ArrBind>, name: Seq<u8>) -> Option<Seq<ArrFrame>>
    decreases arrays.len(),
{
    if arrays.len() == 0 {
        None
    } else if arrays[0].name == name {
        Some(arrays[0].stack)
    } else {
        arr_lookup(arrays.drop_first(), name)
    }
}

pub open spec fn r_stack(ps: Seq<BCNum>, ss: Seq<Num>) -> bool {
    ps.len() == ss.len() && forall|i: int| 0 <= i < ps.len() ==> #[trigger] r_num(ps[i], ss[i])
}

/// The value of element `idx` of a specification frame (0 if unset).
pub open spec fn elem_val(elems: Seq<Elem>, idx: int) -> Option<Num>
    decreases elems.len(),
{
    if elems.len() == 0 {
        None
    } else if elems[0].idx as int == idx {
        Some(elems[0].val)
    } else {
        elem_val(elems.drop_first(), idx)
    }
}

/// An array frame: every subscript below `BC_DIM_MAX` reads the same value (unset is 0 on both
/// sides), and production stores no other subscripts.
pub open spec fn r_frame(pf: Map<usize, BCNum>, sf: ArrFrame) -> bool {
    &&& forall|k: usize| #[trigger] pf.contains_key(k) ==> k < 16777216
    &&& forall|k: usize| #![trigger pf.contains_key(k)] #![trigger elem_val(sf.elems, k as int)]
        k < 16777216 ==> match (pf.contains_key(k), elem_val(sf.elems, k as int)) {
        (true, Some(x)) => r_num(pf[k], x),
        (true, None) => pf[k].val().coeff == 0,
        (false, Some(x)) => to_l0(x).coeff == 0 && wf_num(x),
        (false, None) => true,
    }
}

pub open spec fn r_frames(ps: Seq<BTreeMap<usize, BCNum>>, ss: Seq<ArrFrame>) -> bool {
    ps.len() == ss.len() && forall|i: int| 0 <= i < ps.len() ==> #[trigger] r_frame(ps[i]@, ss[i])
}

/// The names of production's maps are UTF-8 strings whose bytes name the specification's
/// bindings: a name is bound in one exactly when it is bound in the other.
pub open spec fn r_vars(m: Map<String, Vec<BCNum>>, vars: Seq<VarBind>) -> bool {
    &&& forall|k: String| #[trigger] m.contains_key(k) ==> var_lookup(vars, text_view(k)) is Some
        && r_stack(m[k]@, var_lookup(vars, text_view(k))->Some_0)
    &&& forall|i: int| #![trigger vars[i]] 0 <= i < vars.len() ==> exists|k: String| #[trigger] m.contains_key(k)
        && text_view(k) == vars[i].name
}

pub open spec fn r_arrays(m: Map<String, Vec<BTreeMap<usize, BCNum>>>, arrays: Seq<ArrBind>) -> bool {
    &&& forall|k: String| #[trigger] m.contains_key(k) ==> arr_lookup(arrays, text_view(k)) is Some
        && r_frames(m[k]@, arr_lookup(arrays, text_view(k))->Some_0)
    &&& forall|i: int| #![trigger arrays[i]] 0 <= i < arrays.len() ==> exists|k: String| #[trigger] m.contains_key(k)
        && text_view(k) == arrays[i].name
}

/// A function definition: name, parameters and `auto` list, and a body that is the list of
/// subtrees `f.body` of the arena of the unit that defined it.
pub open spec fn r_func(fd: FunctionDef, f: Func) -> bool {
    &&& f.name == text_view(fd.name)
    &&& r_params(fd.params@, f.params)
    &&& r_params(fd.autos@, f.autos)
    &&& r_stmts(fd.body@, f.nodes, f.body)
}

pub open spec fn r_funcs(m: Map<String, FunctionDef>, funcs: Seq<Func>) -> bool {
    &&& forall|k: String| #[trigger] m.contains_key(k) ==> bc_spec::eval::find_func(funcs, text_view(k)) is Some
        && r_func(m[k], bc_spec::eval::find_func(funcs, text_view(k))->Some_0)
    &&& forall|i: int| #![trigger funcs[i]] 0 <= i < funcs.len() ==> exists|k: String| #[trigger] m.contains_key(k)
        && text_view(k) == funcs[i].name
}

pub open spec fn r_calls(ps: Seq<String>, ss: Seq<Seq<u8>>) -> bool {
    ps.len() == ss.len() && forall|i: int| 0 <= i < ps.len() ==> #[trigger] text_view(ps[i]) == ss[i]
}

// ---------------------------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------------------------

/// The message of a runtime error, as the specification writes it.
pub open spec fn runtime_msg(k: RuntimeError) -> Seq<u8> {
    match k {
        RuntimeError::DivideByZero => msg_divide_by_zero(),
        RuntimeError::NegativePowerOfZero => msg_negative_power_of_zero(),
        RuntimeError::ModuloByZero => msg_modulo_by_zero(),
        RuntimeError::NegativeSqrt => msg_negative_sqrt(),
        RuntimeError::UndefinedFunction(n) => msg_undefined_function(text_view(n)),
        RuntimeError::ParameterMismatch => msg_parameter_mismatch(),
        RuntimeError::ParameterTypeMismatch(n) => msg_parameter_type(text_view(n)),
        RuntimeError::ArraySubscriptOutOfBounds(n) => msg_subscript(text_view(n)),
        RuntimeError::ExponentTooLarge => msg_exponent_too_large(),
        RuntimeError::ScaleTooLarge => msg_scale_too_large(),
        // `-l` is not modeled.
        RuntimeError::MathArgumentTooLarge => Seq::empty(),
        RuntimeError::NestingTooDeep => msg_nesting_too_deep(),
    }
}

/// A production error is the specification's runtime error (never "out of fuel").
pub open spec fn r_err(e: BcError, x: RErr) -> bool {
    !x.out_of_fuel && match e {
        BcError::Runtime { kind, func } => x.msg == runtime_msg(kind) && match func {
            Some(f) => x.has_func && x.func == text_view(f),
            None => !x.has_func,
        },
        _ => false,
    }
}

/// The expressions whose evaluation is proved to refine the specification so far;
/// the others are evaluated by trusted code that only keeps `Evaluator::inv`.
pub open spec fn in_fragment(e: Expr) -> bool
    decreases e,
{
    match e {
        Expr::RegisterAccess(_) => true,
        Expr::Paren(a) => in_fragment(*a),
        Expr::Negate(a) => in_fragment(*a),
        Expr::LengthCall(a) => in_fragment(*a),
        Expr::ScaleCall(a) => in_fragment(*a),
        Expr::SqrtCall(a) => in_fragment(*a),
        Expr::BinaryOp(op, l, r) => op != BinOp::Pow && in_fragment(*l) && in_fragment(*r),
        Expr::RelationalOp(_, l, r) => in_fragment(*l) && in_fragment(*r),
        _ => false,
    }
}

// ---------------------------------------------------------------------------------------------
// Uniqueness of the L0 characterizations
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_pow10_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow10(a) <= pow10(b),
    decreases b,
{
    if a < b {
        lemma_pow10_mono(a, (b - 1) as nat);
        lemma_pow10_pos((b - 1) as nat);
        assert(pow10(b) == 10 * pow10((b - 1) as nat));
    }
}

/// The number of digits of a value is unique.
pub proof fn lemma_digit_count_unique(n: int, k1: nat, k2: nat)
    requires
        is_digit_count(n, k1),
        is_digit_count(n, k2),
    ensures
        k1 == k2,
{
    if k1 < k2 {
        lemma_pow10_mono(k1, (k2 - 1) as nat);
    } else if k2 < k1 {
        lemma_pow10_mono(k2, (k1 - 1) as nat);
    }
}

/// The integer square root is unique.
pub proof fn lemma_isqrt_unique(n: int, r1: int, r2: int)
    requires
        is_isqrt(n, r1),
        is_isqrt(n, r2),
    ensures
        r1 == r2,
{
    if r1 < r2 {
        assert((r1 + 1) * (r1 + 1) <= r2 * r2) by (nonlinear_arith)
            requires
                0 <= r1,
                r1 + 1 <= r2;
    } else if r2 < r1 {
        assert((r2 + 1) * (r2 + 1) <= r1 * r1) by (nonlinear_arith)
            requires
                0 <= r2,
                r2 + 1 <= r1;
    }
}

} // verus!
