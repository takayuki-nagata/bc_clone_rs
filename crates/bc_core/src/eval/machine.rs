// SPDX-License-Identifier: MIT

//! The evaluator's machine: expressions run on an explicit stack of frames, so the depth of an
//! evaluation does not depend on the native stack.
//!
//! A frame is what remains to do of one syntactic form once a sub-computation has a result.
//! The proof relates a frame to the specification's `bc_spec::den::K` (`r_frame`) and keeps the
//! meaning of the machine's state, `den(ks, ...)`, equal to the result of the whole evaluation
//! (`m_eval`, `m_node`, `m_ret`). So the theorem of `eval_ref` has the form it had when the
//! evaluator recursed.
//!
//! This module holds the frames, the predicates that relate them to the specification, the
//! loop (`run`), and the step that pops a frame (`step_ret`, `ret_ok`, `ret_stmt`). The steps
//! of each kind of frame are in the submodules: expressions (`expr`), statements (`stmt`),
//! function calls and the `-l` functions (`func`), and the fast path (`quick`).

use super::*;
#[cfg(verus_keep_ghost)]
use bc_spec::den::*;

#[allow(
    clippy::single_match,
    reason = "a match arm that only updates ghost state is empty outside Verus"
)]
mod quick;
use quick::*;
mod expr;
mod func;
mod stmt;

/// One pending syntactic form. See `bc_spec::den::K`, frame by frame.
pub(crate) enum Frame {
    /// The level of `eval_ref`: the depth to restore.
    Depth(usize),
    /// `-e` (0), `length(e)` (1), `sqrt(e)` (2) and `scale(e)` (3).
    Unary(u8),
    BinL(BinOp, usize),
    BinR(BinOp, BCNum),
    RelL(RelOp, usize),
    RelR(RelOp, BCNum),
    /// The subscript of the array node at this index.
    ArrayIdx(usize),
    /// The subscript of the target (the array node at this index) of an assignment, and the
    /// operator and the node of its value.
    AssignIdx(usize, AssignOp, usize),
    /// The subscript of the target of `++`/`--`.
    UpdateIdx(usize, bool, bool),
    /// The value of `=`.
    Store(Place),
    /// The value of `op=`: the operator and the old value.
    OpStore(Place, BinOp, BCNum),
    /// The level of `exec_ref`: the depth to restore.
    DepthS(usize),
    /// The rest of the block at this node, from this statement on.
    List(usize, usize),
    /// An expression statement with this expression.
    ExprStmt(usize),
    Return,
    /// `if`: the body.
    IfCond(usize),
    /// `for`: the condition, the post-expression and the body.
    ForInit(usize, usize, usize),
    /// A loop: the condition, the post-expression of a `for` and the body.
    LoopCond(usize, Option<usize>, usize),
    LoopBody(usize, Option<usize>, usize),
    LoopPost(usize, Option<usize>, usize),
    /// A value argument of the call at this node: the function, the argument's index and the
    /// values so far.
    ArgVal(FunctionDef, usize, usize, Vec<(String, ArgValue)>),
    /// A running function body: the caller's arena, the function's `Define` node, its name and
    /// the caller's saved return state and invocation `ibase`.
    Call(Rc<Code>, usize, String, bool, Option<usize>, BCNum),
    /// The rest of the body of the function at this `Define` node, from this statement on.
    Body(usize, usize),
    /// The argument of the `-l` function `s`, `c`, `a`, `l` or `e` at this call node.
    Math1(usize),
    /// The order of `j(n, x)` at this call node.
    MathJ1(usize),
    /// The argument of `j(n, x)`, with the order's value.
    MathJ2(BCNum),
}

/// What the machine does next.
pub(crate) enum Step {
    Eval(usize),
    Exec(usize),
    /// Runs the body of the function at this `Define` node of this arena.
    Enter(Rc<Code>, usize),
    /// Returns to the caller's arena with the call's result.
    Leave(Rc<Code>, Result<BCNum, BcError>),
    Ret(Result<BCNum, BcError>),
}

#[cfg(not(verus_keep_ghost))]
pub(crate) type MG = ();
#[cfg(not(verus_keep_ghost))]
pub(crate) type MCx = ();
#[cfg(not(verus_keep_ghost))]
pub(crate) type MPop = ();
#[cfg(verus_keep_ghost)]
pub(crate) type MK = K;
#[cfg(not(verus_keep_ghost))]
pub(crate) type MK = ();
#[cfg(verus_keep_ghost)]
pub(crate) type MResult = ER;
#[cfg(not(verus_keep_ghost))]
pub(crate) type MResult = ();

verus! {

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExFrame(Frame);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExStep(Step);

/// The machine's state as the proof sees it: the frames, and what it is about to evaluate from
/// which state, or the result it has.
#[cfg(verus_keep_ghost)]
pub ghost struct MG {
    /// The arena of the code that runs after an `Enter` or `Leave` step.
    pub nodes: Seq<bc_spec::parser::Node>,
    pub ks: Seq<K>,
    pub s: EState,
    pub x: ER,
}

/// The bottom of the stack: the depth of the evaluation, and whether it evaluates an expression
/// (`eval_ref`) or executes a statement (`exec_ref`).
#[cfg(verus_keep_ghost)]
pub ghost struct MRoot {
    pub d: usize,
    pub e: bool,
}

/// What stays fixed while the machine runs in one arena: the arena's model, the result of the
/// whole evaluation, and the bottom of the stack.
#[cfg(verus_keep_ghost)]
pub ghost struct MCx {
    pub nodes: Seq<bc_spec::parser::Node>,
    pub goal: ER,
    pub d0: MRoot,
}

/// The frame just popped: its continuation, the frames below it, and the result it receives.
#[cfg(verus_keep_ghost)]
pub ghost struct MPop {
    pub k: K,
    pub ks: Seq<K>,
    pub x: ER,
}

/// Whether the frame takes the result of an expression (a value) rather than of a statement.
pub(crate) open spec fn takes_value(f: Frame) -> bool {
    !(f is DepthS || f is List || f is LoopBody || f is Body || f is Call)
}

/// Whether the frame's own result is that of an expression.
pub(crate) open spec fn gives_value(f: Frame) -> bool {
    !(f is DepthS || f is List || f is LoopBody || f is ExprStmt || f is Return || f is IfCond
        || f is ForInit || f is LoopCond || f is LoopPost || f is Body)
}

/// Whether the result the stack waits for is a value.
pub(crate) open spec fn wants(fr: Seq<Frame>, d0: MRoot) -> bool {
    if fr.len() == 0 { d0.e } else { takes_value(fr.last()) }
}

/// What holds of the frames without any hypothesis: the depths nest down to `d0`, stored
/// values have small scales, and each frame gives the kind of result the one under it takes.
pub(crate) open spec fn frames_ok(fr: Seq<Frame>, cur: usize, d0: MRoot) -> bool
    decreases fr.len(),
{
    if fr.len() == 0 { cur == d0.d } else {
        &&& gives_value(fr.last()) == wants(fr.drop_last(), d0)
        &&& mframe_ok(fr.last())
        &&& match fr.last() {
            Frame::Depth(d) => d + 1 == cur && frames_ok(fr.drop_last(), d, d0),
            Frame::DepthS(d) => d + 1 == cur && frames_ok(fr.drop_last(), d, d0),
            _ => frames_ok(fr.drop_last(), cur, d0),
        }
    }
}

pub(crate) open spec fn r_mframe(f: Frame, k: K, code: Rc<Code>, nodes: SpecNodes) -> bool {
    match f {
        Frame::Depth(d) => k == K::Depth(d as u64),
        Frame::Unary(w) => k == K::Unary(w),
        Frame::BinL(op, r) => k == K::BinL(nodes, bin_code(op), r),
        Frame::BinR(op, v) => match k {
            K::BinR(c, a) => c == bin_code(op) && r_num(v, a),
            _ => false,
        },
        Frame::RelL(op, r) => k == K::RelL(nodes, rel_code(op), r),
        Frame::RelR(op, v) => match k {
            K::RelR(c, a) => c == rel_code(op) && r_num(v, a),
            _ => false,
        },
        Frame::ArrayIdx(t) => t < code.nodes@.len() && match code.nodes@[t as int] {
            PNode::Array(name, _) => k == K::ArrayIdx(text_view(name)),
            _ => false,
        },
        Frame::AssignIdx(t, op, v) => t < code.nodes@.len() && match code.nodes@[t as int] {
            PNode::Array(name, _) => k == K::AssignIdx(nodes, text_view(name), assign_code(op), v),
            _ => false,
        },
        Frame::UpdateIdx(t, inc, prefix) => t < code.nodes@.len() && match code.nodes@[t as int] {
            PNode::Array(name, _) => k == K::UpdateIdx(text_view(name), inc, prefix),
            _ => false,
        },
        Frame::Store(p) => match k {
            K::Store(sp) => r_place(p, sp),
            _ => false,
        },
        Frame::OpStore(p, op, v) => match k {
            K::OpStore(sp, c, a) => r_place(p, sp) && c == bin_code(op) && r_num(v, a),
            _ => false,
        },
        Frame::DepthS(d) => k == K::Depth(d as u64),
        Frame::List(n, i) => n < code.nodes@.len() && match code.nodes@[n as int] {
            PNode::Block(list) => i <= list@.len() && k == K::List(nodes, list@.skip(i as int)),
            _ => false,
        },
        Frame::ExprStmt(e) => k == K::ExprStmt(nodes, e),
        Frame::Return => k == K::Return,
        Frame::IfCond(b) => k == K::IfCond(nodes, b),
        Frame::ForInit(c, p, b) => k == K::ForInit(nodes, c, p, b),
        Frame::LoopCond(c, p, b) => k == K::LoopCond(nodes, c, opt_index(p), p is Some, b),
        Frame::LoopBody(c, p, b) => k == K::LoopBody(nodes, c, opt_index(p), p is Some, b),
        Frame::LoopPost(c, p, b) => k == K::LoopPost(nodes, c, opt_index(p), p is Some, b),
        Frame::ArgVal(fd, n, i, vals) => match k {
            K::ArgVal(ns, g, a, p, name, acc) => {
                &&& ns == nodes
                &&& r_func(fd, g)
                &&& n < nodes.len()
                &&& nodes[n as int] is Call
                &&& i < call_args(nodes, n).len()
                &&& a == call_args(nodes, n).skip(i as int + 1)
                &&& call_args(nodes, n).len() == g.params.len()
                &&& i < g.params.len()
                &&& p == g.params.skip(i as int + 1)
                &&& name == param_name(g, i)
                &&& vals@.len() == i
                &&& r_argvals(vals@, acc)
                &&& call_named(code, n, g.name)
            },
            _ => false,
        },
        Frame::Body(def, i) => match k {
            K::Body(ns, rest) => ns == nodes && def < nodes.len()
                && (nodes[def as int] matches Node::Define(_, _, _, body) && i <= body.len() && rest == body.skip(i as int)),
            _ => false,
        },
        _ => false,
    }
}

/// The post-expression of a loop as the specification gives it (0 for a `while`).
pub(crate) open spec fn opt_index(p: Option<usize>) -> usize {
    match p {
        Some(i) => i,
        None => 0usize,
    }
}

/// The arguments of the call at node `n`.
pub(crate) open spec fn call_args(nodes: SpecNodes, n: usize) -> Seq<bc_spec::parser::Arg> {
    if n < nodes.len() {
        match nodes[n as int] {
            Node::Call(_, a) => a,
            _ => Seq::empty(),
        }
    } else {
        Seq::empty()
    }
}

/// The name of parameter `i`.
pub(crate) open spec fn param_name(f: Func, i: usize) -> Seq<u8> {
    if i < f.params.len() { f.params[i as int].name } else { Seq::empty() }
}

/// Node `n` calls the function named `name`.
pub(crate) open spec fn call_named(code: Rc<Code>, n: usize, name: Seq<u8>) -> bool {
    n < code.nodes@.len() && match code.nodes@[n as int] {
        PNode::Call(cname, _) => text_view(cname) == name,
        _ => false,
    }
}

/// A statement that the machine does not split into frames.
pub(crate) open spec fn leaf_stmt_node(code: Rc<Code>, n: usize) -> bool {
    n >= code.nodes@.len() || match code.nodes@[n as int] {
        PNode::Block(_) | PNode::ExprStmt(_) | PNode::Return(Some(_)) | PNode::If(_, _)
        | PNode::While(_, _) | PNode::For(_, _, _, _) => false,
        _ => true,
    }
}

/// After popping the frame `fr`, which takes the result of a statement.
pub(crate) open spec fn m_after_s(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, f: Frame, k: K, ks: Seq<K>, x: ER, goal: ER) -> bool {
    &&& r_rc(code, nodes)
    &&& x.ok
    &&& r_state(e, x.st)
    &&& r_mframes(fr, ks, code, nodes)
    &&& r_mframe(f, k, code, nodes)
    &&& den(ks, apply(k, x)) == goal
    &&& done(goal)
}

/// The frames correspond to the specification's, each in the arena it runs in: the frames under a
/// `Call` run in the caller's arena.
pub(crate) open spec fn r_mframes(fr: Seq<Frame>, ks: Seq<K>, code: Rc<Code>, nodes: SpecNodes) -> bool
    decreases fr.len(),
{
    fr.len() == ks.len() && (fr.len() == 0 || match fr.last() {
        Frame::Call(caller, _, _, _, _, _) => r_call_frame(fr.last(), ks.last(), code, nodes) && match ks.last() {
            K::Call(_, _, cn) => r_rc(caller, cn) && r_mframes(fr.drop_last(), ks.drop_last(), caller, cn),
            _ => false,
        },
        _ => r_mframe(fr.last(), ks.last(), code, nodes) && r_mframes(fr.drop_last(), ks.drop_last(), code, nodes),
    })
}

/// A running call, in the callee's arena.
pub(crate) open spec fn r_call_frame(f: Frame, k: K, code: Rc<Code>, nodes: SpecNodes) -> bool {
    match (f, k) {
        (Frame::Call(_, def, name, flag, inv, v), K::Call(g, sv, _)) => {
            &&& r_rc(code, nodes)
            &&& g.nodes == nodes
            &&& def < nodes.len()
            &&& nodes[def as int] == Node::Define(g.name, g.params, g.autos, g.body)
            &&& g.name == text_view(name)
            &&& flag == sv.ret
            &&& r_num(v, sv.ret_val)
            &&& match inv {
                Some(b) => sv.has_inv && b == sv.inv_ibase,
                None => !sv.has_inv,
            }
        },
        _ => false,
    }
}

/// About to evaluate node `n`, including its nesting level.
pub(crate) open spec fn m_eval(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, n: usize, g: MG, goal: ER) -> bool {
    &&& r_rc(code, nodes)
    &&& r_state(e, g.s)
    &&& r_mframes(fr, g.ks, code, nodes)
    &&& den(g.ks, bs_ev(nodes, n, g.s)) == goal
    &&& done(goal)
}

/// About to evaluate the form at node `n`.
pub(crate) open spec fn m_node(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, n: usize, g: MG, goal: ER) -> bool {
    &&& r_rc(code, nodes)
    &&& r_state(e, g.s)
    &&& r_mframes(fr, g.ks, code, nodes)
    &&& den(g.ks, bs_ev_node(nodes, n, g.s)) == goal
    &&& done(goal)
}

/// The result of an expression, or of a statement (whose value means nothing).
pub(crate) open spec fn r_ret(r: Result<BCNum, BcError>, e: Evaluator, x: ER, value: bool) -> bool {
    if value { r_result(r, e, x, e.eval_depth) } else {
        match r {
            Ok(_) => x.ok && r_state(e, x.st),
            Err(err) => !x.ok && r_err(err, x.err) && r_state(e, with_depth(x.st, e.eval_depth as u64)),
        }
    }
}

/// About to execute node `n`, including its nesting level.
pub(crate) open spec fn m_exec(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, n: usize, g: MG, goal: ER) -> bool {
    &&& r_rc(code, nodes)
    &&& r_state(e, g.s)
    &&& r_mframes(fr, g.ks, code, nodes)
    &&& den(g.ks, bs_exec(nodes, n, g.s)) == goal
    &&& done(goal)
}

/// About to execute the statement at node `n`.
pub(crate) open spec fn m_snode(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, n: usize, g: MG, goal: ER) -> bool {
    &&& r_rc(code, nodes)
    &&& r_state(e, g.s)
    &&& r_mframes(fr, g.ks, code, nodes)
    &&& den(g.ks, bs_exec_node(nodes, n, g.s)) == goal
    &&& done(goal)
}

/// With the result of a sub-computation.
pub(crate) open spec fn m_ret(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, r: Result<BCNum, BcError>, g: MG, goal: ER, d0: MRoot) -> bool {
    &&& r_rc(code, nodes)
    &&& r_ret(r, e, g.x, wants(fr, d0))
    &&& r_mframes(fr, g.ks, code, nodes)
    &&& den(g.ks, g.x) == goal
    &&& done(goal)
}

pub(crate) open spec fn m_step(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, st: Step, g: MG, goal: ER, d0: MRoot) -> bool {
    match st {
        Step::Eval(n) => m_eval(e, fr, code, nodes, n, g, goal),
        Step::Exec(n) => m_exec(e, fr, code, nodes, n, g, goal),
        Step::Ret(r) => m_ret(e, fr, code, nodes, r, g, goal, d0),
        Step::Enter(c, def) => m_body(e, fr, c, g.nodes, def, 0, g, goal),
        Step::Leave(c, r) => m_ret(e, fr, c, g.nodes, r, g, goal, d0),
    }
}

/// About to run the body of the function at node `def`, from statement `i` on.
pub(crate) open spec fn m_body(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, def: usize, i: usize, g: MG, goal: ER) -> bool {
    &&& r_rc(code, nodes)
    &&& r_state(e, g.s)
    &&& r_mframes(fr, g.ks, code, nodes)
    &&& def < nodes.len()
    &&& (nodes[def as int] matches Node::Define(_, _, _, body) && i <= body.len()
        && den(g.ks, bs_body(nodes, body.skip(i as int), g.s)) == goal)
    &&& done(goal)
}

pub(crate) open spec fn step_ok(st: Step, fr: Seq<Frame>, d0: MRoot) -> bool {
    match st {
        Step::Eval(_) => wants(fr, d0),
        Step::Exec(_) => !wants(fr, d0),
        Step::Ret(r) => r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
        Step::Enter(_, _) => fr.len() > 0 && fr.last() is Call,
        Step::Leave(_, r) => r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
    }
}

/// A node that the machine does not split into frames.
pub(crate) open spec fn leaf_node(code: Rc<Code>, n: usize) -> bool {
    n >= code.nodes@.len() || match code.nodes@[n as int] {
        PNode::Neg(_) | PNode::Length(_) | PNode::Sqrt(_) | PNode::ScaleOf(_) | PNode::Paren(_)
        | PNode::Binary(_, _, _) | PNode::Rel(_, _, _) | PNode::Array(_, _)
        | PNode::Assign(_, _, _) | PNode::Update(_, _, _) | PNode::Call(_, _) => false,
        _ => true,
    }
}

/// What a frame holds without any hypothesis.
pub(crate) open spec fn mframe_ok(f: Frame) -> bool {
    match f {
        Frame::BinR(_, v) => v.scale <= BC_SCALE_MAX,
        Frame::RelR(_, v) => v.scale <= BC_SCALE_MAX,
        Frame::OpStore(_, _, v) => v.scale <= BC_SCALE_MAX,
        Frame::ArgVal(_, _, i, vals) => args_ok(vals@) && i < usize::MAX,
        Frame::Call(_, _, _, _, inv, v) => v.scale <= BC_SCALE_MAX && match inv {
            Some(b) => 2 <= b <= IBASE_MAX,
            None => true,
        },
        Frame::MathJ2(v) => v.scale <= BC_SCALE_MAX,
        _ => true,
    }
}

/// After popping the frame `fr`, whose sub-computation gave the value `v`.
pub(crate) open spec fn m_after(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, f: Frame, v: BCNum, k: K, ks: Seq<K>, x: ER, goal: ER) -> bool {
    &&& r_rc(code, nodes)
    &&& x.ok
    &&& r_num(v, x.val)
    &&& r_state(e, x.st)
    &&& r_mframes(fr, ks, code, nodes)
    &&& r_mframe(f, k, code, nodes)
    &&& den(ks, apply(k, x)) == goal
    &&& done(goal)
}

proof fn lemma_frames_pop(fr: Seq<Frame>, cur: usize, d0: MRoot)
    requires
        frames_ok(fr, cur, d0),
        fr.len() > 0,
    ensures
        gives_value(fr.last()) == wants(fr.drop_last(), d0),
        mframe_ok(fr.last()),
        match fr.last() {
            Frame::Depth(d) => d + 1 == cur && frames_ok(fr.drop_last(), d, d0),
            Frame::DepthS(d) => d + 1 == cur && frames_ok(fr.drop_last(), d, d0),
            _ => frames_ok(fr.drop_last(), cur, d0),
        },
{
}

proof fn lemma_frames_push(fr: Seq<Frame>, f: Frame, cur: usize, d0: MRoot)
    requires
        frames_ok(fr, cur, d0),
        gives_value(f) == wants(fr, d0),
        mframe_ok(f),
        !(f is Depth) && !(f is DepthS),
    ensures
        frames_ok(fr.push(f), cur, d0),
        wants(fr.push(f), d0) == takes_value(f),
{
    assert(fr.push(f).drop_last() =~= fr);
}

/// Pushing a frame keeps both relations.
proof fn lemma_push(fr: Seq<Frame>, ks: Seq<K>, f: Frame, k: K, code: Rc<Code>, nodes: SpecNodes)
    requires
        r_mframes(fr, ks, code, nodes),
        r_mframe(f, k, code, nodes),
        !(f is Call),
    ensures
        r_mframes(fr.push(f), ks.push(k), code, nodes),
{
    assert(fr.push(f).drop_last() =~= fr);
    assert(ks.push(k).drop_last() =~= ks);
}

proof fn lemma_push_call(fr: Seq<Frame>, ks: Seq<K>, f: Frame, k: K, caller: Rc<Code>, cn: SpecNodes, code: Rc<Code>, nodes: SpecNodes)
    requires
        r_mframes(fr, ks, caller, cn),
        r_rc(caller, cn),
        f matches Frame::Call(c, _, _, _, _, _) && c == caller,
        k matches K::Call(_, _, n) && n == cn,
        r_call_frame(f, k, code, nodes),
    ensures
        r_mframes(fr.push(f), ks.push(k), code, nodes),
{
    assert(fr.push(f).drop_last() =~= fr);
    assert(ks.push(k).drop_last() =~= ks);
}

proof fn lemma_pop(fr: Seq<Frame>, ks: Seq<K>, code: Rc<Code>, nodes: SpecNodes)
    requires
        r_mframes(fr, ks, code, nodes),
        fr.len() > 0,
    ensures
        ks.len() == fr.len(),
        !(fr.last() is Call) ==> r_mframes(fr.drop_last(), ks.drop_last(), code, nodes) && r_mframe(fr.last(), ks.last(), code, nodes),
        fr.last() matches Frame::Call(caller, _, _, _, _, _) ==> r_call_frame(fr.last(), ks.last(), code, nodes)
            && (ks.last() matches K::Call(_, _, cn) && r_rc(caller, cn) && r_mframes(fr.drop_last(), ks.drop_last(), caller, cn)),
{
}

impl Evaluator {
    /// Continues with the result `r` of a sub-computation: pops one frame.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(40)]
    fn step_ret(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, ret: Result<BCNum, BcError>, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            old(frames)@.len() > 0,
            ret is Ok ==> ret->Ok_0.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_ret(*old(self), old(frames)@, *code, cx.nodes, ret, g, cx.goal, cx.d0) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal; let ghost d0 = cx.d0;
        let ghost hyp = m_ret(*self, frames@, *code, nodes, ret, g, goal, d0);
        let ghost fr0 = frames@;
        let ghost x = g.x;
        let ghost k = g.ks.last();
        let ghost ks1 = g.ks.drop_last();
        let ghost y = apply(k, x);
        let popped = frames.pop();
        proof { if fr0.len() > 0 { assert(popped == Some(fr0.last())); } }
        proof {
            assert(frames@ =~= fr0.drop_last());
            lemma_frames_pop(fr0, self.eval_depth, d0);
            assert(mframe_ok(fr0.last()));
            if hyp {
                lemma_pop(fr0, g.ks, *code, nodes);
                assert(ks1.push(k) =~= g.ks);
                lemma_den_push(ks1, k, x);
                assert(den(ks1, y) == goal);
            }
        }
        let fr = match popped {
            Some(fr) => fr,
            None => { return (Step::Ret(ret), Ghost(g)); },
        };
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: g.s, x: y };
        if let Frame::Call(caller, def, name, flag, inv, sv) = fr {
            return self.ret_call(frames, code, caller, def, name, flag, inv, sv, ret, Ghost(MPop { k: k, ks: ks1, x: x }), Ghost(cx));
        }
        let depth = match fr {
            Frame::Depth(d) => Some(d),
            Frame::DepthS(d) => Some(d),
            _ => None,
        };
        if let Some(d) = depth {
            let ghost before = *self;
            self.eval_depth = d;
            proof {
                if hyp {
                    if ret is Ok {
                        lemma_r_state_depth(before, *self, x.st);
                    } else {
                        lemma_r_state_depth(before, *self, with_depth(x.st, before.eval_depth as u64));
                        assert(with_depth(with_depth(x.st, before.eval_depth as u64), d as u64) == with_depth(x.st, d as u64));
                    }
                }
            }
            return (Step::Ret(ret), Ghost(g1));
        }
        let v = match ret {
            Ok(v) => v,
            Err(e) => { return (Step::Ret(Err(e)), Ghost(g1)); },
        };
        if Self::takes_value_ref(&fr) {
            self.ret_ok(frames, code, fr, v, Ghost(MPop { k: k, ks: ks1, x: x }), Ghost(cx))
        } else {
            self.ret_stmt(frames, code, fr, Ghost(MPop { k: k, ks: ks1, x: x }), Ghost(cx))
        }
    }

    fn takes_value_ref(f: &Frame) -> (r: bool)
        ensures
            r == takes_value(*f),
    {
        !matches!(f, Frame::DepthS(_) | Frame::List(..) | Frame::LoopBody(..) | Frame::Body(..) | Frame::Call(..))
    }

    /// With the value of a sub-computation of the frame `fr`.
    #[verifier::exec_allows_no_decreases_clause]
    fn ret_ok(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, fr: Frame, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            v.scale <= BC_SCALE_MAX,
            mframe_ok(fr),
            takes_value(fr),
            gives_value(fr) == wants(old(frames)@, cx.d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            !(fr is Depth) && m_after(*old(self), old(frames)@, *code, cx.nodes, fr, v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost d0 = cx.d0;
        match fr {
            Frame::Depth(_) => (Step::Ret(Ok(v)), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x })),
            Frame::ArrayIdx(t) => self.ret_arrayidx(frames, code, t, v, Ghost(pop), Ghost(cx)),
            Frame::AssignIdx(t, op, value) => self.ret_assignidx(frames, code, t, op, value, v, Ghost(pop), Ghost(cx)),
            Frame::UpdateIdx(t, inc, prefix) => self.ret_updateidx(frames, code, t, inc, prefix, v, Ghost(pop), Ghost(cx)),
            Frame::Unary(which) => self.ret_unary(frames, code, which, v, Ghost(pop), Ghost(cx)),
            Frame::BinL(op, right) => self.ret_binl(frames, code, op, right, v, Ghost(pop), Ghost(cx)),
            Frame::BinR(op, a) => self.ret_binr(frames, code, op, a, v, Ghost(pop), Ghost(cx)),
            Frame::RelL(op, right) => self.ret_rell(frames, code, op, right, v, Ghost(pop), Ghost(cx)),
            Frame::RelR(op, a) => self.ret_relr(frames, code, op, a, v, Ghost(pop), Ghost(cx)),
            Frame::Store(place) => self.ret_store(frames, code, place, v, Ghost(pop), Ghost(cx)),
            Frame::OpStore(place, op, a) => self.ret_opstore(frames, code, place, op, a, v, Ghost(pop), Ghost(cx)),
            Frame::ExprStmt(e) => self.ret_exprstmt(frames, code, e, v, Ghost(pop), Ghost(cx)),
            Frame::Return => self.ret_return(frames, code, v, Ghost(pop), Ghost(cx)),
            Frame::IfCond(b) => self.ret_ifcond(frames, code, b, v, Ghost(pop), Ghost(cx)),
            Frame::ForInit(c, p, b) => self.loop_start(frames, code, c, Some(p), b, Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x }), Ghost(cx)),
            Frame::LoopCond(c, p, b) => self.ret_loopcond(frames, code, c, p, b, v, Ghost(pop), Ghost(cx)),
            Frame::LoopPost(c, p, b) => self.loop_start(frames, code, c, p, b, Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x }), Ghost(cx)),
            Frame::ArgVal(fd, n, i, vals) => self.ret_argval(frames, code, fd, n, i, vals, v, Ghost(pop), Ghost(cx)),
            Frame::Math1(n) => (Step::Ret(self.finish_math1(code, n, v)), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x })),
            Frame::MathJ1(n) => {
                if n < code.nodes.len() {
                    if let PNode::Call(_, args) = &code.nodes[n] {
                        if args.len() == 2 {
                            if let PArg::Expr(e) = &args[1] {
                                let e = *e;
                                let ghost f0 = frames@;
                                frames.push(Frame::MathJ2(v));
                                proof { assert(frames@.drop_last() =~= f0); assert(frames_ok(frames@, self.eval_depth, d0)); }
                                return (Step::Eval(e), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x }));
                            }
                        }
                    }
                }
                (Step::Ret(Ok(v)), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x }))
            },
            Frame::MathJ2(a) => (Step::Ret(self.finish_bessel(&a, &v)), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x })),
            _ => (Step::Ret(Ok(v)), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x })),
        }
    }

    /// With the result of a statement, for a frame that takes one.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(40)]
    fn ret_stmt(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, fr: Frame, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            !takes_value(fr),
            gives_value(fr) == wants(old(frames)@, cx.d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            !(fr is DepthS) && m_after_s(*old(self), old(frames)@, *code, cx.nodes, fr, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after_s(*self, frames@, *code, nodes, fr, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); } }
        match fr {
            Frame::List(n, i) => {
                if self.break_flag || self.return_flag {
                    return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y }));
                }
                self.list_next(frames, code, n, i, Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y }), Ghost(cx))
            },
            Frame::LoopBody(c, p, b) => {
                let (should_break, next_break) = verified_loop_post_body_action(self.break_flag, self.return_flag, self.quit_flag);
                self.break_flag = next_break;
                let ghost st2 = bc_spec::eval::with_flags(x.st, false, x.st.ret, x.st.ret_val);
                if should_break {
                    return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: ks1, s: st2, x: y }));
                }
                match p {
                    Some(post) => {
                        let ghost kp = K::LoopPost(nodes, c, post, true, b);
                        self.push_sub(frames, code, Frame::LoopPost(c, p, b), post, Ghost(kp), Ghost(MG { nodes: nodes, ks: ks1, s: st2, x: y }), Ghost(y), Ghost(cx))
                    },
                    None => self.loop_start(frames, code, c, None, b, Ghost(MG { nodes: nodes, ks: ks1, s: st2, x: y }), Ghost(cx)),
                }
            },
            Frame::Body(def, i) => self.ret_body(frames, code, def, i, Ghost(pop), Ghost(cx)),
            _ => (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y })),
        }
    }

    /// Runs the machine from `start` until its stack is empty.
    #[verifier::exec_allows_no_decreases_clause]
    fn run(&mut self, code: &Rc<Code>, start: Step, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>, Ghost(goal): Ghost<MResult>, Ghost(e): Ghost<bool>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            step_ok(start, Seq::empty(), MRoot { d: old(self).eval_depth, e }),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            m_step(*old(self), Seq::empty(), *code, nodes, start, MG { nodes: nodes, ks: Seq::empty(), s: st, x: goal }, goal, MRoot { d: old(self).eval_depth, e })
                ==> r_ret(r, *final(self), goal, e),
    {
        let ghost d0 = MRoot { d: self.eval_depth, e };
        let ghost hyp = m_step(*self, Seq::empty(), *code, nodes, start, MG { nodes: nodes, ks: Seq::empty(), s: st, x: goal }, goal, d0);
        let mut frames: Vec<Frame> = Vec::new();
        let mut step = start;
        let mut cur = share_code(code);
        let ghost mut ns = nodes;
        let ghost mut g = MG { nodes: nodes, ks: Seq::empty(), s: st, x: goal };
        proof {
            assert(frames@ =~= Seq::<Frame>::empty());
            assert(frames_ok(frames@, self.eval_depth, d0));
        }
        loop
            invariant
                self.inv(),
                frames_ok(frames@, self.eval_depth, d0),
                step_ok(step, frames@, d0),
                d0 == (MRoot { d: old(self).eval_depth, e }),
                hyp == m_step(*old(self), Seq::empty(), *code, nodes, start, MG { nodes: nodes, ks: Seq::empty(), s: st, x: goal }, goal, d0),
                hyp ==> m_step(*self, frames@, cur, ns, step, g, goal, d0),
        {
            match step {
                Step::Eval(j) => {
                    let (next, Ghost(g2)) = self.step_eval(&mut frames, &cur, j, Ghost(g), Ghost(MCx { nodes: ns, goal: goal, d0: d0 }));
                    step = next;
                    proof { g = g2; }
                },
                Step::Exec(j) => {
                    let (next, Ghost(g2)) = self.step_exec(&mut frames, &cur, j, Ghost(g), Ghost(MCx { nodes: ns, goal: goal, d0: d0 }));
                    step = next;
                    proof { g = g2; }
                },
                Step::Enter(c, def) => {
                    cur = c;
                    proof { ns = g.nodes; }
                    let (next, Ghost(g2)) = self.body_next(&mut frames, &cur, def, 0, Ghost(g), Ghost(MCx { nodes: ns, goal: goal, d0: d0 }));
                    step = next;
                    proof { g = g2; }
                },
                Step::Leave(c, res) => {
                    cur = c;
                    proof { ns = g.nodes; }
                    step = Step::Ret(res);
                },
                Step::Ret(res) => {
                    if frames.len() == 0 {
                        proof {
                            if hyp {
                                assert(g.ks =~= Seq::<K>::empty());
                            }
                        }
                        return res;
                    }
                    let (next, Ghost(g2)) = self.step_ret(&mut frames, &cur, res, Ghost(g), Ghost(MCx { nodes: ns, goal: goal, d0: d0 }));
                    step = next;
                    proof { g = g2; }
                },
            }
        }
    }

    /// Evaluates node `n` (the specification's `ev`, at the current depth).
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_ref(
        &mut self,
        code: &Rc<Code>,
        n: usize,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_rc(*code, nodes)) ==> forall|f: u64|
                done(#[trigger] ev(nodes, n, st, f)) ==> r_result(r, *final(self), ev(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost goal = bs_ev(nodes, n, st);
        let ghost e0 = *self;
        proof {
            assert(r_mframes(Seq::<Frame>::empty(), Seq::<K>::empty(), *code, nodes));
        }
        let r = self.run(code, Step::Eval(n), Ghost(nodes), Ghost(st), Ghost(goal), Ghost(true));
        proof {
            if r_state(e0, st) && r_rc(*code, nodes) {
                assert forall|f: u64| done(#[trigger] ev(nodes, n, st, f)) implies r_result(r, *self, ev(nodes, n, st, f), e0.eval_depth) by {
                    lemma_bs_ev(nodes, n, st, f);
                }
            }
        }
        r
    }

    /// Executes node `n` (the specification's `exec`, at the current depth).
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn exec_ref(
        &mut self,
        code: &Rc<Code>,
        n: usize,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_rc(*code, nodes)) ==> forall|f: u64|
                done(#[trigger] exec(nodes, n, st, f)) ==> r_unit(r, *final(self), exec(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost goal = bs_exec(nodes, n, st);
        let ghost e0 = *self;
        proof {
            assert(r_mframes(Seq::<Frame>::empty(), Seq::<K>::empty(), *code, nodes));
        }
        let r = if Self::quick_stmt_ok(code, n, QUICK_BUDGET) {
            self.quick_exec(code, n, QUICK_BUDGET, Ghost(nodes), Ghost(st))
        } else {
            match self.run(code, Step::Exec(n), Ghost(nodes), Ghost(st), Ghost(goal), Ghost(false)) {
                Ok(_) => Ok(()),
                Err(e) => Err(e),
            }
        };
        proof {
            if r_state(e0, st) && r_rc(*code, nodes) {
                assert forall|f: u64| done(#[trigger] exec(nodes, n, st, f)) implies r_unit(r, *self, exec(nodes, n, st, f), e0.eval_depth) by {
                    lemma_bs_exec(nodes, n, st, f);
                }
            }
        }
        r
    }
}

} // verus!
