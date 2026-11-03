// SPDX-License-Identifier: MIT

//! The evaluator's machine: expressions run on an explicit stack of frames, so the depth of an
//! evaluation does not depend on the native stack.
//!
//! A frame is what remains to do of one syntactic form once a sub-computation has a result.
//! The proof relates a frame to the specification's `bc_spec::den::K` (`r_frame`) and keeps the
//! meaning of the machine's state, `den(ks, ...)`, equal to the result of the whole evaluation
//! (`m_eval`, `m_node`, `m_ret`). So the theorem of `eval_ref` has the form it had when the
//! evaluator recursed.

use super::*;
#[cfg(verus_keep_ghost)]
use bc_spec::den::*;

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
}

/// What the machine does next.
pub(crate) enum Step {
    Eval(usize),
    Exec(usize),
    Ret(Result<BCNum, BcError>),
}

#[cfg(not(verus_keep_ghost))]
pub(crate) type MG = ();
#[cfg(not(verus_keep_ghost))]
pub(crate) type MRoot = ();
#[cfg(verus_keep_ghost)]
pub(crate) type MK = K;
#[cfg(verus_keep_ghost)]
pub(crate) type MKs = Seq<K>;
#[cfg(not(verus_keep_ghost))]
pub(crate) type MKs = ();
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

/// Whether the frame takes the result of an expression (a value) rather than of a statement.
pub(crate) open spec fn takes_value(f: Frame) -> bool {
    !(f is DepthS || f is List || f is LoopBody)
}

/// Whether the frame's own result is that of an expression.
pub(crate) open spec fn gives_value(f: Frame) -> bool {
    !(f is DepthS || f is List || f is LoopBody || f is ExprStmt || f is Return || f is IfCond
        || f is ForInit || f is LoopCond || f is LoopPost)
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
        &&& frame_ok(fr.last())
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
    }
}

/// The post-expression of a loop as the specification gives it (0 for a `while`).
pub(crate) open spec fn opt_index(p: Option<usize>) -> usize {
    match p {
        Some(i) => i,
        None => 0usize,
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

pub(crate) open spec fn r_mframes(fr: Seq<Frame>, ks: Seq<K>, code: Rc<Code>, nodes: SpecNodes) -> bool {
    fr.len() == ks.len() && forall|i: int| 0 <= i < fr.len() ==> #[trigger] r_mframe(fr[i], ks[i], code, nodes)
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
    }
}

pub(crate) open spec fn step_ok(st: Step, fr: Seq<Frame>, d0: MRoot) -> bool {
    match st {
        Step::Eval(_) => wants(fr, d0),
        Step::Exec(_) => !wants(fr, d0),
        Step::Ret(r) => r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
    }
}

/// A node that the machine does not split into frames.
pub(crate) open spec fn leaf_node(code: Rc<Code>, n: usize) -> bool {
    n >= code.nodes@.len() || match code.nodes@[n as int] {
        PNode::Neg(_) | PNode::Length(_) | PNode::Sqrt(_) | PNode::ScaleOf(_) | PNode::Paren(_)
        | PNode::Binary(_, _, _) | PNode::Rel(_, _, _) | PNode::Array(_, _)
        | PNode::Assign(_, _, _) | PNode::Update(_, _, _) => false,
        _ => true,
    }
}

/// What a frame holds without any hypothesis.
pub(crate) open spec fn frame_ok(f: Frame) -> bool {
    match f {
        Frame::BinR(_, v) => v.scale <= BC_SCALE_MAX,
        Frame::RelR(_, v) => v.scale <= BC_SCALE_MAX,
        Frame::OpStore(_, _, v) => v.scale <= BC_SCALE_MAX,
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
        frame_ok(fr.last()),
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
        frame_ok(f),
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
    ensures
        r_mframes(fr.push(f), ks.push(k), code, nodes),
{
    assert forall|i: int| 0 <= i < fr.len() + 1 implies #[trigger] r_mframe(fr.push(f)[i], ks.push(k)[i], code, nodes) by {
        if i < fr.len() {
            assert(r_mframe(fr[i], ks[i], code, nodes));
        }
    }
}

proof fn lemma_pop(fr: Seq<Frame>, ks: Seq<K>, code: Rc<Code>, nodes: SpecNodes)
    requires
        r_mframes(fr, ks, code, nodes),
        fr.len() > 0,
    ensures
        r_mframes(fr.drop_last(), ks.drop_last(), code, nodes),
        r_mframe(fr.last(), ks.last(), code, nodes),
{
    assert(r_mframe(fr[fr.len() - 1], ks[ks.len() - 1], code, nodes));
    assert forall|i: int| 0 <= i < fr.len() - 1 implies #[trigger] r_mframe(fr.drop_last()[i], ks.drop_last()[i], code, nodes) by {
        assert(r_mframe(fr[i], ks[i], code, nodes));
    }
}

impl Evaluator {
    /// The result of a form that needs no sub-computation on the machine.
    #[verifier::exec_allows_no_decreases_clause]
    fn leaf_result(&mut self, code: &Rc<Code>, n: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            leaf_node(*code, n),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_rc(*code, nodes) && done(bs_ev_node(nodes, n, st))) ==> r_result(r, *final(self), bs_ev_node(nodes, n, st), old(self).eval_depth),
    {
        let r = self.eval_node_ref(code, n, Ghost(nodes), Ghost(st));
        proof {
            if done(bs_ev_node(nodes, n, st)) {
                let f = choose|f: u64| done(#[trigger] ev_node(nodes, n, st, f));
                assert(done(ev_node(nodes, n, st, f)));
            }
        }
        r
    }

    /// Enters the evaluation of node `n`: its nesting level, then its form.
    #[verifier::exec_allows_no_decreases_clause]
    fn step_eval(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_eval(*old(self), old(frames)@, *code, nodes, n, g, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_eval(*self, frames@, *code, nodes, n, g, goal);
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_depth) {
            let ghost x = bs_ev(nodes, n, g.s);
            let r = Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
            proof {
                if hyp {
                    lemma_ev_too_deep(nodes, n, g.s);
                    assert(with_depth(g.s, self.eval_depth as u64) == g.s);
                }
            }
            return (Step::Ret(r), Ghost(MG { ks: g.ks, s: g.s, x }));
        }
        let ghost before = *self;
        let ghost f0 = frames@;
        let ghost s1 = with_depth(g.s, (g.s.depth + 1) as u64);
        let ghost k = K::Depth(g.s.depth);
        proof {
            if hyp {
                lemma_den_done(g.ks, bs_ev(nodes, n, g.s));
                lemma_step_ev(nodes, n, g.s);
                lemma_den_push(g.ks, k, bs_ev_node(nodes, n, s1));
            }
        }
        frames.push(Frame::Depth(self.eval_depth));
        self.eval_depth += 1;
        proof {
            assert(frames@.drop_last() =~= f0);
            assert(frames_ok(frames@, self.eval_depth, d0));
            assert(wants(frames@, d0));
            if hyp {
                lemma_r_state_depth(before, *self, g.s);
                lemma_push(f0, g.ks, Frame::Depth(before.eval_depth), k, *code, nodes);
                lemma_den_done(g.ks.push(k), bs_ev_node(nodes, n, s1));
            }
        }
        self.step_node(frames, code, n, Ghost(nodes), Ghost(MG { ks: g.ks.push(k), s: s1, x: g.x }), Ghost(goal), Ghost(d0))
    }

    /// A form whose first sub-computation is node `child`.
    #[verifier::exec_allows_no_decreases_clause]
    fn push_sub(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, f: Frame, child: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(parent): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            frame_ok(f),
            !(f is Depth) && !(f is DepthS),
            gives_value(f) == wants(old(frames)@, d0),
            takes_value(f),
        ensures
            *final(self) == *old(self),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            (r_rc(*code, nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, nodes)
                && r_mframe(f, k, *code, nodes) && done(goal) && den(g.ks, parent) == goal
                && (done(parent) ==> parent == apply(k, bs_ev(nodes, child, g.s))))
                ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost f0 = frames@;
        let ghost fv = f;
        frames.push(f);
        proof {
            assert(frames@ == f0.push(fv));
            lemma_frames_push(f0, fv, self.eval_depth, d0);
            if r_rc(*code, nodes) && r_state(*self, g.s) && r_mframes(f0, g.ks, *code, nodes)
                && r_mframe(fv, k, *code, nodes) && done(goal) && den(g.ks, parent) == goal
                && (done(parent) ==> parent == apply(k, bs_ev(nodes, child, g.s))) {
                lemma_den_done(g.ks, parent);
                lemma_den_push(g.ks, k, bs_ev(nodes, child, g.s));
                lemma_push(f0, g.ks, fv, k, *code, nodes);
            }
        }
        (Step::Eval(child), Ghost(MG { ks: g.ks.push(k), s: g.s, x: g.x }))
    }

    /// One step of a form (the specification's `ev_node`).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(30)]
    fn step_node(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_node(*old(self), old(frames)@, *code, nodes, n, g, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_node(*self, frames@, *code, nodes, n, g, goal);
        let ghost parent = bs_ev_node(nodes, n, g.s);
        proof {
            if hyp {
                lemma_den_done(g.ks, parent);
                if n < nodes.len() {
                    assert(r_node(code.nodes@[n as int], nodes[n as int]));
                }
            }
        }
        if n < code.nodes.len() {
            match &code.nodes[n] {
                PNode::Neg(e) => {
                    proof { if hyp { lemma_step_unary(nodes, n, 0u8, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::Unary(0), *e, Ghost(nodes), Ghost(K::Unary(0u8)), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::Length(e) => {
                    proof { if hyp { lemma_step_unary(nodes, n, 1u8, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::Unary(1), *e, Ghost(nodes), Ghost(K::Unary(1u8)), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::Sqrt(e) => {
                    proof { if hyp { lemma_step_unary(nodes, n, 2u8, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::Unary(2), *e, Ghost(nodes), Ghost(K::Unary(2u8)), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::ScaleOf(e) => {
                    proof { if hyp { lemma_step_unary(nodes, n, 3u8, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::Unary(3), *e, Ghost(nodes), Ghost(K::Unary(3u8)), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::Paren(e) => {
                    proof { if hyp { lemma_step_paren(nodes, n, *e, g.s); } }
                    return (Step::Eval(*e), Ghost(g));
                },
                PNode::Binary(op, l, r) => {
                    let ghost k = K::BinL(nodes, bin_code(*op), *r);
                    proof { if hyp { lemma_step_binary(nodes, n, bin_code(*op), *l, *r, g.s); } }
                    return self.push_sub(frames, code, Frame::BinL(*op, *r), *l, Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::Rel(op, l, r) => {
                    let ghost k = K::RelL(nodes, rel_code(*op), *r);
                    proof { if hyp { lemma_step_rel(nodes, n, rel_code(*op), *l, *r, g.s); } }
                    return self.push_sub(frames, code, Frame::RelL(*op, *r), *l, Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::Array(name, i) => {
                    let ghost k = K::ArrayIdx(text_view(*name));
                    proof { if hyp { lemma_step_array(nodes, n, text_view(*name), *i, g.s); } }
                    return self.push_sub(frames, code, Frame::ArrayIdx(n), *i, Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::Assign(op, t, v) => {
                    return self.step_assign(frames, code, n, *op, *t, *v, Ghost(nodes), Ghost(g), Ghost(goal), Ghost(d0));
                },
                PNode::Update(inc, prefix, t) => {
                    return self.step_update(frames, code, n, *inc, *prefix, *t, Ghost(nodes), Ghost(g), Ghost(goal), Ghost(d0));
                },
                _ => {},
            }
        }
        let r = self.leaf_result(code, n, Ghost(nodes), Ghost(g.s));
        proof { if hyp { assert(r_mframes(frames@, g.ks, *code, nodes)); } }
        (Step::Ret(r), Ghost(MG { ks: g.ks, s: g.s, x: parent }))
    }

    /// An assignment: its target, then its value.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn step_assign(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, op: AssignOp, t: usize, v: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Assign(op, t, v),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_node(*old(self), old(frames)@, *code, nodes, n, g, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_node(*self, frames@, *code, nodes, n, g, goal);
        let ghost parent = bs_ev_node(nodes, n, g.s);
        proof {
            if hyp {
                lemma_den_done(g.ks, parent);
                assert(r_node(code.nodes@[n as int], nodes[n as int]));
                if t < nodes.len() { assert(r_node(code.nodes@[t as int], nodes[t as int])); }
            }
        }
        if t < code.nodes.len() {
            if let PNode::Array(name, i) = &code.nodes[t] {
                let ghost k = K::AssignIdx(nodes, text_view(*name), assign_code(op), v);
                proof { if hyp { lemma_step_assign_elem(nodes, n, assign_code(op), text_view(*name), *i, t, v, g.s); } }
                return self.push_sub(frames, code, Frame::AssignIdx(t, op, v), *i, Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
            }
        }
        let place = self.plain_place_ref(code, t, Ghost(nodes));
        let ghost sp = plain_place(nodes, t);
        proof { if hyp { lemma_step_assign_plain(nodes, n, assign_code(op), t, v, g.s); } }
        self.assign_to_ref(frames, code, op, v, place, Ghost(nodes), Ghost(sp), Ghost(g), Ghost(goal), Ghost(d0))
    }

    /// The place of a target that is not a subscript.
    fn plain_place_ref(&self, code: &Rc<Code>, t: usize, Ghost(nodes): Ghost<SpecNodes>) -> (p: Place)
        ensures
            (r_rc(*code, nodes) && !is_subscript(nodes, t)) ==> r_place(p, plain_place(nodes, t)),
    {
        proof { if r_rc(*code, nodes) && t < nodes.len() { assert(r_node(code.nodes@[t as int], nodes[t as int])); } }
        if t < code.nodes.len() {
            match &code.nodes[t] {
                PNode::Var(name) => { return Place::Variable(name.clone()); },
                PNode::Reg(reg) => { return Place::Register(*reg); },
                _ => {},
            }
        }
        Self::empty_place()
    }

    /// A single hexadecimal digit assigned to `ibase` or `obase` (`single_digit_base`), and its value.
    fn single_digit_ref(code: &Rc<Code>, place: &Place, op: AssignOp, v: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(sp): Ghost<SpecPlace>) -> (hex: Option<usize>)
        ensures
            hex is Some ==> hex->Some_0 < 16,
            (r_rc(*code, nodes) && r_place(*place, sp)) ==> match hex {
                Some(h) => bc_spec::eval::single_digit_base(nodes, sp, assign_code(op), v) && h == bc_spec::eval::hex_val(bc_spec::eval::number_text(nodes, v)[0]),
                None => !bc_spec::eval::single_digit_base(nodes, sp, assign_code(op), v),
            },
    {
        proof { if r_rc(*code, nodes) && v < nodes.len() { assert(r_node(code.nodes@[v as int], nodes[v as int])); } }
        match (place, op) {
            (Place::Register(Register::Ibase), AssignOp::Assign)
            | (Place::Register(Register::Obase), AssignOp::Assign) => {
                if v < code.nodes.len() {
                    match &code.nodes[v] {
                        PNode::Number(digits) => {
                            let b = digits.as_str().as_bytes();
                            if b.len() == 1 { Some(verified_hex_char_val(b[0])) } else { None }
                        },
                        _ => None,
                    }
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    /// The assignment once its target is known (the specification's `assign_to`).
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn assign_to_ref(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: AssignOp, v: usize, place: Place, Ghost(nodes): Ghost<SpecNodes>, Ghost(sp): Ghost<SpecPlace>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            (r_rc(*code, nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, nodes) && r_place(place, sp) && done(goal)
                && den(g.ks, assign_to(nodes, assign_code(op), v, sp, g.s)) == goal)
                ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, g.s) && r_mframes(frames@, g.ks, *code, nodes) && r_place(place, sp) && done(goal)
            && den(g.ks, assign_to(nodes, assign_code(op), v, sp, g.s)) == goal;
        let ghost parent = assign_to(nodes, assign_code(op), v, sp, g.s);
        let ghost acode = assign_code(op);
        proof { if hyp { lemma_den_done(g.ks, parent); } }
        let hex = Self::single_digit_ref(code, &place, op, v, Ghost(nodes), Ghost(sp));
        if let Some(h) = hex {
            let val = BCNum::new(big_from_usize(h), 0);
            let ghost sv = num_u64(bc_spec::eval::hex_val(if bc_spec::eval::number_text(nodes, v).len() > 0 { bc_spec::eval::number_text(nodes, v)[0] } else { 0u8 }));
            proof { if hyp { lemma_u64_mag(h as u64); } }
            let res = val.copy();
            let _ = self.store_ref(place, val, Ghost(sp), Ghost(g.s), Ghost(sv));
            return (Step::Ret(Ok(res)), Ghost(MG { ks: g.ks, s: g.s, x: parent }));
        }
        match op {
            AssignOp::Assign => {
                proof { if hyp { assert(acode == 0); } }
                self.push_sub(frames, code, Frame::Store(place), v, Ghost(nodes), Ghost(K::Store(sp)), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0))
            },
            AssignOp::Compound(bin) => {
                let old_v = self.load_ref(&place, Ghost(sp), Ghost(g.s));
                let ghost k = K::OpStore(sp, bin_code(bin), bc_spec::eval::load(g.s, sp));
                proof { if hyp { assert(acode != 0); assert((acode - 1) as u8 == bin_code(bin)); } }
                self.push_sub(frames, code, Frame::OpStore(place, bin, old_v), v, Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0))
            },
        }
    }

    /// `++`/`--`.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn step_update(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, inc: bool, prefix: bool, t: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Update(inc, prefix, t),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_node(*old(self), old(frames)@, *code, nodes, n, g, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_node(*self, frames@, *code, nodes, n, g, goal);
        let ghost parent = bs_ev_node(nodes, n, g.s);
        proof {
            if hyp {
                lemma_den_done(g.ks, parent);
                assert(r_node(code.nodes@[n as int], nodes[n as int]));
                if t < nodes.len() { assert(r_node(code.nodes@[t as int], nodes[t as int])); }
            }
        }
        if t < code.nodes.len() {
            if let PNode::Array(name, i) = &code.nodes[t] {
                let ghost k = K::UpdateIdx(text_view(*name), inc, prefix);
                proof { if hyp { lemma_step_update_elem(nodes, n, inc, prefix, text_view(*name), *i, t, g.s); } }
                return self.push_sub(frames, code, Frame::UpdateIdx(t, inc, prefix), *i, Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
            }
        }
        let place = self.plain_place_ref(code, t, Ghost(nodes));
        let ghost sp = plain_place(nodes, t);
        proof { if hyp { lemma_step_update_plain(nodes, n, inc, prefix, t, g.s); } }
        let v = self.update_at_ref(inc, prefix, place, Ghost(sp), Ghost(g.s));
        (Step::Ret(Ok(v)), Ghost(MG { ks: g.ks, s: g.s, x: parent }))
    }

    /// `++`/`--` once its target is known (the specification's `update_at`).
    fn update_at_ref(&mut self, increment: bool, prefix: bool, place: Place, Ghost(sp): Ghost<SpecPlace>, Ghost(st): Ghost<SpecState>) -> (r: BCNum)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_place(place, sp)) ==> ({
                let u = update_at(increment, prefix, sp, st);
                u.ok && r_num(r, u.val) && r_state(*final(self), u.st)
            }),
    {
        let ghost hyp = r_state(*self, st) && r_place(place, sp);
        let ghost sold = bc_spec::eval::load(st, sp);
        let old_val = self.load_ref(&place, Ghost(sp), Ghost(st));
        let step = BCNum::new(big_from_usize(1), 0);
        let new_val = if increment { old_val.add(&step) } else { old_val.sub(&step) };
        let ghost snew = if increment { num_add(sold, one_num()) } else { num_sub(sold, one_num()) };
        proof {
            if hyp {
                lemma_one_mag();
                if increment { lemma_num_add(sold, one_num()); } else { lemma_num_sub(sold, one_num()); }
            }
        }
        let stored = self.store_ref(place, new_val, Ghost(sp), Ghost(st), Ghost(snew));
        if prefix { stored } else { old_val }
    }

    /// `-e`, `length(e)`, `sqrt(e)` or `scale(e)` of the value `v` (the frame `K::Unary`).
    fn finish_unary(&self, which: u8, v: BCNum, Ghost(x): Ghost<MResult>) -> (r: Result<BCNum, BcError>)
        requires
            self.inv(),
            v.scale <= BC_SCALE_MAX,
        ensures
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*self, x.st) && x.ok && r_num(v, x.val)) ==> r_result(r, *self, apply(K::Unary(which), x), self.eval_depth),
    {
        let ghost hyp = r_state(*self, x.st) && x.ok && r_num(v, x.val);
        if which == 0 {
            let w = BCNum::new(big_neg(&v.coeff), v.scale);
            proof {
                if hyp {
                    lemma_is_zero_mag(x.val.mag);
                    assert(r_num(w, negate(x.val)));
                }
            }
            Ok(w)
        } else if which == 1 {
            let w = v.length();
            proof {
                if hyp {
                    let a = x.val;
                    axiom_bigint_size(&v.coeff);
                    lemma_mag_bounds(a.mag);
                    lemma_num_length(a);
                    let lr = num_length(a);
                    lemma_pow10_pos(a.scale as nat);
                    let ip = mag_val(a.mag) / spec_num::pow10(a.scale as nat);
                    if ip > 0 {
                        lemma_digit_count_unique(ip, (big_view(&w.coeff) - a.scale) as nat, (mag_val(lr.mag) - a.scale) as nat);
                    }
                    assert(r_num(w, lr));
                }
            }
            Ok(w)
        } else if which == 3 {
            let w = v.scale_func();
            proof {
                if hyp {
                    lemma_num_scale(x.val);
                    assert(r_num(w, num_scale(x.val)));
                }
            }
            Ok(w)
        } else {
            let r1 = v.try_sqrt(self.scale);
            let r = match r1 {
                Ok(w) => Ok(w),
                Err(k) => Err(BcError::Runtime { kind: k, func: None }),
            };
            proof {
                if hyp {
                    let a = x.val;
                    lemma_num_sqrt(a, x.st.scale);
                    assert(with_depth(x.st, self.eval_depth as u64) == x.st);
                    match num_sqrt(a, x.st.scale) {
                        NumRes::Ok(q) => {
                            let w = r->Ok_0;
                            let sr = w.scale;
                            lemma_isqrt_unique(num_coeff(a) * spec_num::pow10((2 * sr - a.scale) as nat), big_view(&w.coeff), num_coeff(q));
                            assert(r_num(w, q));
                        },
                        _ => {},
                    }
                }
            }
            r
        }
    }

    /// A comparison (the frame `K::RelR`).
    fn finish_rel(op: RelOp, l: &BCNum, r: &BCNum, Ghost(a): Ghost<SpecNum>, Ghost(b): Ghost<SpecNum>) -> (v: BCNum)
        requires
            l.scale <= BC_SCALE_MAX,
            r.scale <= BC_SCALE_MAX,
        ensures
            v.scale <= BC_SCALE_MAX,
            (r_num(*l, a) && r_num(*r, b)) ==> r_num(v, if rel_holds(rel_code(op), bc_spec::num::num_cmp(a, b)) { one_num() } else { bc_spec::eval::zero_num() }),
    {
        let ord = l.cmp_val(r);
        let holds = match op {
            RelOp::Eq => matches!(ord, Ordering::Equal),
            RelOp::Ne => !matches!(ord, Ordering::Equal),
            RelOp::Lt => matches!(ord, Ordering::Less),
            RelOp::Le => !matches!(ord, Ordering::Greater),
            RelOp::Gt => matches!(ord, Ordering::Greater),
            RelOp::Ge => !matches!(ord, Ordering::Less),
        };
        let v = BCNum::new(big_from_usize(if holds { 1 } else { 0 }), 0);
        proof {
            if r_num(*l, a) && r_num(*r, b) {
                lemma_one_mag();
                lemma_u64_mag(0);
                lemma_num_cmp(a, b);
                assert(holds == rel_holds(rel_code(op), bc_spec::num::num_cmp(a, b)));
            }
        }
        v
    }

    /// An element of an array (the frame `K::ArrayIdx`).
    fn finish_array(&mut self, name: &String, v: BCNum, Ghost(x): Ghost<MResult>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), x.st) && x.ok && r_num(v, x.val)) ==> r_result(r, *final(self), apply(K::ArrayIdx(text_view(*name)), x), old(self).eval_depth),
    {
        let ghost hyp = r_state(*self, x.st) && x.ok && r_num(v, x.val);
        let i = match Self::array_index_ref(name, &v) {
            Ok(i) => i,
            Err(e) => {
                proof { if hyp { assert(r_num(v, x.val)); assert(with_depth(x.st, self.eval_depth as u64) == x.st); } }
                return Err(e);
            },
        };
        let w = self.arr_get(name, i);
        proof {
            if hyp {
                assert(r_num(v, x.val));
                let nm = text_view(*name);
                lemma_array_index_value(x.val);
                let idx = array_index(x.val).1;
                assert(i == idx && (idx as int) < 16777216);
                lemma_arr_top(x.st.arrays, nm);
                lemma_elem_get(arr_top(x.st.arrays, nm).elems, idx);
                let m = self.arrays@;
                if m.contains_key(*name) {
                    let ss = arr_lookup(x.st.arrays, nm)->Some_0;
                    assert(r_frames(m[*name]@, ss));
                    if ss.len() > 0 {
                        assert(r_frame(m[*name]@[ss.len() - 1]@, ss[ss.len() - 1]));
                        assert(i < 16777216);
                    }
                } else {
                    lemma_arr_absent(m, x.st.arrays, *name);
                }
                assert(r_num(w, elem_get(arr_top(x.st.arrays, nm).elems, idx)));
            }
        }
        Ok(w)
    }

    /// Storing the value of an assignment (the frame `K::Store`).
    fn finish_store(&mut self, place: Place, val: BCNum, Ghost(sp): Ghost<SpecPlace>, Ghost(x): Ghost<MResult>) -> (r: BCNum)
        requires
            old(self).inv(),
            val.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r.scale <= BC_SCALE_MAX,
            (r_state(*old(self), x.st) && x.ok && r_num(val, x.val) && r_place(place, sp)) ==> r_result(Ok(r), *final(self), store_k(sp, x), old(self).eval_depth),
    {
        let r = val.copy();
        let _ = self.store_ref(place, val, Ghost(sp), Ghost(x.st), Ghost(x.val));
        r
    }

    /// Continues with the result `r` of a sub-computation: pops one frame.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(40)]
    fn step_ret(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, ret: Result<BCNum, BcError>, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            old(frames)@.len() > 0,
            ret is Ok ==> ret->Ok_0.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_ret(*old(self), old(frames)@, *code, nodes, ret, g, goal, d0) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
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
            assert(frame_ok(fr0.last()));
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
        let ghost g1 = MG { ks: ks1, s: g.s, x: y };
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
            self.ret_ok(frames, code, fr, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0))
        } else {
            self.ret_stmt(frames, code, fr, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0))
        }
    }

    fn takes_value_ref(f: &Frame) -> (r: bool)
        ensures
            r == takes_value(*f),
    {
        !matches!(f, Frame::DepthS(_) | Frame::List(..) | Frame::LoopBody(..))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_arrayidx(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, t: usize, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::ArrayIdx(t), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::ArrayIdx(t), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                if t < code.nodes.len() {
                    if let PNode::Array(name, _) = &code.nodes[t] {
                        let r = self.finish_array(name, v, Ghost(x));
                        return (Step::Ret(r), Ghost(g1));
                    }
                }
                (Step::Ret(Ok(v)), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_assignidx(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, t: usize, op: AssignOp, value: usize, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::AssignIdx(t, op, value), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::AssignIdx(t, op, value), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                if t < code.nodes.len() {
                    if let PNode::Array(name, _) = &code.nodes[t] {
                        let i = match Self::array_index_ref(name, &v) {
                            Ok(i) => i,
                            Err(e) => {
                                proof { if hyp { assert(r_num(v, x.val)); assert(with_depth(x.st, self.eval_depth as u64) == x.st); } }
                                return (Step::Ret(Err(e)), Ghost(g1));
                            },
                        };
                        let ghost sp = elem_place(text_view(*name), x);
                        let place = Place::Element(name.clone(), i);
                        proof { if hyp { assert(r_num(v, x.val)); lemma_array_index_value(x.val); } }
                        return self.assign_to_ref(frames, code, op, value, place, Ghost(nodes), Ghost(sp), Ghost(MG { ks: ks1, s: x.st, x: x }), Ghost(goal), Ghost(d0));
                    }
                }
                (Step::Ret(Ok(v)), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_updateidx(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, t: usize, inc: bool, prefix: bool, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::UpdateIdx(t, inc, prefix), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::UpdateIdx(t, inc, prefix), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                if t < code.nodes.len() {
                    if let PNode::Array(name, _) = &code.nodes[t] {
                        let i = match Self::array_index_ref(name, &v) {
                            Ok(i) => i,
                            Err(e) => {
                                proof { if hyp { assert(r_num(v, x.val)); assert(with_depth(x.st, self.eval_depth as u64) == x.st); } }
                                return (Step::Ret(Err(e)), Ghost(g1));
                            },
                        };
                        let ghost sp = elem_place(text_view(*name), x);
                        let place = Place::Element(name.clone(), i);
                        proof { if hyp { assert(r_num(v, x.val)); lemma_array_index_value(x.val); } }
                        let w = self.update_at_ref(inc, prefix, place, Ghost(sp), Ghost(x.st));
                        return (Step::Ret(Ok(w)), Ghost(g1));
                    }
                }
                (Step::Ret(Ok(v)), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_unary(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, which: u8, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::Unary(which), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::Unary(which), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let r = self.finish_unary(which, v, Ghost(x));
                (Step::Ret(r), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_binl(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: BinOp, right: usize, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::BinL(op, right), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::BinL(op, right), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost kr = K::BinR(bin_code(op), x.val);
                let ghost g2 = MG { ks: ks1, s: x.st, x: x };
                proof { if hyp { assert(y == bin_r(bin_code(op), x.val, bs_ev(nodes, right, x.st))); } }
                self.push_sub(frames, code, Frame::BinR(op, v), right, Ghost(nodes), Ghost(kr), Ghost(g2), Ghost(goal), Ghost(y), Ghost(d0))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_binr(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: BinOp, a: BCNum, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
            a.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::BinR(op, a), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::BinR(op, a), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost sa = match k { K::BinR(_, a) => a, _ => x.val };
                let r = self.arith_ref(op, &a, &v, Ghost(sa), Ghost(x.val), Ghost(x.st));
                (Step::Ret(r), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_rell(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: RelOp, right: usize, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::RelL(op, right), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::RelL(op, right), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost kr = K::RelR(rel_code(op), x.val);
                let ghost g2 = MG { ks: ks1, s: x.st, x: x };
                self.push_sub(frames, code, Frame::RelR(op, v), right, Ghost(nodes), Ghost(kr), Ghost(g2), Ghost(goal), Ghost(y), Ghost(d0))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_relr(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: RelOp, a: BCNum, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
            a.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::RelR(op, a), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::RelR(op, a), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost sa = match k { K::RelR(_, a) => a, _ => x.val };
                let w = Self::finish_rel(op, &a, &v, Ghost(sa), Ghost(x.val));
                (Step::Ret(Ok(w)), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_store(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, place: Place, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::Store(place), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::Store(place), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost sp = match k { K::Store(p) => p, _ => arbitrary() };
                let w = self.finish_store(place, v, Ghost(sp), Ghost(x));
                (Step::Ret(Ok(w)), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_opstore(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, place: Place, op: BinOp, a: BCNum, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
            a.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::OpStore(place, op, a), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::OpStore(place, op, a), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost (sp, sa) = match k { K::OpStore(p, _, a) => (p, a), _ => arbitrary() };
                let ghost z = bin_r(bin_code(op), sa, x);
                match self.arith_ref(op, &a, &v, Ghost(sa), Ghost(x.val), Ghost(x.st)) {
                    Ok(u) => {
                        let w = self.finish_store(place, u, Ghost(sp), Ghost(z));
                        (Step::Ret(Ok(w)), Ghost(g1))
                    },
                    Err(e) => (Step::Ret(Err(e)), Ghost(g1)),
                }
    }

    /// With the value of a sub-computation of the frame `fr`.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn ret_ok(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, fr: Frame, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            v.scale <= BC_SCALE_MAX,
            frame_ok(fr),
            takes_value(fr),
            gives_value(fr) == wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            !(fr is Depth) && m_after(*old(self), old(frames)@, *code, nodes, fr, v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        match fr {
            Frame::Depth(_) => (Step::Ret(Ok(v)), Ghost(MG { ks: ks1, s: x.st, x: x })),
            Frame::ArrayIdx(t) => self.ret_arrayidx(frames, code, t, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::AssignIdx(t, op, value) => self.ret_assignidx(frames, code, t, op, value, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::UpdateIdx(t, inc, prefix) => self.ret_updateidx(frames, code, t, inc, prefix, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::Unary(which) => self.ret_unary(frames, code, which, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::BinL(op, right) => self.ret_binl(frames, code, op, right, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::BinR(op, a) => self.ret_binr(frames, code, op, a, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::RelL(op, right) => self.ret_rell(frames, code, op, right, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::RelR(op, a) => self.ret_relr(frames, code, op, a, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::Store(place) => self.ret_store(frames, code, place, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::OpStore(place, op, a) => self.ret_opstore(frames, code, place, op, a, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::ExprStmt(e) => self.ret_exprstmt(frames, code, e, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::Return => self.ret_return(frames, code, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::IfCond(b) => self.ret_ifcond(frames, code, b, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::ForInit(c, p, b) => self.loop_start(frames, code, c, Some(p), b, Ghost(nodes), Ghost(MG { ks: ks1, s: x.st, x: x }), Ghost(goal), Ghost(d0)),
            Frame::LoopCond(c, p, b) => self.ret_loopcond(frames, code, c, p, b, v, Ghost(nodes), Ghost(k), Ghost(ks1), Ghost(x), Ghost(goal), Ghost(d0)),
            Frame::LoopPost(c, p, b) => self.loop_start(frames, code, c, p, b, Ghost(nodes), Ghost(MG { ks: ks1, s: x.st, x: x }), Ghost(goal), Ghost(d0)),
            _ => (Step::Ret(Ok(v)), Ghost(MG { ks: ks1, s: x.st, x: x })),
        }
    }

    /// With the result of a statement, for a frame that takes one.
    #[verifier::exec_allows_no_decreases_clause]
    fn ret_stmt(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, fr: Frame, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !takes_value(fr),
            gives_value(fr) == wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            !(fr is DepthS) && m_after_s(*old(self), old(frames)@, *code, nodes, fr, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after_s(*self, frames@, *code, nodes, fr, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); } }
        match fr {
            Frame::List(n, i) => {
                if self.break_flag || self.return_flag {
                    return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { ks: ks1, s: x.st, x: y }));
                }
                self.list_next(frames, code, n, i, Ghost(nodes), Ghost(MG { ks: ks1, s: x.st, x: y }), Ghost(goal), Ghost(d0))
            },
            Frame::LoopBody(c, p, b) => {
                let (should_break, next_break) = verified_loop_post_body_action(self.break_flag, self.return_flag, self.quit_flag);
                self.break_flag = next_break;
                let ghost st2 = bc_spec::eval::with_flags(x.st, false, x.st.ret, x.st.ret_val);
                if should_break {
                    return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { ks: ks1, s: st2, x: y }));
                }
                match p {
                    Some(post) => {
                        let ghost kp = K::LoopPost(nodes, c, post, true, b);
                        self.push_sub(frames, code, Frame::LoopPost(c, p, b), post, Ghost(nodes), Ghost(kp), Ghost(MG { ks: ks1, s: st2, x: y }), Ghost(goal), Ghost(y), Ghost(d0))
                    },
                    None => self.loop_start(frames, code, c, None, b, Ghost(nodes), Ghost(MG { ks: ks1, s: st2, x: y }), Ghost(goal), Ghost(d0)),
                }
            },
            _ => (Step::Ret(Ok(BCNum::zero())), Ghost(MG { ks: ks1, s: x.st, x: y })),
        }
    }

    /// Enters the execution of node `n`: its nesting level, then the statement.
    #[verifier::exec_allows_no_decreases_clause]
    fn step_exec(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_exec(*old(self), old(frames)@, *code, nodes, n, g, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_exec(*self, frames@, *code, nodes, n, g, goal);
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_depth) {
            let ghost x = bs_exec(nodes, n, g.s);
            let r = Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
            proof {
                if hyp {
                    lemma_exec_too_deep(nodes, n, g.s);
                    assert(with_depth(g.s, self.eval_depth as u64) == g.s);
                }
            }
            return (Step::Ret(r), Ghost(MG { ks: g.ks, s: g.s, x }));
        }
        let ghost before = *self;
        let ghost f0 = frames@;
        let ghost s1 = with_depth(g.s, (g.s.depth + 1) as u64);
        let ghost k = K::Depth(g.s.depth);
        proof {
            if hyp {
                lemma_den_done(g.ks, bs_exec(nodes, n, g.s));
                lemma_step_exec(nodes, n, g.s);
                lemma_den_push(g.ks, k, bs_exec_node(nodes, n, s1));
            }
        }
        frames.push(Frame::DepthS(self.eval_depth));
        self.eval_depth += 1;
        proof {
            assert(frames@.drop_last() =~= f0);
            assert(frames_ok(frames@, self.eval_depth, d0));
            assert(!wants(frames@, d0));
            if hyp {
                lemma_r_state_depth(before, *self, g.s);
                lemma_push(f0, g.ks, Frame::DepthS(before.eval_depth), k, *code, nodes);
                lemma_den_done(g.ks.push(k), bs_exec_node(nodes, n, s1));
            }
        }
        self.step_stmt(frames, code, n, Ghost(nodes), Ghost(MG { ks: g.ks.push(k), s: s1, x: g.x }), Ghost(goal), Ghost(d0))
    }

    /// A form whose first sub-computation is the statement `child`.
    #[verifier::exec_allows_no_decreases_clause]
    fn push_sub_s(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, f: Frame, child: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(parent): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            frame_ok(f),
            !(f is Depth) && !(f is DepthS),
            gives_value(f) == wants(old(frames)@, d0),
            !takes_value(f),
        ensures
            *final(self) == *old(self),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            (r_rc(*code, nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, nodes)
                && r_mframe(f, k, *code, nodes) && done(goal) && den(g.ks, parent) == goal
                && (done(parent) ==> parent == apply(k, bs_exec(nodes, child, g.s))))
                ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost f0 = frames@;
        let ghost fv = f;
        frames.push(f);
        proof {
            assert(frames@ == f0.push(fv));
            lemma_frames_push(f0, fv, self.eval_depth, d0);
            if r_rc(*code, nodes) && r_state(*self, g.s) && r_mframes(f0, g.ks, *code, nodes)
                && r_mframe(fv, k, *code, nodes) && done(goal) && den(g.ks, parent) == goal
                && (done(parent) ==> parent == apply(k, bs_exec(nodes, child, g.s))) {
                lemma_den_done(g.ks, parent);
                lemma_den_push(g.ks, k, bs_exec(nodes, child, g.s));
                lemma_push(f0, g.ks, fv, k, *code, nodes);
            }
        }
        (Step::Exec(child), Ghost(MG { ks: g.ks.push(k), s: g.s, x: g.x }))
    }

    /// The statement at node `n` (the specification's `exec_node`).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(30)]
    fn step_stmt(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_snode(*old(self), old(frames)@, *code, nodes, n, g, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_snode(*self, frames@, *code, nodes, n, g, goal);
        let ghost parent = bs_exec_node(nodes, n, g.s);
        proof {
            if hyp {
                lemma_den_done(g.ks, parent);
                if n < nodes.len() {
                    assert(r_node(code.nodes@[n as int], nodes[n as int]));
                }
            }
        }
        if !verified_should_abort_execution(self.break_flag, self.return_flag, self.quit_flag) && n < code.nodes.len() {
            match &code.nodes[n] {
                PNode::Block(list) => {
                    proof { if hyp { lemma_step_block(nodes, n, list@, g.s); assert(list@.skip(0) =~= list@); } }
                    return self.list_next(frames, code, n, 0, Ghost(nodes), Ghost(g), Ghost(goal), Ghost(d0));
                },
                PNode::ExprStmt(e) => {
                    proof { if hyp { lemma_step_expr_stmt(nodes, n, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::ExprStmt(*e), *e, Ghost(nodes), Ghost(K::ExprStmt(nodes, *e)), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::Return(Some(e)) => {
                    proof { if hyp { lemma_step_return(nodes, n, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::Return, *e, Ghost(nodes), Ghost(K::Return), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::If(c, b) => {
                    proof { if hyp { lemma_step_if(nodes, n, *c, *b, g.s); } }
                    return self.push_sub(frames, code, Frame::IfCond(*b), *c, Ghost(nodes), Ghost(K::IfCond(nodes, *b)), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                PNode::While(c, b) => {
                    proof { if hyp { lemma_step_while(nodes, n, *c, *b, g.s); } }
                    return self.loop_start(frames, code, *c, None, *b, Ghost(nodes), Ghost(g), Ghost(goal), Ghost(d0));
                },
                PNode::For(i, c, p, b) => {
                    proof { if hyp { lemma_step_for(nodes, n, *i, *c, *p, *b, g.s); } }
                    return self.push_sub(frames, code, Frame::ForInit(*c, *p, *b), *i, Ghost(nodes), Ghost(K::ForInit(nodes, *c, *p, *b)), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
                _ => {},
            }
        }
        let r = self.leaf_stmt(code, n, Ghost(nodes), Ghost(g.s));
        (Step::Ret(r), Ghost(MG { ks: g.ks, s: g.s, x: parent }))
    }

    /// The result of a statement that needs no sub-computation on the machine.
    #[verifier::exec_allows_no_decreases_clause]
    fn leaf_stmt(&mut self, code: &Rc<Code>, n: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            (old(self).break_flag || old(self).return_flag || old(self).quit_flag) || leaf_stmt_node(*code, n),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale == 0,
            (r_state(*old(self), st) && r_rc(*code, nodes) && done(bs_exec_node(nodes, n, st))) ==> r_ret(r, *final(self), bs_exec_node(nodes, n, st), false),
    {
        let r = self.exec_node_ref(code, n, Ghost(nodes), Ghost(st));
        proof {
            if done(bs_exec_node(nodes, n, st)) {
                let f = choose|f: u64| done(#[trigger] exec_node(nodes, n, st, f));
                assert(done(exec_node(nodes, n, st, f)));
            }
        }
        match r {
            Ok(()) => Ok(BCNum::zero()),
            Err(e) => Err(e),
        }
    }

    /// The statements of the block at node `n` from statement `i` on (the specification's
    /// `exec_list`).
    #[verifier::exec_allows_no_decreases_clause]
    fn list_next(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, i: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            (r_rc(*code, nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, nodes) && done(goal)
                && n < code.nodes@.len() && (code.nodes@[n as int] matches PNode::Block(list) && i <= list@.len()
                && den(g.ks, bs_list(nodes, list@.skip(i as int), g.s)) == goal))
                ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, g.s) && r_mframes(frames@, g.ks, *code, nodes) && done(goal)
                && n < code.nodes@.len() && (code.nodes@[n as int] matches PNode::Block(list) && i <= list@.len()
                && den(g.ks, bs_list(nodes, list@.skip(i as int), g.s)) == goal);
        if n < code.nodes.len() {
            if let PNode::Block(list) = &code.nodes[n] {
                let ghost rest = list@.skip(i as int);
                let ghost parent = bs_list(nodes, rest, g.s);
                if i >= list.len() {
                    proof { if hyp { lemma_list_end(nodes, rest, g.s); } }
                    return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { ks: g.ks, s: g.s, x: parent }));
                }
                let ghost k = K::List(nodes, list@.skip(i as int + 1));
                proof {
                    if hyp {
                        lemma_den_done(g.ks, parent);
                        lemma_step_list(nodes, rest, g.s);
                        assert(rest.drop_first() =~= list@.skip(i as int + 1));
                        assert(rest[0] == list@[i as int]);
                    }
                }
                return self.push_sub_s(frames, code, Frame::List(n, i + 1), list[i], Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
            }
        }
        (Step::Ret(Ok(BCNum::zero())), Ghost(g))
    }

    /// One turn of a loop: the condition (the specification's `exec_loop`).
    #[verifier::exec_allows_no_decreases_clause]
    fn loop_start(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, c: usize, p: Option<usize>, b: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            (r_rc(*code, nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, nodes) && done(goal)
                && den(g.ks, bs_loop(nodes, c, opt_index(p), p is Some, b, g.s)) == goal)
                ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, g.s) && r_mframes(frames@, g.ks, *code, nodes) && done(goal)
                && den(g.ks, bs_loop(nodes, c, opt_index(p), p is Some, b, g.s)) == goal;
        let ghost parent = bs_loop(nodes, c, opt_index(p), p is Some, b, g.s);
        let ghost k = K::LoopCond(nodes, c, opt_index(p), p is Some, b);
        proof { if hyp { lemma_den_done(g.ks, parent); lemma_step_loop(nodes, c, opt_index(p), p is Some, b, g.s); } }
        self.push_sub(frames, code, Frame::LoopCond(c, p, b), c, Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0))
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn ret_exprstmt(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, e: usize, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::ExprStmt(e), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::ExprStmt(e), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); } }
        let assignment = Self::is_assignment_ref(code, e, Ghost(nodes));
        if !assignment {
            let mut text = v.format_bytes(self.obase);
            text.push(10);
            self.stdout_writer.write_bytes(&text);
            self.stdout_writer.flush_out();
        }
        proof {
            if hyp && !assignment {
                axiom_bigint_size(&v.coeff);
                lemma_mag_bounds(x.val.mag);
                lemma_format_num(x.val, x.st.obase);
            }
        }
        (Step::Ret(Ok(BCNum::zero())), Ghost(MG { ks: ks1, s: x.st, x: y }))
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn ret_return(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::Return, v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::Return, v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); } }
        self.return_value = v;
        self.return_flag = true;
        (Step::Ret(Ok(BCNum::zero())), Ghost(MG { ks: ks1, s: x.st, x: y }))
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn ret_ifcond(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, b: usize, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::IfCond(b), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::IfCond(b), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); lemma_is_zero_mag(x.val.mag); } }
        if v.is_zero() {
            return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { ks: ks1, s: x.st, x: y }));
        }
        (Step::Exec(b), Ghost(MG { ks: ks1, s: x.st, x: y }))
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn ret_loopcond(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, c: usize, p: Option<usize>, b: usize, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::LoopCond(c, p, b), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::LoopCond(c, p, b), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); lemma_is_zero_mag(x.val.mag); } }
        if v.is_zero() {
            return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { ks: ks1, s: x.st, x: y }));
        }
        let ghost kb = K::LoopBody(nodes, c, opt_index(p), p is Some, b);
        self.push_sub_s(frames, code, Frame::LoopBody(c, p, b), b, Ghost(nodes), Ghost(kb), Ghost(MG { ks: ks1, s: x.st, x: x }), Ghost(goal), Ghost(y), Ghost(d0))
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
            m_step(*old(self), Seq::empty(), *code, nodes, start, MG { ks: Seq::empty(), s: st, x: goal }, goal, MRoot { d: old(self).eval_depth, e })
                ==> r_ret(r, *final(self), goal, e),
    {
        let ghost d0 = MRoot { d: self.eval_depth, e };
        let ghost hyp = m_step(*self, Seq::empty(), *code, nodes, start, MG { ks: Seq::empty(), s: st, x: goal }, goal, d0);
        let mut frames: Vec<Frame> = Vec::new();
        let mut step = start;
        let ghost mut g = MG { ks: Seq::empty(), s: st, x: goal };
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
                hyp == m_step(*old(self), Seq::empty(), *code, nodes, start, MG { ks: Seq::empty(), s: st, x: goal }, goal, d0),
                hyp ==> m_step(*self, frames@, *code, nodes, step, g, goal, d0),
        {
            match step {
                Step::Eval(j) => {
                    let (next, Ghost(g2)) = self.step_eval(&mut frames, code, j, Ghost(nodes), Ghost(g), Ghost(goal), Ghost(d0));
                    step = next;
                    proof { g = g2; }
                },
                Step::Exec(j) => {
                    let (next, Ghost(g2)) = self.step_exec(&mut frames, code, j, Ghost(nodes), Ghost(g), Ghost(goal), Ghost(d0));
                    step = next;
                    proof { g = g2; }
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
                    let (next, Ghost(g2)) = self.step_ret(&mut frames, code, res, Ghost(nodes), Ghost(g), Ghost(goal), Ghost(d0));
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
        let r = self.run(code, Step::Exec(n), Ghost(nodes), Ghost(st), Ghost(goal), Ghost(false));
        let r = match r {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
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
