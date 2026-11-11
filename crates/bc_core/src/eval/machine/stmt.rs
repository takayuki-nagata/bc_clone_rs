// SPDX-License-Identifier: MIT

//! The machine's statement frames: entering the execution of a node (`step_exec`,
//! `step_stmt`), blocks, `if`, `while` and `for`, and what each statement frame does with the
//! result of its sub-computation (`ret_exprstmt` to `ret_loopcond`).

use super::*;

verus! {

impl Evaluator {
    /// Enters the execution of node `n`: its nesting level, then the statement.
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn step_exec(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            !wants(old(frames)@, cx.d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_exec(*old(self), old(frames)@, *code, cx.nodes, n, g, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal; let ghost d0 = cx.d0;
        let ghost hyp = m_exec(*self, frames@, *code, nodes, n, g, goal);
        if Self::quick_stmt_ok(code, n, QUICK_BUDGET) {
            let ghost x = bs_exec(nodes, n, g.s);
            proof { if hyp { lemma_den_done(g.ks, x); } }
            let r = match self.quick_exec(code, n, QUICK_BUDGET, Ghost(nodes), Ghost(g.s)) {
                Ok(()) => Ok(BCNum::zero()),
                Err(e) => Err(e),
            };
            return (Step::Ret(r), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x }));
        }
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_eval_depth) {
            let ghost x = bs_exec(nodes, n, g.s);
            let r = Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
            proof {
                if hyp {
                    lemma_exec_too_deep(nodes, n, g.s);
                    assert(with_depth(g.s, self.eval_depth as u64) == g.s);
                }
            }
            return (Step::Ret(r), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x }));
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
        self.step_stmt(frames, code, n, Ghost(MG { nodes: nodes, ks: g.ks.push(k), s: s1, x: g.x }), Ghost(cx))
    }

    /// A form whose first sub-computation is the statement `child`.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn push_sub_s(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, f: Frame, child: usize, Ghost(k): Ghost<MK>, Ghost(g): Ghost<MG>, Ghost(parent): Ghost<MResult>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            mframe_ok(f),
            !(f is Depth) && !(f is DepthS),
            gives_value(f) == wants(old(frames)@, cx.d0),
            !takes_value(f),
        ensures
            *final(self) == *old(self),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            (r_rc(*code, cx.nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, cx.nodes)
                && r_mframe(f, k, *code, cx.nodes) && done(cx.goal) && den(g.ks, parent) == cx.goal
                && (done(parent) ==> parent == apply(k, bs_exec(cx.nodes, child, g.s))))
                ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal; let ghost d0 = cx.d0;
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
        (Step::Exec(child), Ghost(MG { nodes: nodes, ks: g.ks.push(k), s: g.s, x: g.x }))
    }

    /// The statement at node `n` (the specification's `exec_node`).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(30)]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn step_stmt(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            !wants(old(frames)@, cx.d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_snode(*old(self), old(frames)@, *code, cx.nodes, n, g, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal;
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
                    return self.list_next(frames, code, n, 0, Ghost(g), Ghost(cx));
                },
                PNode::ExprStmt(e) => {
                    proof { if hyp { lemma_step_expr_stmt(nodes, n, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::ExprStmt(*e), *e, Ghost(K::ExprStmt(nodes, *e)), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::Return(Some(e)) => {
                    proof { if hyp { lemma_step_return(nodes, n, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::Return, *e, Ghost(K::Return), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::If(c, b) => {
                    proof { if hyp { lemma_step_if(nodes, n, *c, *b, g.s); } }
                    return self.push_sub(frames, code, Frame::IfCond(*b), *c, Ghost(K::IfCond(nodes, *b)), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::While(c, b) => {
                    proof { if hyp { lemma_step_while(nodes, n, *c, *b, g.s); } }
                    return self.loop_start(frames, code, *c, None, *b, Ghost(g), Ghost(cx));
                },
                PNode::For(i, c, p, b) => {
                    proof { if hyp { lemma_step_for(nodes, n, *i, *c, *p, *b, g.s); } }
                    return self.push_sub(frames, code, Frame::ForInit(*c, *p, *b), *i, Ghost(K::ForInit(nodes, *c, *p, *b)), Ghost(g), Ghost(parent), Ghost(cx));
                },
                _ => {},
            }
        }
        let r = self.leaf_stmt(code, n, Ghost(nodes), Ghost(g.s));
        (Step::Ret(r), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }))
    }

    /// The result of a statement that needs no sub-computation on the machine.
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn leaf_stmt(&mut self, code: &Rc<Code>, n: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            (old(self).break_flag || old(self).return_flag || old(self).quit_flag) || leaf_stmt_node(*code, n),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale == 0,
            (r_state(*old(self), st) && r_rc(*code, nodes) && done(bs_exec_node(nodes, n, st))) ==> r_ret(r, *final(self), bs_exec_node(nodes, n, st), false),
    {
        let r = self.exec_leaf_ref(code, n, Ghost(nodes), Ghost(st));
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
    #[allow(clippy::collapsible_if, reason = "Verus does not support `let` chains")]
    pub(super) fn list_next(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, i: usize, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            !wants(old(frames)@, cx.d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            (r_rc(*code, cx.nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, cx.nodes) && done(cx.goal)
                && n < code.nodes@.len() && (code.nodes@[n as int] matches PNode::Block(list) && i <= list@.len()
                && den(g.ks, bs_list(cx.nodes, list@.skip(i as int), g.s)) == cx.goal))
                ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, g.s) && r_mframes(frames@, g.ks, *code, nodes) && done(goal)
                && n < code.nodes@.len() && (code.nodes@[n as int] matches PNode::Block(list) && i <= list@.len()
                && den(g.ks, bs_list(nodes, list@.skip(i as int), g.s)) == goal);
        if n < code.nodes.len() {
            if let PNode::Block(list) = &code.nodes[n] {
                let ghost rest = list@.skip(i as int);
                let ghost parent = bs_list(nodes, rest, g.s);
                if i >= list.len() {
                    proof { if hyp { lemma_list_end(nodes, rest, g.s); } }
                    return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }));
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
                return self.push_sub_s(frames, code, Frame::List(n, i + 1), list[i], Ghost(k), Ghost(g), Ghost(parent), Ghost(cx));
            }
        }
        (Step::Ret(Ok(BCNum::zero())), Ghost(g))
    }

    /// One turn of a loop: the condition (the specification's `exec_loop`).
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    pub(super) fn loop_start(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, c: usize, p: Option<usize>, b: usize, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            !wants(old(frames)@, cx.d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            (r_rc(*code, cx.nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, cx.nodes) && done(cx.goal)
                && den(g.ks, bs_loop(cx.nodes, c, opt_index(p), p is Some, b, g.s)) == cx.goal)
                ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, g.s) && r_mframes(frames@, g.ks, *code, nodes) && done(goal)
                && den(g.ks, bs_loop(nodes, c, opt_index(p), p is Some, b, g.s)) == goal;
        let ghost parent = bs_loop(nodes, c, opt_index(p), p is Some, b, g.s);
        let ghost k = K::LoopCond(nodes, c, opt_index(p), p is Some, b);
        proof { if hyp { lemma_den_done(g.ks, parent); lemma_step_loop(nodes, c, opt_index(p), p is Some, b, g.s); } }
        self.push_sub(frames, code, Frame::LoopCond(c, p, b), c, Ghost(k), Ghost(g), Ghost(parent), Ghost(cx))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_exprstmt(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, e: usize, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            !wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::ExprStmt(e), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::ExprStmt(e), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); } }
        let assignment = Self::is_assignment_ref(code, e, Ghost(nodes));
        if !assignment {
            let mut text = v.format_bytes(self.obase);
            text.push(10);
            proof { bc_spec::output::lemma_write_wrapped_append(out_log(&self.stdout_writer), out_col(&self.stdout_writer), text@); }
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
        (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y }))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_return(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            !wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::Return, v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::Return, v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); } }
        self.return_value = v;
        self.return_flag = true;
        (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y }))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_ifcond(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, b: usize, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            !wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::IfCond(b), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::IfCond(b), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); lemma_is_zero_mag(x.val.mag); } }
        if v.is_zero() {
            return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y }));
        }
        (Step::Exec(b), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y }))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    pub(super) fn ret_loopcond(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, c: usize, p: Option<usize>, b: usize, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            !wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::LoopCond(c, p, b), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::LoopCond(c, p, b), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); lemma_is_zero_mag(x.val.mag); } }
        if v.is_zero() {
            return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y }));
        }
        let ghost kb = K::LoopBody(nodes, c, opt_index(p), p is Some, b);
        self.push_sub_s(frames, code, Frame::LoopBody(c, p, b), b, Ghost(kb), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x }), Ghost(y), Ghost(cx))
    }
}

} // verus!
