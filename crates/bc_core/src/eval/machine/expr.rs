// SPDX-License-Identifier: MIT

//! The machine's expression frames: entering the evaluation of a node (`step_eval`,
//! `step_node`), pushing the frame of a sub-expression (`push_sub`), assignments and `++`/`--`,
//! and what each expression frame does with the value of its sub-expression (`ret_arrayidx`
//! to `ret_opstore`).

use super::*;

verus! {

impl Evaluator {
    /// The result of a form that needs no sub-computation on the machine.
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn leaf_result(&mut self, code: &Rc<Code>, n: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            leaf_node(*code, n),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_rc(*code, nodes) && done(bs_ev_node(nodes, n, st))) ==> r_result(r, *final(self), bs_ev_node(nodes, n, st), old(self).eval_depth),
    {
        let r = self.eval_leaf_ref(code, n, Ghost(nodes), Ghost(st));
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
    pub(super) fn step_eval(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_eval(*old(self), old(frames)@, *code, cx.nodes, n, g, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal; let ghost d0 = cx.d0;
        let ghost hyp = m_eval(*self, frames@, *code, nodes, n, g, goal);
        if Self::quick_ok(code, n, QUICK_BUDGET) {
            let ghost x = bs_ev(nodes, n, g.s);
            proof { if hyp { lemma_den_done(g.ks, x); } }
            let r = self.quick_eval(code, n, QUICK_BUDGET, Ghost(nodes), Ghost(g.s));
            return (Step::Ret(r), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x }));
        }
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_eval_depth) {
            let ghost x = bs_ev(nodes, n, g.s);
            let r = Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
            proof {
                if hyp {
                    lemma_ev_too_deep(nodes, n, g.s);
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
        self.step_node(frames, code, n, Ghost(MG { nodes: nodes, ks: g.ks.push(k), s: s1, x: g.x }), Ghost(cx))
    }

    /// A form whose first sub-computation is node `child`.
    /// Evaluates `child` for the frame `f`: by the fast path when it can, else on a new frame.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    pub(super) fn push_sub(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, f: Frame, child: usize, Ghost(k): Ghost<MK>, Ghost(g): Ghost<MG>, Ghost(parent): Ghost<MResult>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            mframe_ok(f),
            !(f is Depth) && !(f is DepthS),
            gives_value(f) == wants(old(frames)@, cx.d0),
            takes_value(f),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            (r_rc(*code, cx.nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, cx.nodes)
                && r_mframe(f, k, *code, cx.nodes) && done(cx.goal) && den(g.ks, parent) == cx.goal
                && (done(parent) ==> parent == apply(k, bs_ev(cx.nodes, child, g.s))))
                ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, g.s) && r_mframes(frames@, g.ks, *code, nodes)
            && r_mframe(f, k, *code, nodes) && done(goal) && den(g.ks, parent) == goal
            && (done(parent) ==> parent == apply(k, bs_ev(nodes, child, g.s)));
        // An argument is not taken here: its frame leads to the next argument, so the recursion
        // through `ret_ok` would be as deep as the call has arguments.
        if !matches!(f, Frame::ArgVal(..)) && Self::quick_ok(code, child, QUICK_BUDGET) {
            let ghost x = bs_ev(nodes, child, g.s);
            proof {
                if hyp {
                    lemma_den_done(g.ks, parent);
                    if !done(x) { lemma_apply_not_done(k, x); }
                }
            }
            return match self.quick_eval(code, child, QUICK_BUDGET, Ghost(nodes), Ghost(g.s)) {
                Ok(v) => self.ret_ok(frames, code, f, v, Ghost(MPop { k: k, ks: g.ks, x: x }), Ghost(cx)),
                Err(e) => (Step::Ret(Err(e)), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent })),
            };
        }
        self.push_frame(frames, code, f, child, Ghost(k), Ghost(g), Ghost(parent), Ghost(cx))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn push_frame(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, f: Frame, child: usize, Ghost(k): Ghost<MK>, Ghost(g): Ghost<MG>, Ghost(parent): Ghost<MResult>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            mframe_ok(f),
            !(f is Depth) && !(f is DepthS),
            gives_value(f) == wants(old(frames)@, cx.d0),
            takes_value(f),
        ensures
            *final(self) == *old(self),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            (r_rc(*code, cx.nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, cx.nodes)
                && r_mframe(f, k, *code, cx.nodes) && done(cx.goal) && den(g.ks, parent) == cx.goal
                && (done(parent) ==> parent == apply(k, bs_ev(cx.nodes, child, g.s))))
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
                && (done(parent) ==> parent == apply(k, bs_ev(nodes, child, g.s))) {
                lemma_den_done(g.ks, parent);
                lemma_den_push(g.ks, k, bs_ev(nodes, child, g.s));
                lemma_push(f0, g.ks, fv, k, *code, nodes);
            }
        }
        (Step::Eval(child), Ghost(MG { nodes: nodes, ks: g.ks.push(k), s: g.s, x: g.x }))
    }

    /// One step of a form (the specification's `ev_node`).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(30)]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn step_node(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_node(*old(self), old(frames)@, *code, cx.nodes, n, g, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal;
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
                    return self.push_sub(frames, code, Frame::Unary(0), *e, Ghost(K::Unary(0u8)), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::Length(e) => {
                    proof { if hyp { lemma_step_unary(nodes, n, 1u8, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::Unary(1), *e, Ghost(K::Unary(1u8)), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::Sqrt(e) => {
                    proof { if hyp { lemma_step_unary(nodes, n, 2u8, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::Unary(2), *e, Ghost(K::Unary(2u8)), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::ScaleOf(e) => {
                    proof { if hyp { lemma_step_unary(nodes, n, 3u8, *e, g.s); } }
                    return self.push_sub(frames, code, Frame::Unary(3), *e, Ghost(K::Unary(3u8)), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::Paren(e) => {
                    proof { if hyp { lemma_step_paren(nodes, n, *e, g.s); } }
                    return (Step::Eval(*e), Ghost(g));
                },
                PNode::Binary(op, l, r) => {
                    let ghost k = K::BinL(nodes, bin_code(*op), *r);
                    proof { if hyp { lemma_step_binary(nodes, n, bin_code(*op), *l, *r, g.s); } }
                    return self.push_sub(frames, code, Frame::BinL(*op, *r), *l, Ghost(k), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::Rel(op, l, r) => {
                    let ghost k = K::RelL(nodes, rel_code(*op), *r);
                    proof { if hyp { lemma_step_rel(nodes, n, rel_code(*op), *l, *r, g.s); } }
                    return self.push_sub(frames, code, Frame::RelL(*op, *r), *l, Ghost(k), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::Array(name, i) => {
                    let ghost k = K::ArrayIdx(text_view(*name));
                    proof { if hyp { lemma_step_array(nodes, n, text_view(*name), *i, g.s); } }
                    return self.push_sub(frames, code, Frame::ArrayIdx(n), *i, Ghost(k), Ghost(g), Ghost(parent), Ghost(cx));
                },
                PNode::Assign(op, t, v) => {
                    return self.step_assign(frames, code, n, *op, *t, *v, Ghost(g), Ghost(cx));
                },
                PNode::Call(name, args) => {
                    return self.step_call(frames, code, n, name, args, Ghost(g), Ghost(cx));
                },
                PNode::Update(inc, prefix, t) => {
                    return self.step_update(frames, code, n, *inc, *prefix, *t, Ghost(g), Ghost(cx));
                },
                _ => {},
            }
        }
        let r = self.leaf_result(code, n, Ghost(nodes), Ghost(g.s));
        proof { if hyp { assert(r_mframes(frames@, g.ks, *code, nodes)); } }
        (Step::Ret(r), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }))
    }

    /// An assignment: its target, then its value.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::collapsible_if, reason = "Verus does not support `let` chains")]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn step_assign(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, op: AssignOp, t: usize, v: usize, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Assign(op, t, v),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_node(*old(self), old(frames)@, *code, cx.nodes, n, g, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal;
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
                return self.push_sub(frames, code, Frame::AssignIdx(t, op, v), *i, Ghost(k), Ghost(g), Ghost(parent), Ghost(cx));
            }
        }
        let place = self.plain_place_ref(code, t, Ghost(nodes));
        let ghost sp = plain_place(nodes, t);
        proof { if hyp { lemma_step_assign_plain(nodes, n, assign_code(op), t, v, g.s); } }
        self.assign_to_ref(frames, code, op, v, place, Ghost(sp), Ghost(g), Ghost(cx))
    }

    /// The place of a target that is not a subscript.
    pub(super) fn plain_place_ref(&self, code: &Rc<Code>, t: usize, Ghost(nodes): Ghost<SpecNodes>) -> (p: Place)
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
    pub(super) fn single_digit_ref(code: &Rc<Code>, place: &Place, op: AssignOp, v: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(sp): Ghost<SpecPlace>) -> (hex: Option<usize>)
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
    fn assign_to_ref(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: AssignOp, v: usize, place: Place, Ghost(sp): Ghost<SpecPlace>, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            (r_rc(*code, cx.nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, cx.nodes) && r_place(place, sp) && done(cx.goal)
                && den(g.ks, assign_to(cx.nodes, assign_code(op), v, sp, g.s)) == cx.goal)
                ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal;
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
            return (Step::Ret(Ok(res)), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }));
        }
        match op {
            AssignOp::Assign => {
                proof { if hyp { assert(acode == 0); } }
                self.push_sub(frames, code, Frame::Store(place), v, Ghost(K::Store(sp)), Ghost(g), Ghost(parent), Ghost(cx))
            },
            AssignOp::Compound(bin) => {
                let old_v = self.load_ref(&place, Ghost(sp), Ghost(g.s));
                let ghost k = K::OpStore(sp, bin_code(bin), bc_spec::eval::load(g.s, sp));
                proof { if hyp { assert(acode != 0); assert((acode - 1) as u8 == bin_code(bin)); } }
                self.push_sub(frames, code, Frame::OpStore(place, bin, old_v), v, Ghost(k), Ghost(g), Ghost(parent), Ghost(cx))
            },
        }
    }

    /// `++`/`--`.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::collapsible_if, reason = "Verus does not support `let` chains")]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn step_update(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, inc: bool, prefix: bool, t: usize, Ghost(g): Ghost<MG>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Update(inc, prefix, t),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_node(*old(self), old(frames)@, *code, cx.nodes, n, g, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost nodes = cx.nodes; let ghost goal = cx.goal;
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
                return self.push_sub(frames, code, Frame::UpdateIdx(t, inc, prefix), *i, Ghost(k), Ghost(g), Ghost(parent), Ghost(cx));
            }
        }
        let place = self.plain_place_ref(code, t, Ghost(nodes));
        let ghost sp = plain_place(nodes, t);
        proof { if hyp { lemma_step_update_plain(nodes, n, inc, prefix, t, g.s); } }
        let v = self.update_at_ref(inc, prefix, place, Ghost(sp), Ghost(g.s));
        (Step::Ret(Ok(v)), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }))
    }

    /// `++`/`--` once its target is known (the specification's `update_at`).
    pub(super) fn update_at_ref(&mut self, increment: bool, prefix: bool, place: Place, Ghost(sp): Ghost<SpecPlace>, Ghost(st): Ghost<SpecState>) -> (r: BCNum)
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
    pub(super) fn finish_unary(&self, which: u8, v: BCNum, Ghost(x): Ghost<MResult>) -> (r: Result<BCNum, BcError>)
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
    pub(super) fn finish_rel(op: RelOp, l: &BCNum, r: &BCNum, Ghost(a): Ghost<SpecNum>, Ghost(b): Ghost<SpecNum>) -> (v: BCNum)
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
    pub(super) fn finish_store(&mut self, place: Place, val: BCNum, Ghost(sp): Ghost<SpecPlace>, Ghost(x): Ghost<MResult>) -> (r: BCNum)
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

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::collapsible_if, reason = "Verus does not support `let` chains")]
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_arrayidx(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, t: usize, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::ArrayIdx(t), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::ArrayIdx(t), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
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
    #[allow(clippy::collapsible_if, reason = "Verus does not support `let` chains")]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    pub(super) fn ret_assignidx(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, t: usize, op: AssignOp, value: usize, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::AssignIdx(t, op, value), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::AssignIdx(t, op, value), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
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
                        return self.assign_to_ref(frames, code, op, value, place, Ghost(sp), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x }), Ghost(cx));
                    }
                }
                (Step::Ret(Ok(v)), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::collapsible_if, reason = "Verus does not support `let` chains")]
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_updateidx(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, t: usize, inc: bool, prefix: bool, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::UpdateIdx(t, inc, prefix), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::UpdateIdx(t, inc, prefix), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
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
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_unary(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, which: u8, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::Unary(which), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::Unary(which), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let r = self.finish_unary(which, v, Ghost(x));
                (Step::Ret(r), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    pub(super) fn ret_binl(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: BinOp, right: usize, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::BinL(op, right), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::BinL(op, right), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost kr = K::BinR(bin_code(op), x.val);
                let ghost g2 = MG { nodes: nodes, ks: ks1, s: x.st, x: x };
                proof { if hyp { assert(y == bin_r(bin_code(op), x.val, bs_ev(nodes, right, x.st))); } }
                self.push_sub(frames, code, Frame::BinR(op, v), right, Ghost(kr), Ghost(g2), Ghost(y), Ghost(cx))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_binr(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: BinOp, a: BCNum, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
            a.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::BinR(op, a), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::BinR(op, a), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost sa = match k { K::BinR(_, a) => a, _ => x.val };
                let r = self.arith_ref(op, &a, &v, Ghost(sa), Ghost(x.val), Ghost(x.st));
                (Step::Ret(r), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    pub(super) fn ret_rell(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: RelOp, right: usize, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::RelL(op, right), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::RelL(op, right), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost kr = K::RelR(rel_code(op), x.val);
                let ghost g2 = MG { nodes: nodes, ks: ks1, s: x.st, x: x };
                self.push_sub(frames, code, Frame::RelR(op, v), right, Ghost(kr), Ghost(g2), Ghost(y), Ghost(cx))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_relr(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, op: RelOp, a: BCNum, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
            a.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::RelR(op, a), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::RelR(op, a), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost sa = match k { K::RelR(_, a) => a, _ => x.val };
                let w = Self::finish_rel(op, &a, &v, Ghost(sa), Ghost(x.val));
                (Step::Ret(Ok(w)), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_store(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, place: Place, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::Store(place), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::Store(place), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
        proof { if hyp { lemma_den_done(ks1, y); } }
                let ghost sp = match k { K::Store(p) => p, _ => arbitrary() };
                let w = self.finish_store(place, v, Ghost(sp), Ghost(x));
                (Step::Ret(Ok(w)), Ghost(g1))
    }

    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "every frame handler takes the machine's stack in the same form")]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    pub(super) fn ret_opstore(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, place: Place, op: BinOp, a: BCNum, v: BCNum, Ghost(pop): Ghost<MPop>, Ghost(cx): Ghost<MCx>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, cx.d0),
            wants(old(frames)@, cx.d0),
            v.scale <= BC_SCALE_MAX,
            a.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, cx.d0),
            step_ok(r.0, final(frames)@, cx.d0),
            m_after(*old(self), old(frames)@, *code, cx.nodes, Frame::OpStore(place, op, a), v, pop.k, pop.ks, pop.x, cx.goal) ==> m_step(*final(self), final(frames)@, *code, cx.nodes, r.0, r.1@, cx.goal, cx.d0),
    {
        let ghost k = pop.k; let ghost ks1 = pop.ks; let ghost x = pop.x; let ghost nodes = cx.nodes; let ghost goal = cx.goal;
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::OpStore(place, op, a), v, k, ks1, x, goal);
        let ghost y = apply(k, x);
        let ghost g1 = MG { nodes: nodes, ks: ks1, s: x.st, x: y };
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
}

} // verus!
