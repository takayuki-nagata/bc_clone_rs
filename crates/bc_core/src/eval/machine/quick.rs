// SPDX-License-Identifier: MIT

//! The fast path of the machine: a call-free expression, or a statement made of call-free
//! expressions, at most [`QUICK_BUDGET`] levels deep, runs by native recursion instead of
//! frames. The recursion is bounded by the budget, not by the input, so the native stack
//! stays bounded. Verus checks this: each function decreases `(b, stage)`, where `stage`
//! orders the functions that pass the same budget `b` on (`quick_eval` 2, `quick_node` 1,
//! the operators 0; `quick_exec` 3, `quick_stmt` 2, `quick_for` 1, the rest 0), and only the
//! loop in `quick_loop` is exempt, because a `while` need not end. Whether a statement may
//! take the fast path is checked by looking at no more than [`QUICK_STMTS`] statement nodes,
//! so that a wide block (one skipped by `if (0)` in a loop, say) is not scanned on every
//! pass. Anything else (calls, subscripted targets, deeper trees) goes to the machine. Each function has the theorem of the machine's: its result is the
//! specification's `bs_ev`, `bs_ev_node`, `bs_exec` or `bs_exec_node`.

use super::*;

verus! {

/// The levels below a node that the fast path runs by recursion.
pub(crate) const QUICK_BUDGET: u32 = 8;

/// The statements the fast path looks at before it leaves a statement to the machine.
pub(crate) const QUICK_STMTS: u32 = 64;

/// A target of `=` or `++` that is not a subscript.
pub(crate) open spec fn plain_target(code: Rc<Code>, t: usize) -> bool {
    !(t < code.nodes@.len() && code.nodes@[t as int] is Array)
}

/// The statements of the block at node `n`.
pub(crate) open spec fn block_of(code: Rc<Code>, n: usize) -> Seq<usize> {
    match code.nodes@[n as int] {
        PNode::Block(list) => list@,
        _ => Seq::empty(),
    }
}

/// A call-free expression whose subscripts are leaves, at most `b` levels deep.
pub(crate) open spec fn quick(code: Rc<Code>, n: usize, b: u32) -> bool
    decreases b,
{
    n >= code.nodes@.len() || match code.nodes@[n as int] {
        PNode::Neg(e) => b > 0 && quick(code, e, (b - 1) as u32),
        PNode::Length(e) => b > 0 && quick(code, e, (b - 1) as u32),
        PNode::Sqrt(e) => b > 0 && quick(code, e, (b - 1) as u32),
        PNode::ScaleOf(e) => b > 0 && quick(code, e, (b - 1) as u32),
        PNode::Paren(e) => b > 0 && quick(code, e, (b - 1) as u32),
        PNode::Binary(_, l, r) => b > 0 && quick(code, l, (b - 1) as u32) && quick(code, r, (b - 1) as u32),
        PNode::Rel(_, l, r) => b > 0 && quick(code, l, (b - 1) as u32) && quick(code, r, (b - 1) as u32),
        PNode::Assign(_, t, v) => b > 0 && plain_target(code, t) && quick(code, v, (b - 1) as u32),
        PNode::Update(_, _, t) => plain_target(code, t),
        PNode::Array(_, _) => false,
        PNode::Call(_, _) => false,
        _ => true,
    }
}

/// A statement made of [`quick`] expressions, at most `b` levels deep.
pub(crate) open spec fn quick_s(code: Rc<Code>, n: usize, b: u32) -> bool
    decreases b,
{
    n < code.nodes@.len() && b > 0 && match code.nodes@[n as int] {
        PNode::ExprStmt(e) => quick(code, e, (b - 1) as u32),
        PNode::Return(Some(e)) => quick(code, e, (b - 1) as u32),
        PNode::Return(None) => true,
        PNode::Str(_) => true,
        PNode::Break => true,
        PNode::Block(list) => forall|i: int| #![trigger list@[i]] 0 <= i < list@.len() ==> quick_s(code, list@[i], (b - 1) as u32),
        PNode::If(c, s) => quick(code, c, (b - 1) as u32) && quick_s(code, s, (b - 1) as u32),
        PNode::While(c, s) => quick(code, c, (b - 1) as u32) && quick_s(code, s, (b - 1) as u32),
        PNode::For(i, c, p, s) => quick(code, i, (b - 1) as u32) && quick(code, c, (b - 1) as u32)
            && quick(code, p, (b - 1) as u32) && quick_s(code, s, (b - 1) as u32),
        _ => false,
    }
}

impl Evaluator {
    fn plain_target_ref(code: &Rc<Code>, t: usize) -> (r: bool)
        ensures
            r == plain_target(*code, t),
    {
        !(t < code.nodes.len() && matches!(&code.nodes[t], PNode::Array(..)))
    }

    /// Whether `n` is [`quick`].
    pub(super) fn quick_ok(code: &Rc<Code>, n: usize, b: u32) -> (r: bool)
        ensures
            r == quick(*code, n, b),
        decreases b,
    {
        if n >= code.nodes.len() {
            return true;
        }
        match &code.nodes[n] {
            PNode::Neg(e) | PNode::Length(e) | PNode::Sqrt(e) | PNode::ScaleOf(e) | PNode::Paren(e) => b > 0 && Self::quick_ok(code, *e, b - 1),
            PNode::Binary(_, l, r) | PNode::Rel(_, l, r) => b > 0 && Self::quick_ok(code, *l, b - 1) && Self::quick_ok(code, *r, b - 1),
            PNode::Assign(_, t, v) => b > 0 && Self::plain_target_ref(code, *t) && Self::quick_ok(code, *v, b - 1),
            PNode::Update(_, _, t) => Self::plain_target_ref(code, *t),
            PNode::Array(..) | PNode::Call(..) => false,
            _ => true,
        }
    }

    /// Whether `n` is [`quick_s`]. It looks at no more than [`QUICK_STMTS`] statement nodes
    /// (`n` and the statements in it), and says no to a larger statement, which the machine then runs, so that one step of the
    /// machine checks a bounded number of nodes however wide a block is.
    pub(super) fn quick_stmt_ok(code: &Rc<Code>, n: usize, b: u32) -> (r: bool)
        ensures
            r ==> quick_s(*code, n, b),
    {
        Self::quick_stmt_fit(code, n, b, QUICK_STMTS).is_some()
    }

    /// Whether `n` is [`quick_s`] with at most `k` statement nodes; if so, the rest of `k`.
    fn quick_stmt_fit(code: &Rc<Code>, n: usize, b: u32, k: u32) -> (r: Option<u32>)
        ensures
            r matches Some(k2) ==> quick_s(*code, n, b) && k2 < k,
        decreases b,
    {
        if n >= code.nodes.len() || b == 0 || k == 0 {
            return None;
        }
        let k = k - 1;
        match &code.nodes[n] {
            PNode::ExprStmt(e) => if Self::quick_ok(code, *e, b - 1) { Some(k) } else { None },
            PNode::Return(Some(e)) => if Self::quick_ok(code, *e, b - 1) { Some(k) } else { None },
            PNode::Return(None) | PNode::Str(_) | PNode::Break => Some(k),
            PNode::Block(list) => {
                let mut i = 0;
                let mut left = k;
                while i < list.len()
                    invariant
                        n < code.nodes@.len(),
                        code.nodes@[n as int] == PNode::Block(*list),
                        b > 0,
                        i <= list@.len(),
                        left <= k,
                        forall|j: int| #![trigger list@[j]] 0 <= j < i ==> quick_s(*code, list@[j], (b - 1) as u32),
                    decreases list.len() - i,
                {
                    match Self::quick_stmt_fit(code, list[i], b - 1, left) {
                        Some(rest) => { left = rest; },
                        None => { return None; },
                    }
                    i += 1;
                }
                Some(left)
            },
            PNode::If(c, s) | PNode::While(c, s) => if Self::quick_ok(code, *c, b - 1) { Self::quick_stmt_fit(code, *s, b - 1, k) } else { None },
            PNode::For(i, c, p, s) => {
                if Self::quick_ok(code, *i, b - 1) && Self::quick_ok(code, *c, b - 1) && Self::quick_ok(code, *p, b - 1) {
                    Self::quick_stmt_fit(code, *s, b - 1, k)
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    /// Evaluates node `n` with its nesting level (the specification's `ev`).
    pub(super) fn quick_eval(&mut self, code: &Rc<Code>, n: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            quick(*code, n, b),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_ev(nodes, n, st))) ==> r_result(r, *final(self), bs_ev(nodes, n, st), old(self).eval_depth),
        decreases b, 2u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_ev(nodes, n, st));
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_eval_depth) {
            proof {
                if hyp {
                    lemma_ev_too_deep(nodes, n, st);
                    assert(with_depth(st, self.eval_depth as u64) == st);
                }
            }
            return Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
        }
        let ghost before = *self;
        let ghost s1 = with_depth(st, (st.depth + 1) as u64);
        proof { if hyp { lemma_step_ev(nodes, n, st); } }
        let d = self.eval_depth;
        self.eval_depth = d + 1;
        proof { if hyp { lemma_r_state_depth(before, *self, st); } }
        let r = self.quick_node(code, n, b, Ghost(nodes), Ghost(s1));
        let ghost mid = *self;
        self.eval_depth = d;
        proof {
            if hyp {
                let x = bs_ev_node(nodes, n, s1);
                if !done(x) { lemma_apply_not_done(K::Depth(st.depth), x); }
                if r is Ok {
                    lemma_r_state_depth(mid, *self, x.st);
                } else {
                    lemma_r_state_depth(mid, *self, with_depth(x.st, mid.eval_depth as u64));
                    assert(with_depth(with_depth(x.st, mid.eval_depth as u64), d as u64) == with_depth(x.st, d as u64));
                }
            }
        }
        r
    }

    /// Evaluates the form at node `n` (the specification's `ev_node`).
    fn quick_node(&mut self, code: &Rc<Code>, n: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            quick(*code, n, b),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_ev_node(nodes, n, st))) ==> r_result(r, *final(self), bs_ev_node(nodes, n, st), old(self).eval_depth),
        decreases b, 1u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_ev_node(nodes, n, st));
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        if n < code.nodes.len() {
            match &code.nodes[n] {
                PNode::Neg(e) => { return self.quick_unary(code, n, 0, *e, b, Ghost(nodes), Ghost(st)); },
                PNode::Length(e) => { return self.quick_unary(code, n, 1, *e, b, Ghost(nodes), Ghost(st)); },
                PNode::Sqrt(e) => { return self.quick_unary(code, n, 2, *e, b, Ghost(nodes), Ghost(st)); },
                PNode::ScaleOf(e) => { return self.quick_unary(code, n, 3, *e, b, Ghost(nodes), Ghost(st)); },
                PNode::Paren(e) => {
                    proof { if hyp { lemma_step_paren(nodes, n, *e, st); } }
                    return self.quick_eval(code, *e, b - 1, Ghost(nodes), Ghost(st));
                },
                PNode::Binary(op, l, r) => { return self.quick_binary(code, n, *op, *l, *r, b, Ghost(nodes), Ghost(st)); },
                PNode::Rel(op, l, r) => { return self.quick_rel(code, n, *op, *l, *r, b, Ghost(nodes), Ghost(st)); },
                PNode::Assign(op, t, v) => { return self.quick_assign(code, n, *op, *t, *v, b, Ghost(nodes), Ghost(st)); },
                PNode::Update(inc, prefix, t) => {
                    let place = self.plain_place_ref(code, *t, Ghost(nodes));
                    let ghost sp = plain_place(nodes, *t);
                    proof {
                        if hyp {
                            if *t < nodes.len() { assert(r_node(code.nodes@[*t as int], nodes[*t as int])); }
                            lemma_step_update_plain(nodes, n, *inc, *prefix, *t, st);
                        }
                    }
                    return Ok(self.update_at_ref(*inc, *prefix, place, Ghost(sp), Ghost(st)));
                },
                _ => {},
            }
        }
        self.leaf_result(code, n, Ghost(nodes), Ghost(st))
    }

    /// `-e`, `length(e)`, `sqrt(e)` and `scale(e)`.
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn quick_unary(&mut self, code: &Rc<Code>, n: usize, which: u8, e: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            b > 0,
            quick(*code, e, (b - 1) as u32),
            n < code.nodes@.len(),
            (which == 0 && code.nodes@[n as int] == PNode::Neg(e)) || (which == 1 && code.nodes@[n as int] == PNode::Length(e))
                || (which == 2 && code.nodes@[n as int] == PNode::Sqrt(e)) || (which == 3 && code.nodes@[n as int] == PNode::ScaleOf(e)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_ev_node(nodes, n, st))) ==> r_result(r, *final(self), bs_ev_node(nodes, n, st), old(self).eval_depth),
        decreases b, 0u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_ev_node(nodes, n, st));
        let ghost x = bs_ev(nodes, e, st);
        proof {
            if hyp {
                assert(r_node(code.nodes@[n as int], nodes[n as int]));
                lemma_step_unary(nodes, n, which, e, st);
                if !done(x) { lemma_apply_not_done(K::Unary(which), x); }
            }
        }
        match self.quick_eval(code, e, b - 1, Ghost(nodes), Ghost(st)) {
            Ok(v) => self.finish_unary(which, v, Ghost(x)),
            Err(err) => Err(err),
        }
    }

    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn quick_binary(&mut self, code: &Rc<Code>, n: usize, op: BinOp, l: usize, r: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (res: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            b > 0,
            quick(*code, l, (b - 1) as u32),
            quick(*code, r, (b - 1) as u32),
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Binary(op, l, r),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            res is Ok ==> res->Ok_0.scale <= BC_SCALE_MAX,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_ev_node(nodes, n, st))) ==> r_result(res, *final(self), bs_ev_node(nodes, n, st), old(self).eval_depth),
        decreases b, 0u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_ev_node(nodes, n, st));
        let ghost x = bs_ev(nodes, l, st);
        proof {
            if hyp {
                assert(r_node(code.nodes@[n as int], nodes[n as int]));
                lemma_step_binary(nodes, n, bin_code(op), l, r, st);
                if !done(x) { lemma_apply_not_done(K::BinL(nodes, bin_code(op), r), x); }
            }
        }
        let a = match self.quick_eval(code, l, b - 1, Ghost(nodes), Ghost(st)) {
            Ok(a) => a,
            Err(err) => { return Err(err); },
        };
        let ghost y = bs_ev(nodes, r, x.st);
        proof { if hyp && !done(y) { lemma_apply_not_done(K::BinR(bin_code(op), x.val), y); } }
        let v = match self.quick_eval(code, r, b - 1, Ghost(nodes), Ghost(x.st)) {
            Ok(v) => v,
            Err(err) => { return Err(err); },
        };
        self.arith_ref(op, &a, &v, Ghost(x.val), Ghost(y.val), Ghost(y.st))
    }

    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn quick_rel(&mut self, code: &Rc<Code>, n: usize, op: RelOp, l: usize, r: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (res: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            b > 0,
            quick(*code, l, (b - 1) as u32),
            quick(*code, r, (b - 1) as u32),
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Rel(op, l, r),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            res is Ok ==> res->Ok_0.scale <= BC_SCALE_MAX,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_ev_node(nodes, n, st))) ==> r_result(res, *final(self), bs_ev_node(nodes, n, st), old(self).eval_depth),
        decreases b, 0u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_ev_node(nodes, n, st));
        let ghost x = bs_ev(nodes, l, st);
        proof {
            if hyp {
                assert(r_node(code.nodes@[n as int], nodes[n as int]));
                lemma_step_rel(nodes, n, rel_code(op), l, r, st);
                if !done(x) { lemma_apply_not_done(K::RelL(nodes, rel_code(op), r), x); }
            }
        }
        let a = match self.quick_eval(code, l, b - 1, Ghost(nodes), Ghost(st)) {
            Ok(a) => a,
            Err(err) => { return Err(err); },
        };
        let ghost y = bs_ev(nodes, r, x.st);
        proof { if hyp && !done(y) { lemma_apply_not_done(K::RelR(rel_code(op), x.val), y); } }
        let v = match self.quick_eval(code, r, b - 1, Ghost(nodes), Ghost(x.st)) {
            Ok(v) => v,
            Err(err) => { return Err(err); },
        };
        Ok(Self::finish_rel(op, &a, &v, Ghost(x.val), Ghost(y.val)))
    }

    /// `=` and `op=` to a target that is not a subscript (the specification's `assign_to`).
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn quick_assign(&mut self, code: &Rc<Code>, n: usize, op: AssignOp, t: usize, v: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            b > 0,
            plain_target(*code, t),
            quick(*code, v, (b - 1) as u32),
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Assign(op, t, v),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_ev_node(nodes, n, st))) ==> r_result(r, *final(self), bs_ev_node(nodes, n, st), old(self).eval_depth),
        decreases b, 0u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_ev_node(nodes, n, st));
        let ghost acode = assign_code(op);
        let place = self.plain_place_ref(code, t, Ghost(nodes));
        let ghost sp = plain_place(nodes, t);
        proof {
            if hyp {
                assert(r_node(code.nodes@[n as int], nodes[n as int]));
                if t < nodes.len() { assert(r_node(code.nodes@[t as int], nodes[t as int])); }
                lemma_step_assign_plain(nodes, n, acode, t, v, st);
            }
        }
        let hex = Self::single_digit_ref(code, &place, op, v, Ghost(nodes), Ghost(sp));
        if let Some(h) = hex {
            let val = BCNum::new(big_from_usize(h), 0);
            let ghost sv = num_u64(bc_spec::eval::hex_val(if bc_spec::eval::number_text(nodes, v).len() > 0 { bc_spec::eval::number_text(nodes, v)[0] } else { 0u8 }));
            proof { if hyp { lemma_u64_mag(h as u64); } }
            let res = val.copy();
            let _ = self.store_ref(place, val, Ghost(sp), Ghost(st), Ghost(sv));
            return Ok(res);
        }
        let ghost x = bs_ev(nodes, v, st);
        match op {
            AssignOp::Assign => {
                proof { if hyp { assert(acode == 0); if !done(x) { lemma_apply_not_done(K::Store(sp), x); } } }
                match self.quick_eval(code, v, b - 1, Ghost(nodes), Ghost(st)) {
                    Ok(w) => Ok(self.finish_store(place, w, Ghost(sp), Ghost(x))),
                    Err(err) => Err(err),
                }
            },
            AssignOp::Compound(bin) => {
                let old_v = self.load_ref(&place, Ghost(sp), Ghost(st));
                let ghost sa = bc_spec::eval::load(st, sp);
                proof {
                    if hyp {
                        assert(acode != 0);
                        assert((acode - 1) as u8 == bin_code(bin));
                        if !done(x) { lemma_apply_not_done(K::OpStore(sp, bin_code(bin), sa), x); }
                    }
                }
                let w = match self.quick_eval(code, v, b - 1, Ghost(nodes), Ghost(st)) {
                    Ok(w) => w,
                    Err(err) => { return Err(err); },
                };
                let ghost z = bin_r(bin_code(bin), sa, x);
                match self.arith_ref(bin, &old_v, &w, Ghost(sa), Ghost(x.val), Ghost(x.st)) {
                    Ok(u) => Ok(self.finish_store(place, u, Ghost(sp), Ghost(z))),
                    Err(err) => Err(err),
                }
            },
        }
    }

    /// Executes node `n` with its nesting level (the specification's `exec`).
    pub(super) fn quick_exec(&mut self, code: &Rc<Code>, n: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            quick_s(*code, n, b),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_exec(nodes, n, st))) ==> r_unit(r, *final(self), bs_exec(nodes, n, st), old(self).eval_depth),
        decreases b, 3u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_exec(nodes, n, st));
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_eval_depth) {
            proof {
                if hyp {
                    lemma_exec_too_deep(nodes, n, st);
                    assert(with_depth(st, self.eval_depth as u64) == st);
                }
            }
            return Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
        }
        let ghost before = *self;
        let ghost s1 = with_depth(st, (st.depth + 1) as u64);
        proof { if hyp { lemma_step_exec(nodes, n, st); } }
        let d = self.eval_depth;
        self.eval_depth = d + 1;
        proof { if hyp { lemma_r_state_depth(before, *self, st); } }
        let r = self.quick_stmt(code, n, b, Ghost(nodes), Ghost(s1));
        let ghost mid = *self;
        self.eval_depth = d;
        proof {
            if hyp {
                let x = bs_exec_node(nodes, n, s1);
                if !done(x) { lemma_apply_not_done(K::Depth(st.depth), x); }
                if r is Ok {
                    lemma_r_state_depth(mid, *self, x.st);
                } else {
                    lemma_r_state_depth(mid, *self, with_depth(x.st, mid.eval_depth as u64));
                    assert(with_depth(with_depth(x.st, mid.eval_depth as u64), d as u64) == with_depth(x.st, d as u64));
                }
            }
        }
        r
    }

    /// Executes the statement at node `n` (the specification's `exec_node`).
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables, reason = "used only by the proof, which a normal build erases"))]
    fn quick_stmt(&mut self, code: &Rc<Code>, n: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            quick_s(*code, n, b),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_exec_node(nodes, n, st))) ==> r_unit(r, *final(self), bs_exec_node(nodes, n, st), old(self).eval_depth),
        decreases b, 2u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_exec_node(nodes, n, st));
        if !verified_should_abort_execution(self.break_flag, self.return_flag, self.quit_flag) {
            match &code.nodes[n] {
                PNode::ExprStmt(_) => { return self.quick_expr_stmt(code, n, b, Ghost(nodes), Ghost(st)); },
                PNode::Return(Some(_)) => { return self.quick_return(code, n, b, Ghost(nodes), Ghost(st)); },
                PNode::Block(list) => {
                    proof { if hyp { assert(r_node(code.nodes@[n as int], nodes[n as int])); lemma_step_block(nodes, n, list@, st); } }
                    return self.quick_list(code, n, b, Ghost(nodes), Ghost(st));
                },
                PNode::If(..) => { return self.quick_if(code, n, b, Ghost(nodes), Ghost(st)); },
                PNode::While(c, s) => {
                    proof { if hyp { assert(r_node(code.nodes@[n as int], nodes[n as int])); lemma_step_while(nodes, n, *c, *s, st); } }
                    return self.quick_loop(code, *c, None, *s, b, Ghost(nodes), Ghost(st));
                },
                PNode::For(..) => { return self.quick_for(code, n, b, Ghost(nodes), Ghost(st)); },
                _ => {},
            }
        }
        match self.leaf_stmt(code, n, Ghost(nodes), Ghost(st)) {
            Ok(_) => Ok(()),
            Err(err) => Err(err),
        }
    }

    /// An expression statement.
    fn quick_expr_stmt(&mut self, code: &Rc<Code>, n: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            quick_s(*code, n, b),
            !old(self).break_flag && !old(self).return_flag,
            code.nodes@[n as int] is ExprStmt,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_exec_node(nodes, n, st))) ==> r_unit(r, *final(self), bs_exec_node(nodes, n, st), old(self).eval_depth),
        decreases b, 0u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_exec_node(nodes, n, st));
        proof { if hyp { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let e = match &code.nodes[n] { PNode::ExprStmt(e) => *e, _ => { return Ok(()); } };
        let ghost x = bs_ev(nodes, e, st);
        proof {
            if hyp {
                lemma_step_expr_stmt(nodes, n, e, st);
                if !done(x) { lemma_apply_not_done(K::ExprStmt(nodes, e), x); }
            }
        }
        let v = match self.quick_eval(code, e, b - 1, Ghost(nodes), Ghost(st)) {
            Ok(v) => v,
            Err(err) => { return Err(err); },
        };
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
        Ok(())
    }

    /// `return (e)`.
    fn quick_return(&mut self, code: &Rc<Code>, n: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            quick_s(*code, n, b),
            !old(self).break_flag && !old(self).return_flag,
            code.nodes@[n as int] matches PNode::Return(Some(_)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_exec_node(nodes, n, st))) ==> r_unit(r, *final(self), bs_exec_node(nodes, n, st), old(self).eval_depth),
        decreases b, 0u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_exec_node(nodes, n, st));
        proof { if hyp { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let e = match &code.nodes[n] { PNode::Return(Some(e)) => *e, _ => { return Ok(()); } };
        let ghost x = bs_ev(nodes, e, st);
        proof {
            if hyp {
                lemma_step_return(nodes, n, e, st);
                if !done(x) { lemma_apply_not_done(K::Return, x); }
            }
        }
        let v = match self.quick_eval(code, e, b - 1, Ghost(nodes), Ghost(st)) {
            Ok(v) => v,
            Err(err) => { return Err(err); },
        };
        self.return_value = v;
        self.return_flag = true;
        Ok(())
    }

    /// `if`.
    fn quick_if(&mut self, code: &Rc<Code>, n: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            quick_s(*code, n, b),
            !old(self).break_flag && !old(self).return_flag,
            code.nodes@[n as int] is If,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_exec_node(nodes, n, st))) ==> r_unit(r, *final(self), bs_exec_node(nodes, n, st), old(self).eval_depth),
        decreases b, 0u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_exec_node(nodes, n, st));
        proof { if hyp { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let (c, s) = match &code.nodes[n] { PNode::If(c, s) => (*c, *s), _ => { return Ok(()); } };
        let ghost x = bs_ev(nodes, c, st);
        proof {
            if hyp {
                lemma_step_if(nodes, n, c, s, st);
                if !done(x) { lemma_apply_not_done(K::IfCond(nodes, s), x); }
            }
        }
        let v = match self.quick_eval(code, c, b - 1, Ghost(nodes), Ghost(st)) {
            Ok(v) => v,
            Err(err) => { return Err(err); },
        };
        proof { if hyp { lemma_is_zero_mag(x.val.mag); } }
        if v.is_zero() {
            return Ok(());
        }
        self.quick_exec(code, s, b - 1, Ghost(nodes), Ghost(x.st))
    }

    /// `for`: the initialization, then the loop.
    fn quick_for(&mut self, code: &Rc<Code>, n: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            quick_s(*code, n, b),
            !old(self).break_flag && !old(self).return_flag,
            code.nodes@[n as int] is For,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_exec_node(nodes, n, st))) ==> r_unit(r, *final(self), bs_exec_node(nodes, n, st), old(self).eval_depth),
        decreases b, 1u32,
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_exec_node(nodes, n, st));
        proof { if hyp { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let (i, c, p, s) = match &code.nodes[n] { PNode::For(i, c, p, s) => (*i, *c, *p, *s), _ => { return Ok(()); } };
        let ghost x = bs_ev(nodes, i, st);
        proof {
            if hyp {
                lemma_step_for(nodes, n, i, c, p, s, st);
                if !done(x) { lemma_apply_not_done(K::ForInit(nodes, c, p, s), x); }
            }
        }
        match self.quick_eval(code, i, b - 1, Ghost(nodes), Ghost(st)) {
            Ok(_) => {},
            Err(err) => { return Err(err); },
        }
        self.quick_loop(code, c, Some(p), s, b, Ghost(nodes), Ghost(x.st))
    }

    /// The statements of the block at node `n` (the specification's `bs_list`).
    fn quick_list(&mut self, code: &Rc<Code>, n: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            quick_s(*code, n, b),
            code.nodes@[n as int] is Block,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_list(nodes, block_of(*code, n), st)))
                ==> r_unit(r, *final(self), bs_list(nodes, block_of(*code, n), st), old(self).eval_depth),
        decreases b, 0u32,
    {
        let ghost e0 = *self;
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(bs_list(nodes, block_of(*code, n), st));
        let ghost x0 = bs_list(nodes, block_of(*code, n), st);
        let list = match &code.nodes[n] {
            PNode::Block(list) => list,
            _ => { return Ok(()); },
        };
        let ghost mut s = st;
        proof {
            assert(list@.skip(0) =~= list@);
            assert(block_of(*code, n) == list@);
        }
        let mut i = 0;
        while i < list.len()
            invariant
                e0 == *old(self),
                self.inv(),
                self.eval_depth == e0.eval_depth,
                n < code.nodes@.len(),
                code.nodes@[n as int] == PNode::Block(*list),
                b > 0,
                i <= list@.len(),
                forall|j: int| #![trigger list@[j]] 0 <= j < list@.len() ==> quick_s(*code, list@[j], (b - 1) as u32),
                hyp == (r_rc(*code, nodes) && r_state(e0, st) && done(x0)),
                x0 == bs_list(nodes, list@, st),
                hyp ==> (r_state(*self, s) && bs_list(nodes, list@.skip(i as int), s) == x0),
            decreases list.len() - i,
        {
            let ghost l = list@.skip(i as int);
            let ghost x = bs_exec(nodes, list@[i as int], s);
            proof {
                if hyp {
                    lemma_step_list(nodes, l, s);
                    assert(l[0] == list@[i as int]);
                    if !done(x) { lemma_apply_not_done(K::List(nodes, l.drop_first()), x); }
                }
            }
            match self.quick_exec(code, list[i], b - 1, Ghost(nodes), Ghost(s)) {
                Ok(()) => {},
                Err(err) => { return Err(err); },
            }
            if self.break_flag || self.return_flag {
                return Ok(());
            }
            proof {
                if hyp {
                    assert(l.drop_first() =~= list@.skip(i as int + 1));
                }
                s = x.st;
            }
            i += 1;
        }
        proof {
            if hyp {
                assert(list@.skip(i as int).len() == 0);
                lemma_list_end(nodes, list@.skip(i as int), s);
            }
        }
        Ok(())
    }

    /// A loop from its condition on (the specification's `bs_loop`).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::allow(decreases_when_exec_allows_no_decreases_clause)]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    #[allow(clippy::single_match, reason = "the other arm only updates ghost state, so it is empty outside Verus")]
    fn quick_loop(&mut self, code: &Rc<Code>, c: usize, p: Option<usize>, s: usize, b: u32, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            b > 0,
            quick(*code, c, (b - 1) as u32),
            p matches Some(q) ==> quick(*code, q, (b - 1) as u32),
            quick_s(*code, s, (b - 1) as u32),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_rc(*code, nodes) && r_state(*old(self), st) && done(bs_loop(nodes, c, opt_index(p), p is Some, s, st)))
                ==> r_unit(r, *final(self), bs_loop(nodes, c, opt_index(p), p is Some, s, st), old(self).eval_depth),
        decreases b, 0u32,
    {
        let ghost e0 = *self;
        let ghost x0 = bs_loop(nodes, c, opt_index(p), p is Some, s, st);
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, st) && done(x0);
        let ghost pi = opt_index(p);
        let ghost hp = p is Some;
        let ghost mut cur = st;
        loop
            invariant
                e0 == *old(self),
                self.inv(),
                self.eval_depth == e0.eval_depth,
                b > 0,
                quick(*code, c, (b - 1) as u32),
                p matches Some(q) ==> quick(*code, q, (b - 1) as u32),
                quick_s(*code, s, (b - 1) as u32),
                pi == opt_index(p),
                hp == p is Some,
                x0 == bs_loop(nodes, c, pi, hp, s, st),
                hyp == (r_rc(*code, nodes) && r_state(e0, st) && done(x0)),
                hyp ==> (r_state(*self, cur) && bs_loop(nodes, c, pi, hp, s, cur) == x0),
        {
            let ghost x = bs_ev(nodes, c, cur);
            proof {
                if hyp {
                    lemma_step_loop(nodes, c, pi, hp, s, cur);
                    if !done(x) { lemma_apply_not_done(K::LoopCond(nodes, c, pi, hp, s), x); }
                }
            }
            let v = match self.quick_eval(code, c, b - 1, Ghost(nodes), Ghost(cur)) {
                Ok(v) => v,
                Err(err) => { return Err(err); },
            };
            proof { if hyp { lemma_is_zero_mag(x.val.mag); } }
            if v.is_zero() {
                return Ok(());
            }
            let ghost w = bs_exec(nodes, s, x.st);
            proof { if hyp && !done(w) { lemma_apply_not_done(K::LoopBody(nodes, c, pi, hp, s), w); } }
            match self.quick_exec(code, s, b - 1, Ghost(nodes), Ghost(x.st)) {
                Ok(()) => {},
                Err(err) => { return Err(err); },
            }
            let (should_break, next_break) = verified_loop_post_body_action(self.break_flag, self.return_flag, self.quit_flag);
            self.break_flag = next_break;
            let ghost st2 = bc_spec::eval::with_flags(w.st, false, w.st.ret, w.st.ret_val);
            if should_break {
                return Ok(());
            }
            match p {
                Some(post) => {
                    let ghost q = bs_ev(nodes, post, st2);
                    proof { if hyp && !done(q) { lemma_apply_not_done(K::LoopPost(nodes, c, post, true, s), q); } }
                    match self.quick_eval(code, post, b - 1, Ghost(nodes), Ghost(st2)) {
                        Ok(_) => {},
                        Err(err) => { return Err(err); },
                    }
                    proof { cur = q.st; }
                },
                None => {
                    proof { cur = st2; }
                },
            }
        }
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{Lexer, Parser};
    use alloc::format;

    fn first_statement_is_quick(src: &str) -> bool {
        let mut parser = Parser::try_new(Lexer::new(src.as_bytes())).unwrap();
        let stmts = parser.try_parse_program().unwrap();
        let code = Rc::new(parser.take_code());
        Evaluator::quick_stmt_ok(&code, stmts[0], QUICK_BUDGET)
    }

    /// The check counts a statement's own node and every statement in it, and the parser
    /// wraps the statements of a unit in a block of their own: a unit `{ 62 statements }` is
    /// 64 nodes, the most the fast path takes, and an `if` around the block is one more.
    #[test]
    fn test_statement_budget_boundary() {
        let n = QUICK_STMTS as usize;
        let block = |w: usize| format!("{{\n{}}}\n", "x = x + 1\n".repeat(w));
        assert!(first_statement_is_quick(&block(n - 2)));
        assert!(!first_statement_is_quick(&block(n - 1)));
        assert!(first_statement_is_quick(&format!(
            "if (1) {}",
            block(n - 3)
        )));
        assert!(!first_statement_is_quick(&format!(
            "if (1) {}",
            block(n - 2)
        )));
    }
}
