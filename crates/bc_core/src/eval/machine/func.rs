// SPDX-License-Identifier: MIT

//! The machine's function calls: the arguments (`step_call`, `args_next`, `ret_argval`),
//! entering and leaving the body (`enter_call`, `body_next`, `ret_body`, `ret_call`), and the
//! `-l` functions (`math_start`, `finish_math1`, `finish_bessel`).

use super::*;

verus! {

/// Collecting the arguments of the call at node `n` from the `i`-th on.
pub(crate) open spec fn m_args(e: Evaluator, fr: Seq<Frame>, code: Rc<Code>, nodes: SpecNodes, n: usize, fd: FunctionDef, i: usize, vals: Seq<(String, ArgValue)>, gf: Func, acc: Seq<bc_spec::eval::ArgVal>, g: MG, goal: ER) -> bool {
    &&& r_rc(code, nodes)
    &&& r_state(e, g.s)
    &&& r_mframes(fr, g.ks, code, nodes)
    &&& done(goal)
    &&& r_func(fd, gf)
    &&& n < nodes.len()
    &&& call_named(code, n, gf.name)
    &&& nodes[n as int] is Call
    &&& i <= call_args(nodes, n).len()
    &&& call_args(nodes, n).len() == gf.params.len()
    &&& den(g.ks, after_args(gf, bs_args(nodes, call_args(nodes, n).skip(i as int), gf.params.skip(i as int), g.s, acc))) == goal
    &&& vals.len() == i
    &&& r_argvals(vals, acc)
}

/// The parameters of a function.
pub(crate) open spec fn fd_params(fd: FunctionDef) -> Seq<Param> {
    if fd.def < fd.code.nodes@.len() {
        match fd.code.nodes@[fd.def as int] {
            PNode::Define(decl) => decl.params@,
            _ => Seq::empty(),
        }
    } else {
        Seq::empty()
    }
}

impl Evaluator {
    /// A call (the specification's `ev_call`): the function, then its arguments.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(30)]
    pub(super) fn step_call(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, name: &String, args: &Vec<PArg>, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Call(*name, *args),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_node(*old(self), old(frames)@, *code, nodes, n, g, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_node(*self, frames@, *code, nodes, n, g, goal);
        let ghost parent = bs_ev_node(nodes, n, g.s);
        let ghost sname = text_view(*name);
        let ghost sargs = match nodes[n as int] { Node::Call(_, a) => a, _ => Seq::empty() };
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            if hyp {
                lemma_den_done(g.ks, parent);
                assert(r_node(code.nodes@[n as int], nodes[n as int]));
            }
        }
        let fd = match self.functions.get(name) {
            Some(fd) => fd.clone(),
            None => {
                if self.math_enabled {
                    return self.math_start(frames, code, n, name, args, Ghost(nodes), Ghost(g), Ghost(goal), Ghost(d0));
                }
                let r = Err(BcError::Runtime { kind: RuntimeError::UndefinedFunction(name.clone()), func: None });
                proof {
                    if hyp {
                        lemma_func_absent(self.functions@, g.s.funcs, *name);
                        lemma_step_call_undefined(nodes, n, sname, sargs, g.s);
                        assert(with_depth(g.s, self.eval_depth as u64) == g.s);
                    }
                }
                return (Step::Ret(r), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }));
            },
        };
        let ghost gf = bc_spec::eval::find_func(g.s.funcs, sname)->Some_0;
        proof {
            if hyp {
                assert(self.functions@.contains_key(*name));
                assert(r_func(fd, gf));
                lemma_find_func_index(g.s.funcs, sname);
                assert(r_node(fd.code.nodes@[fd.def as int], gf.nodes[fd.def as int]));
            }
        }
        if fd.def >= fd.code.nodes.len() {
            return (Step::Ret(Ok(BCNum::zero())), Ghost(g));
        }
        let nparams = match &fd.code.nodes[fd.def] {
            PNode::Define(decl) => decl.params.len(),
            _ => { return (Step::Ret(Ok(BCNum::zero())), Ghost(g)); },
        };
        if args.len() != nparams {
            let r = Err(BcError::Runtime { kind: RuntimeError::ParameterMismatch, func: None });
            proof {
                if hyp {
                    assert(r_args(args@, sargs));
                    lemma_step_call_mismatch(nodes, n, sname, sargs, g.s, gf);
                    assert(with_depth(g.s, self.eval_depth as u64) == g.s);
                }
            }
            return (Step::Ret(r), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }));
        }
        proof {
            if hyp {
                assert(r_args(args@, sargs));
                lemma_step_call(nodes, n, sname, sargs, g.s, gf);
                assert(sargs.skip(0) =~= sargs);
                assert(gf.params.skip(0) =~= gf.params);
            }
        }
        self.args_next(frames, code, n, fd, 0, Vec::new(), Ghost(nodes), Ghost(gf), Ghost(Seq::empty()), Ghost(g), Ghost(goal), Ghost(d0))
    }

    /// The arguments of the call at node `n` from the `i`-th on (the specification's `ev_args`),
    /// then the call.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(80)]
    fn args_next(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, fd: FunctionDef, i0: usize, vals0: Vec<(String, ArgValue)>, Ghost(nodes): Ghost<SpecNodes>, Ghost(gf): Ghost<SpecFunc>, Ghost(acc0): Ghost<SpecArgVals>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            args_ok(vals0@),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_args(*old(self), old(frames)@, *code, nodes, n, fd, i0, vals0@, gf, acc0, g, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_args(*self, frames@, *code, nodes, n, fd, i0, vals0@, gf, acc0, g, goal);
        let ghost sargs = call_args(nodes, n);
        let mut i = i0;
        let mut vals = vals0;
        let ghost mut acc = acc0;
        proof { if hyp { assert(r_node(code.nodes@[n as int], nodes[n as int])); assert(r_node(fd.code.nodes@[fd.def as int], gf.nodes[fd.def as int])); } }
        if n >= code.nodes.len() || fd.def >= fd.code.nodes.len() {
            return (Step::Ret(Ok(BCNum::zero())), Ghost(g));
        }
        let args = match &code.nodes[n] {
            PNode::Call(_, args) => args,
            _ => { return (Step::Ret(Ok(BCNum::zero())), Ghost(g)); },
        };
        let params = match &fd.code.nodes[fd.def] {
            PNode::Define(decl) => &decl.params,
            _ => { return (Step::Ret(Ok(BCNum::zero())), Ghost(g)); },
        };
        loop
            invariant
                self.inv(),
                frames_ok(frames@, self.eval_depth, d0),
                wants(frames@, d0),
                args_ok(vals@),
                n < code.nodes@.len(),
                code.nodes@[n as int] matches PNode::Call(_, a) && a == *args,
                fd.def < fd.code.nodes@.len(),
                fd.code.nodes@[fd.def as int] matches PNode::Define(decl) && decl.params == *params,
                sargs == call_args(nodes, n),
                hyp == m_args(*old(self), old(frames)@, *code, nodes, n, fd, i0, vals0@, gf, acc0, g, goal),
                hyp ==> r_params(params@, gf.params) && r_args(args@, sargs) && sargs.len() == gf.params.len(),
                hyp ==> m_args(*self, frames@, *code, nodes, n, fd, i, vals@, gf, acc, g, goal),
            decreases args.len() - i,
        {
            let ghost a = sargs.skip(i as int);
            let ghost p = gf.params.skip(i as int);
            let ghost parent = after_args(gf, bs_args(nodes, a, p, g.s, acc));
            proof {
                if hyp {
                    lemma_den_done(g.ks, parent);
                    if i < args.len() {
                        lemma_r_args_index(args@, sargs, i as int);
                        assert(r_param(params@[i as int], gf.params[i as int]));
                        assert(r_arg(args@[i as int], sargs[i as int]));
                        assert(a[0] == sargs[i as int]);
                        assert(p[0] == gf.params[i as int]);
                        assert(a.drop_first() =~= sargs.skip(i as int + 1));
                        assert(p.drop_first() =~= gf.params.skip(i as int + 1));
                    }
                }
            }
            if i >= args.len() || i >= params.len() {
                proof {
                    if hyp {
                        assert(a.len() == 0);
                        lemma_args_end(nodes, a, p, g.s, acc);
                        assert(r_argvals(vals@, acc));
                        assert(call_named(*code, n, gf.name));
                        assert(parent == leave(gf, saved_of(g.s), bs_body(gf.nodes, gf.body, enter(gf, acc, g.s))));
                        assert(den(g.ks, parent) == goal);
                        assert(r_mframes(frames@, g.ks, *code, nodes));
                        assert(r_state(*self, g.s));
                        assert(r_func(fd, gf));
                        assert(done(goal));
                        assert(r_rc(*code, nodes));
                    }
                }
                return self.enter_call(frames, code, n, fd, vals, Ghost(nodes), Ghost(gf), Ghost(acc), Ghost(g), Ghost(goal), Ghost(d0));
            }
            let param = &params[i];
            match &args[i] {
                PArg::Array(arg_name) => {
                    proof { if hyp { assert(a[0].is_array && a[0].name == text_view(*arg_name)); assert(p[0].is_array == param.is_array && p[0].name == text_view(param.name)); } }
                    if !param.is_array {
                        let r = Err(BcError::Runtime { kind: RuntimeError::ParameterTypeMismatch(param.name.clone()), func: None });
                        proof {
                            if hyp {
                                lemma_args_end(nodes, a, p, g.s, acc);
                                assert(with_depth(g.s, self.eval_depth as u64) == g.s);
                                assert(parent == bc_spec::eval::er_err(g.s, bc_spec::eval::msg_parameter_type(p[0].name)));
                                assert(r_err(r->Err_0, parent.err));
                                assert(den(g.ks, parent) == goal);
                            }
                        }
                        return (Step::Ret(r), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }));
                    }
                    let frame = self.arr_frame_clone(arg_name, Ghost(g.s));
                    let ghost v = bc_spec::eval::ArgVal { is_array: true, name: param_name(gf, i), val: bc_spec::eval::zero_num(), frame: arr_top(g.s.arrays, text_view(*arg_name)) };
                    let ghost vals0 = vals@;
                    vals.push((param.name.clone(), ArgValue::Array(frame)));
                    proof {
                        assert(vals@ == vals0.push(vals@.last()));
                        assert forall|j: int| 0 <= j < vals@.len() implies match (#[trigger] vals@[j]).1 {
                            ArgValue::Array(f) => frame_ok(f@),
                            ArgValue::Scalar(v) => v.scale <= BC_SCALE_MAX,
                        } by { if j < vals0.len() { assert(vals@[j] == vals0[j]); } }
                        if hyp {
                            lemma_step_arg_array(nodes, a, p, g.s, acc);
                            assert(r_arg(PArg::Array(*arg_name), a[0]));
                            assert(r_argval(vals@.last(), v));
                            assert forall|j: int| 0 <= j < vals@.len() implies #[trigger] r_argval(vals@[j], acc.push(v)[j]) by {
                                if j < vals0.len() { assert(vals@[j] == vals0[j]); }
                            }
                            assert(sargs.skip(i as int + 1) == a.drop_first());
                            acc = acc.push(v);
                        }
                    }
                    i += 1;
                },
                PArg::Expr(e) => {
                    proof { if hyp { assert(!a[0].is_array && a[0].expr == *e); assert(p[0].is_array == param.is_array && p[0].name == text_view(param.name)); } }
                    if param.is_array {
                        let r = Err(BcError::Runtime { kind: RuntimeError::ParameterTypeMismatch(param.name.clone()), func: None });
                        proof { if hyp { lemma_args_end(nodes, a, p, g.s, acc); assert(with_depth(g.s, self.eval_depth as u64) == g.s); } }
                        return (Step::Ret(r), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }));
                    }
                    let e = *e;
                    let ghost k = K::ArgVal(nodes, gf, a.drop_first(), p.drop_first(), param_name(gf, i), acc);
                    proof {
                        if hyp {
                            lemma_step_arg(nodes, gf, a, p, g.s, acc);
                            assert(param_name(gf, i) == p[0].name);
                            assert(r_mframe(Frame::ArgVal(fd, n, i, vals), k, *code, nodes));
                            assert(den(g.ks, parent) == goal);
                            assert(r_mframes(frames@, g.ks, *code, nodes));
                            assert(r_state(*self, g.s));
                            assert(done(parent) ==> parent == apply(k, bs_ev(nodes, e, g.s)));
                        }
                    }
                    return self.push_sub(frames, code, Frame::ArgVal(fd, n, i, vals), e, Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
                },
            }
        }
    }

    /// Enters the function with its arguments (the specification's `run_call`, up to its body).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(40)]
    fn enter_call(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, fd: FunctionDef, vals: Vec<(String, ArgValue)>, Ghost(nodes): Ghost<SpecNodes>, Ghost(gf): Ghost<SpecFunc>, Ghost(acc): Ghost<SpecArgVals>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            args_ok(vals@),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            (r_rc(*code, nodes) && r_state(*old(self), g.s) && r_mframes(old(frames)@, g.ks, *code, nodes) && done(goal)
                && r_func(fd, gf) && r_argvals(vals@, acc) && n < code.nodes@.len() && call_named(*code, n, gf.name)
                && den(g.ks, leave(gf, saved_of(g.s), bs_body(gf.nodes, gf.body, enter(gf, acc, g.s)))) == goal)
                ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = r_rc(*code, nodes) && r_state(*self, g.s) && r_mframes(frames@, g.ks, *code, nodes) && done(goal)
                && r_func(fd, gf) && r_argvals(vals@, acc) && n < code.nodes@.len() && call_named(*code, n, gf.name)
                && den(g.ks, leave(gf, saved_of(g.s), bs_body(gf.nodes, gf.body, enter(gf, acc, g.s)))) == goal;
        proof { if hyp { assert(r_node(fd.code.nodes@[fd.def as int], gf.nodes[fd.def as int])); } }
        if n >= code.nodes.len() || fd.def >= fd.code.nodes.len() {
            return (Step::Ret(Ok(BCNum::zero())), Ghost(g));
        }
        let name = match &code.nodes[n] {
            PNode::Call(name, _) => name.clone(),
            _ => { return (Step::Ret(Ok(BCNum::zero())), Ghost(g)); },
        };
        let callee = share_code(&fd.code);
        let def = fd.def;
        let (params, autos) = match &callee.nodes[def] {
            PNode::Define(decl) => (&decl.params, &decl.autos),
            _ => { return (Step::Ret(Ok(BCNum::zero())), Ghost(g)); },
        };
        let ghost s0 = g.s;
        let ghost sv = saved_of(s0);
        self.push_args_ref(vals, Ghost(acc), Ghost(s0));
        let ghost sp = bc_spec::eval::push_args(s0, acc);
        self.push_autos_ref(autos, Ghost(gf.autos), Ghost(sp));
        let ghost s1 = bc_spec::eval::push_autos(sp, gf.autos);
        let saved_flag = self.return_flag;
        let saved_inv = self.invocation_ibase;
        let mut saved_val = BCNum::zero();
        core::mem::swap(&mut self.return_value, &mut saved_val);
        self.return_flag = false;
        self.invocation_ibase = Some(self.ibase);
        let ghost calls1 = self.call_stack@;
        self.call_stack.push(name.clone());
        let ghost s2 = bc_spec::eval::with_flags(s1, s1.brk, false, bc_spec::eval::zero_num());
        let ghost s3 = bc_spec::eval::with_call(s2, s2.calls.push(gf.name), true, s2.ibase);
        proof {
            if hyp {
                lemma_push_args_keeps(s0, acc);
                lemma_push_autos_keeps(sp, gf.autos);
                assert(r_calls(self.call_stack@, s3.calls)) by {
                    assert forall|i: int| 0 <= i < self.call_stack@.len() implies #[trigger] text_view(self.call_stack@[i]) == s3.calls[i] by {
                        if i < calls1.len() {
                            assert(self.call_stack@[i] == calls1[i]);
                        }
                    }
                }
                assert(r_state(*self, s3));
                assert(s3 == enter(gf, acc, s0));
            }
        }
        let ghost f0 = frames@;
        let ghost k = K::Call(gf, sv, nodes);
        let caller = share_code(code);
        let fr = Frame::Call(caller, def, name, saved_flag, saved_inv, saved_val);
        let ghost fv = fr;
        frames.push(fr);
        proof {
            assert(frames@ == f0.push(fv));
            assert(frames@.drop_last() =~= f0);
            assert(frames_ok(frames@, self.eval_depth, d0));
            if hyp {
                lemma_den_done(g.ks, leave(gf, sv, bs_body(gf.nodes, gf.body, s3)));
                lemma_den_push(g.ks, k, bs_body(gf.nodes, gf.body, s3));
                assert(r_call_frame(fv, k, callee, gf.nodes));
                lemma_push_call(f0, g.ks, fv, k, *code, nodes, callee, gf.nodes);
                assert(gf.body.skip(0) =~= gf.body);
            }
        }
        (Step::Enter(callee, def), Ghost(MG { nodes: gf.nodes, ks: g.ks.push(k), s: s3, x: g.x }))
    }

    /// The body of the function at node `def` from statement `i` on (the specification's
    /// `exec_body`).
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn body_next(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, def: usize, i: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            old(frames)@.len() > 0 && (old(frames)@.last() is Call || old(frames)@.last() is Body) || !wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_body(*old(self), old(frames)@, *code, nodes, def, i, g, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_body(*self, frames@, *code, nodes, def, i, g, goal);
        proof { if hyp { assert(r_node(code.nodes@[def as int], nodes[def as int])); } }
        if def < code.nodes.len() {
            if let PNode::Define(decl) = &code.nodes[def] {
                let body = &decl.body;
                let ghost rest = body@.skip(i as int);
                let ghost parent = bs_body(nodes, rest, g.s);
                if i >= body.len() {
                    proof { if hyp { lemma_body_end(nodes, rest, g.s); } }
                    return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: g.ks, s: g.s, x: parent }));
                }
                let ghost k = K::Body(nodes, body@.skip(i as int + 1));
                proof {
                    if hyp {
                        lemma_den_done(g.ks, parent);
                        lemma_step_body(nodes, rest, g.s);
                        assert(rest.drop_first() =~= body@.skip(i as int + 1));
                        assert(rest[0] == body@[i as int]);
                    }
                }
                return self.push_sub_s(frames, code, Frame::Body(def, i + 1), body[i], Ghost(nodes), Ghost(k), Ghost(g), Ghost(goal), Ghost(parent), Ghost(d0));
            }
        }
        (Step::Ret(Ok(BCNum::zero())), Ghost(g))
    }

    /// Leaves the function whose body gave the result `ret` (the specification's `leave`).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(30)]
    pub(super) fn ret_call(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, caller: Rc<Code>, def: usize, name: String, saved_flag: bool, saved_inv: Option<usize>, saved_val: BCNum, ret: Result<BCNum, BcError>, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            saved_val.scale <= BC_SCALE_MAX,
            match saved_inv {
                Some(b) => 2 <= b <= IBASE_MAX,
                None => true,
            },
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            (r_rc(*code, nodes) && r_ret(ret, *old(self), x, false) && r_call_frame(Frame::Call(caller, def, name, saved_flag, saved_inv, saved_val), k, *code, nodes)
                && (k matches K::Call(_, _, cn) && r_rc(caller, cn) && r_mframes(old(frames)@, ks1, caller, cn))
                && den(ks1, apply(k, x)) == goal && done(goal))
                ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = r_rc(*code, nodes) && r_ret(ret, *self, x, false) && r_call_frame(Frame::Call(caller, def, name, saved_flag, saved_inv, saved_val), k, *code, nodes)
                && (k matches K::Call(_, _, cn) && r_rc(caller, cn) && r_mframes(frames@, ks1, caller, cn))
                && den(ks1, apply(k, x)) == goal && done(goal);
        let ghost (gf, sv, cn) = match k { K::Call(f, s, c) => (f, s, c), _ => arbitrary() };
        let ghost y = apply(k, x);
        let ghost d = self.eval_depth;
        proof { if hyp { assert(r_node(code.nodes@[def as int], nodes[def as int])); lemma_den_done(ks1, y); } }
        if def >= code.nodes.len() {
            return (Step::Leave(caller, Ok(BCNum::zero())), Ghost(MG { nodes: cn, ks: ks1, s: x.st, x: y }));
        }
        let (params, autos) = match &code.nodes[def] {
            PNode::Define(decl) => (&decl.params, &decl.autos),
            _ => { return (Step::Leave(caller, Ok(BCNum::zero())), Ghost(MG { nodes: cn, ks: ks1, s: x.st, x: y })); },
        };
        let ghost sl = if ret is Ok { x.st } else { with_depth(x.st, d as u64) };
        let ret_val = self.leave_call(autos, params, saved_flag, saved_inv, saved_val, Ghost(gf), Ghost(sv), Ghost(sl));
        let r = match ret {
            Ok(_) => Ok(ret_val),
            Err(e) => Err(e.in_function(&name)),
        };
        proof {
            if hyp {
                lemma_leave_call_depth(x.st, gf, sv, d as u64);
            }
        }
        (Step::Leave(caller, r), Ghost(MG { nodes: cn, ks: ks1, s: x.st, x: y }))
    }

    /// With the result of the function body's statement (the frame `K::Body`).
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn ret_body(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, def: usize, i: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            !wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after_s(*old(self), old(frames)@, *code, nodes, Frame::Body(def, i), k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after_s(*self, frames@, *code, nodes, Frame::Body(def, i), k, ks1, x, goal);
        let ghost y = apply(k, x);
        proof { if hyp { lemma_den_done(ks1, y); } }
        if self.return_flag {
            return (Step::Ret(Ok(BCNum::zero())), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y }));
        }
        self.body_next(frames, code, def, i, Ghost(nodes), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: y }), Ghost(goal), Ghost(d0))
    }

    /// With the value of a value argument (the frame `K::ArgVal`).
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn ret_argval(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, fd: FunctionDef, n: usize, i: usize, vals: Vec<(String, ArgValue)>, v: BCNum, Ghost(nodes): Ghost<SpecNodes>, Ghost(k): Ghost<MK>, Ghost(ks1): Ghost<MKs>, Ghost(x): Ghost<MResult>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
            v.scale <= BC_SCALE_MAX,
            args_ok(vals@),
            i < usize::MAX,
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            m_after(*old(self), old(frames)@, *code, nodes, Frame::ArgVal(fd, n, i, vals), v, k, ks1, x, goal) ==> m_step(*final(self), final(frames)@, *code, nodes, r.0, r.1@, goal, d0),
    {
        let ghost hyp = m_after(*self, frames@, *code, nodes, Frame::ArgVal(fd, n, i, vals), v, k, ks1, x, goal);
        let ghost (gf, acc, pname) = match k { K::ArgVal(_, f, _, _, nm, a) => (f, a, nm), _ => arbitrary() };
        let ghost sv = bc_spec::eval::ArgVal { is_array: false, name: pname, val: x.val, frame: bc_spec::eval::empty_frame() };
        proof { if hyp { assert(r_node(fd.code.nodes@[fd.def as int], gf.nodes[fd.def as int])); } }
        let pn = if fd.def < fd.code.nodes.len() {
            match &fd.code.nodes[fd.def] {
                PNode::Define(decl) => if i < decl.params.len() { decl.params[i].name.clone() } else { String::new() },
                _ => String::new(),
            }
        } else {
            String::new()
        };
        let mut vals = vals;
        let ghost vals0 = vals@;
        vals.push((pn, ArgValue::Scalar(v)));
        proof {
            assert(vals@ == vals0.push(vals@.last()));
            assert forall|j: int| 0 <= j < vals@.len() implies match (#[trigger] vals@[j]).1 {
                ArgValue::Array(f) => frame_ok(f@),
                ArgValue::Scalar(v) => v.scale <= BC_SCALE_MAX,
            } by { if j < vals0.len() { assert(vals@[j] == vals0[j]); } }
            if hyp {
                assert(r_param(fd_params(fd)[i as int], gf.params[i as int]));
                assert(r_argval(vals@.last(), sv));
                assert forall|j: int| 0 <= j < vals@.len() implies #[trigger] r_argval(vals@[j], acc.push(sv)[j]) by {
                    if j < vals0.len() { assert(vals@[j] == vals0[j]); }
                }
            }
        }
        self.args_next(frames, code, n, fd, i + 1, vals, Ghost(nodes), Ghost(gf), Ghost(acc.push(sv)), Ghost(MG { nodes: nodes, ks: ks1, s: x.st, x: x }), Ghost(goal), Ghost(d0))
    }

    /// A call of a `-l` function (no user function has the name): its arguments go on the stack.
    /// The specification does not model `-l`, so nothing relates these frames.
    #[verifier::exec_allows_no_decreases_clause]
    fn math_start(&mut self, frames: &mut Vec<Frame>, code: &Rc<Code>, n: usize, name: &String, args: &Vec<PArg>, Ghost(nodes): Ghost<SpecNodes>, Ghost(g): Ghost<MG>, Ghost(goal): Ghost<MResult>, Ghost(d0): Ghost<MRoot>) -> (r: (Step, Ghost<MG>))
        requires
            old(self).inv(),
            old(self).math_enabled,
            frames_ok(old(frames)@, old(self).eval_depth, d0),
            wants(old(frames)@, d0),
        ensures
            final(self).inv(),
            frames_ok(final(frames)@, final(self).eval_depth, d0),
            step_ok(r.0, final(frames)@, d0),
            !m_node(*old(self), old(frames)@, *code, nodes, n, g, goal),
    {
        let nb = name.as_str().as_bytes();
        let ghost f0 = frames@;
        if nb.len() == 1 && args.len() == 1 {
            let c = nb[0];
            if c == 115 || c == 99 || c == 97 || c == 108 || c == 101 {
                if let PArg::Expr(e) = &args[0] {
                    let e = *e;
                    frames.push(Frame::Math1(n));
                    proof { assert(frames@.drop_last() =~= f0); assert(frames_ok(frames@, self.eval_depth, d0)); }
                    return (Step::Eval(e), Ghost(g));
                }
            }
        }
        if nb.len() == 1 && nb[0] == 106 && args.len() == 2 {
            if let PArg::Expr(e) = &args[0] {
                if let PArg::Expr(_) = &args[1] {
                    let e = *e;
                    frames.push(Frame::MathJ1(n));
                    proof { assert(frames@.drop_last() =~= f0); assert(frames_ok(frames@, self.eval_depth, d0)); }
                    return (Step::Eval(e), Ghost(g));
                }
            }
        }
        (Step::Ret(Err(BcError::Runtime { kind: RuntimeError::UndefinedFunction(name.clone()), func: None })), Ghost(g))
    }

    /// `j(n, x)`.
    pub(super) fn finish_bessel(&self, n: &BCNum, x: &BCNum) -> (r: Result<BCNum, BcError>)
        requires
            self.inv(),
            n.scale <= BC_SCALE_MAX,
            x.scale <= BC_SCALE_MAX,
        ensures
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            r is Ok ==> r->Ok_0.scale == self.scale,
            r is Ok ==> math_ok(seq![106u8], r->Ok_0),
    {
        match bc_bessel(n, x, self.scale) {
            Ok(v) => {
                proof {
                    let j = seq![106u8];
                    assert(j[0] == 106u8);
                    assert(j != seq![115u8] && j != seq![99u8] && j != seq![97u8] && j != seq![108u8] && j != seq![101u8]) by {
                        assert(seq![115u8][0] == 115u8 && seq![99u8][0] == 99u8 && seq![97u8][0] == 97u8);
                        assert(seq![108u8][0] == 108u8 && seq![101u8][0] == 101u8);
                    }
                    lemma_math_ok(j, *n, *x, v);
                }
                Ok(v)
            },
            Err(kind) => Err(BcError::Runtime { kind, func: None }),
        }
    }

    /// `s`, `c`, `a`, `l` or `e` of `x` (the `-l` function called at node `n`).
    pub(super) fn finish_math1(&self, code: &Rc<Code>, n: usize, x: BCNum) -> (r: Result<BCNum, BcError>)
        requires
            self.inv(),
            x.scale <= BC_SCALE_MAX,
        ensures
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            r is Ok ==> r->Ok_0.scale == self.scale,
            r is Ok && n < code.nodes@.len() ==> (code.nodes@[n as int] matches PNode::Call(name, _) && math_ok(text_view(name), r->Ok_0)),
    {
        if n >= code.nodes.len() {
            return Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
        }
        let name = match &code.nodes[n] {
            PNode::Call(name, _) => name,
            _ => { return Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None }); },
        };
        let nb = name.as_str().as_bytes();
        if nb.len() != 1 {
            return Err(BcError::Runtime { kind: RuntimeError::UndefinedFunction(name.clone()), func: None });
        }
        let c = nb[0];
        let scale = self.scale;
        let res = if c == 115 {
            bc_sin(&x, scale)
        } else if c == 99 {
            bc_cos(&x, scale)
        } else if c == 97 {
            bc_atan(&x, scale)
        } else if c == 108 {
            bc_ln(&x, scale)
        } else if c == 101 {
            bc_exp(&x, scale)
        } else {
            return Err(BcError::Runtime { kind: RuntimeError::UndefinedFunction(name.clone()), func: None });
        };
        match res {
            Ok(v) => {
                proof {
                    assert(nb@ =~= seq![c]);
                    lemma_math_ok(text_view(*name), x, v, v);
                }
                Ok(v)
            },
            Err(kind) => Err(BcError::Runtime { kind, func: None }),
        }
    }
}

} // verus!
