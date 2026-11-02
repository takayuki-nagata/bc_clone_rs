// SPDX-License-Identifier: MIT

//! Function calls (the specification's `ev_call` and `run_call`): arguments, frames and
//! the caller's restored state.

use super::*;

verus! {

impl Evaluator {
    /// Pushes a frame with value `v` for variable `name` (the specification's `var_update` with
    /// op 1).
    pub(crate) fn push_var_ref(&mut self, name: String, v: BCNum, Ghost(st): Ghost<SpecState>, Ghost(x): Ghost<SpecNum>)
        requires
            old(self).inv(),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_num(v, x)) ==> r_state(*final(self),
                bc_spec::eval::with_vars(st, bc_spec::eval::var_update(st.vars, text_view(name), 1u8, x, Seq::empty()))),
    {
        let ghost m = self.variables@;
        let ghost nm_name = name;
        let ghost gv = v;
        let ghost hyp = r_state(*self, st) && r_num(v, x);
        self.var_push(name, v);
        proof {
            if hyp {
                let found = var_lookup(st.vars, text_view(nm_name));
                let t = self.variables@[nm_name]@;
                if m.contains_key(nm_name) {
                    let s = found->Some_0;
                    assert(r_stack(m[nm_name]@, s));
                    assert forall|i: int| 0 <= i < t.len() implies #[trigger] r_num(t[i], s.push(x)[i]) by {
                        if i < s.len() {
                            assert(t[i] == m[nm_name]@[i]);
                        }
                    }
                    assert(r_stack(t, upd_stack(found, 1u8, x)->Some_0));
                } else {
                    lemma_var_absent(m, st.vars, nm_name);
                    let ss = upd_stack(found, 1u8, x)->Some_0;
                    assert(ss =~= seq![bc_spec::eval::zero_num(), x]);
                    assert(r_num(t[0], bc_spec::eval::zero_num()));
                    assert forall|i: int| 0 <= i < t.len() implies #[trigger] r_num(t[i], ss[i]) by {}
                }
                lemma_r_vars_update(m, self.variables@, st.vars, nm_name, 1u8, x);
            }
        }
    }

    /// Pushes `frame` for array `name` (the specification's `arr_update` with op 1).
    pub(crate) fn push_arr_ref(&mut self, name: String, frame: BTreeMap<usize, BCNum>, Ghost(st): Ghost<SpecState>, Ghost(sf): Ghost<SpecFrame>)
        requires
            old(self).inv(),
            frame_ok(frame@),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_frame(frame@, sf)) ==> r_state(*final(self),
                bc_spec::eval::with_arrays(st, bc_spec::eval::arr_update(st.arrays, text_view(name), 1u8, sf, Seq::empty()))),
    {
        let ghost m = self.arrays@;
        let ghost nm_name = name;
        let ghost gf = frame;
        let ghost hyp = r_state(*self, st) && r_frame(frame@, sf);
        self.arr_push(name, frame);
        proof {
            if hyp {
                let found = arr_lookup(st.arrays, text_view(nm_name));
                let t = self.arrays@[nm_name]@;
                let ss = upd_frames(found, 1u8, sf)->Some_0;
                if m.contains_key(nm_name) {
                    let s = found->Some_0;
                    assert(r_frames(m[nm_name]@, s));
                    assert(ss == s.push(sf));
                    assert forall|i: int| 0 <= i < t.len() implies #[trigger] r_frame(t[i]@, ss[i]) by {
                        if i < s.len() {
                            assert(t[i] == m[nm_name]@[i]);
                        }
                    }
                } else {
                    lemma_arr_absent(m, st.arrays, nm_name);
                    assert(ss =~= seq![bc_spec::eval::empty_frame(), sf]);
                    assert(r_frame(Map::<usize, BCNum>::empty(), bc_spec::eval::empty_frame()));
                    assert forall|i: int| 0 <= i < t.len() implies #[trigger] r_frame(t[i]@, ss[i]) by {}
                }
                lemma_r_arrays_update(m, self.arrays@, st.arrays, nm_name, 1u8, sf);
            }
        }
    }

    /// Pops the top frame of variable `name` (the specification's `var_update` with op 2).
    #[allow(clippy::ptr_arg, reason = "the specification relates the String to the name")]
    pub(crate) fn pop_var_ref(&mut self, name: &String, Ghost(st): Ghost<SpecState>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r_state(*old(self), st) ==> r_state(*final(self),
                bc_spec::eval::with_vars(st, bc_spec::eval::var_update(st.vars, text_view(*name), 2u8, bc_spec::eval::zero_num(), Seq::empty()))),
    {
        let ghost m = self.variables@;
        let ghost hyp = r_state(*self, st);
        self.var_pop(name);
        proof {
            if hyp {
                let found = var_lookup(st.vars, text_view(*name));
                if m.contains_key(*name) {
                    let s = found->Some_0;
                    let t = self.variables@[*name]@;
                    let ss = upd_stack(found, 2u8, bc_spec::eval::zero_num())->Some_0;
                    assert(r_stack(m[*name]@, s));
                    assert forall|i: int| 0 <= i < t.len() implies #[trigger] r_num(t[i], ss[i]) by {
                        assert(t[i] == m[*name]@[i]);
                    }
                } else {
                    lemma_var_absent(m, st.vars, *name);
                }
                lemma_r_vars_update(m, self.variables@, st.vars, *name, 2u8, bc_spec::eval::zero_num());
            }
        }
    }

    /// Pops the top frame of array `name` (the specification's `arr_update` with op 2).
    #[allow(clippy::ptr_arg, reason = "the specification relates the String to the name")]
    pub(crate) fn pop_arr_ref(&mut self, name: &String, Ghost(st): Ghost<SpecState>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r_state(*old(self), st) ==> r_state(*final(self),
                bc_spec::eval::with_arrays(st, bc_spec::eval::arr_update(st.arrays, text_view(*name), 2u8, bc_spec::eval::empty_frame(), Seq::empty()))),
    {
        let ghost m = self.arrays@;
        let ghost hyp = r_state(*self, st);
        self.arr_pop(name);
        proof {
            if hyp {
                let found = arr_lookup(st.arrays, text_view(*name));
                if m.contains_key(*name) {
                    let s = found->Some_0;
                    let t = self.arrays@[*name]@;
                    let ss = upd_frames(found, 2u8, bc_spec::eval::empty_frame())->Some_0;
                    assert(r_frames(m[*name]@, s));
                    assert forall|i: int| 0 <= i < t.len() implies #[trigger] r_frame(t[i]@, ss[i]) by {
                        assert(t[i] == m[*name]@[i]);
                    }
                } else {
                    lemma_arr_absent(m, st.arrays, *name);
                }
                lemma_r_arrays_update(m, self.arrays@, st.arrays, *name, 2u8, bc_spec::eval::empty_frame());
            }
        }
    }

    /// A copy of the current frame of array `name` (empty if it has none), for an array
    /// argument (the specification's `arr_top`).
    #[allow(clippy::ptr_arg, reason = "the specification relates the String to the name")]
    pub(crate) fn arr_frame_clone(&self, name: &String, Ghost(st): Ghost<SpecState>) -> (r: BTreeMap<usize, BCNum>)
        requires
            self.inv(),
        ensures
            frame_ok(r@),
            r_state(*self, st) ==> r_frame(r@, arr_top(st.arrays, text_view(*name))),
    {
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            lemma_arr_top(st.arrays, text_view(*name));
            assert(r_frame(Map::<usize, BCNum>::empty(), bc_spec::eval::empty_frame()));
        }
        match self.arrays.get(name) {
            Some(stack) => {
                if !stack.is_empty() {
                    let r = stack[stack.len() - 1].clone();
                    proof {
                        assert(frames_ok(self.arrays@[*name]@));
                        assert(frame_ok(stack@[stack.len() - 1]@));
                        if r_state(*self, st) {
                            let ss = arr_lookup(st.arrays, text_view(*name))->Some_0;
                            assert(r_frames(stack@, ss));
                            assert(r_frame(stack@[stack.len() - 1]@, ss[ss.len() - 1]));
                        }
                    }
                    r
                } else {
                    proof {
                        if r_state(*self, st) {
                            assert(r_frames(stack@, arr_lookup(st.arrays, text_view(*name))->Some_0));
                        }
                    }
                    BTreeMap::new()
                }
            },
            None => {
                proof {
                    if r_state(*self, st) {
                        lemma_arr_absent(self.arrays@, st.arrays, *name);
                    }
                }
                BTreeMap::new()
            },
        }
    }

    /// The arguments of a call (the specification's `ev_args`), evaluated in order before any
    /// frame is pushed: a copy of the current frame for an array parameter, the value
    /// otherwise.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(30)]
    #[allow(clippy::ptr_arg, reason = "the specification relates the lists to the call")]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn ev_args_ref(&mut self, code: &Rc<Code>, params: &Vec<Param>, args: &Vec<PArg>, Ghost(nodes): Ghost<SpecNodes>, Ghost(sargs): Ghost<SpecArgs>, Ghost(sparams): Ghost<SpecParams>, Ghost(st): Ghost<SpecState>) -> (r: Result<Vec<(String, ArgValue)>, BcError>)
        requires
            old(self).inv(),
            params.len() == args.len(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> args_ok(r->Ok_0@),
            (r_state(*old(self), st) && r_rc(*code, nodes) && r_args(args@, sargs) && r_params(params@, sparams)) ==> forall|f: u64|
                done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r)
                    ==> r_args_result(r, *final(self), bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes) && r_args(args@, sargs) && r_params(params@, sparams);
        let ghost fin = exists|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r);
        let mut vals: Vec<(String, ArgValue)> = Vec::new();
        let ghost mut si = st;
        let ghost mut acc: Seq<bc_spec::eval::ArgVal> = Seq::empty();
        let mut i: usize = 0;
        proof {
            if hyp {
                assert(sargs.skip(0) =~= sargs);
                assert(sparams.skip(0) =~= sparams);
            }
        }
        while i < args.len()
            invariant
                self.inv(),
                self.eval_depth == d,
                d == old(self).eval_depth,
                i <= args.len(),
                params.len() == args.len(),
                vals@.len() == i,
                args_ok(vals@),
                hyp == (r_state(*old(self), st) && r_rc(*code, nodes) && r_args(args@, sargs) && r_params(params@, sparams)),
                fin == exists|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r),
                hyp ==> sargs.len() == args.len() && sparams.len() == args.len(),
                hyp && fin ==> r_state(*self, si) && r_argvals(vals@, acc),
                hyp ==> forall|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r) ==> f as int >= i
                    && bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f)
                        == bc_spec::eval::ev_args(nodes, sargs.skip(i as int), sparams.skip(i as int), si, acc, (f - i) as u64),
            decreases args.len() - i,
        {
            let ghost e0 = *self;
            let ghost sa = sargs[i as int];
            let ghost sp = sparams[i as int];
            proof {
                if hyp {
                    lemma_r_args_index(args@, sargs, i as int);
                    assert(r_param(params@[i as int], sp));
                    assert(sargs.skip(i as int)[0] == sa);
                    assert(sparams.skip(i as int)[0] == sp);
                    assert(sargs.skip(i as int).drop_first() =~= sargs.skip(i as int + 1));
                    assert(sparams.skip(i as int).drop_first() =~= sparams.skip(i as int + 1));
                }
            }
            let param = &params[i];
            match &args[i] {
                PArg::Array(arg_name) => {
                    if !param.is_array {
                        let r = Err(BcError::Runtime { kind: RuntimeError::ParameterTypeMismatch(param.name.clone()), func: None });
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r)
                                    implies r_args_result(r, *self, bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f), d) by {
                                    assert(r_state(*self, si));
                                    assert(with_depth(si, d as u64) == si);
                                }
                            }
                        }
                        return r;
                    }
                    proof {
                        if hyp {
                            assert(r_arg(PArg::Array(*arg_name), sa));
                            assert(sa.is_array && sa.name == text_view(*arg_name));
                            assert(sp.name == text_view(param.name));
                        }
                    }
                    let frame = self.arr_frame_clone(arg_name, Ghost(si));
                    let ghost gf = frame;
                    vals.push((param.name.clone(), ArgValue::Array(frame)));
                    proof {
                        if hyp {
                            let v = bc_spec::eval::ArgVal { is_array: true, name: sp.name, val: bc_spec::eval::zero_num(), frame: arr_top(si.arrays, sa.name) };
                            assert forall|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r) implies f as int >= i + 1
                                && bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f)
                                    == bc_spec::eval::ev_args(nodes, sargs.skip(i as int + 1), sparams.skip(i as int + 1), si, acc.push(v), (f - i - 1) as u64) by {
                            }
                            if fin {
                                assert(r_argval(vals@[i as int], v));
                                assert forall|j: int| 0 <= j < vals@.len() implies #[trigger] r_argval(vals@[j], acc.push(v)[j]) by {}
                            }
                            acc = acc.push(v);
                        }
                    }
                },
                PArg::Expr(e) => {
                    if param.is_array {
                        let r = Err(BcError::Runtime { kind: RuntimeError::ParameterTypeMismatch(param.name.clone()), func: None });
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r)
                                    implies r_args_result(r, *self, bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f), d) by {
                                    assert(r_state(*self, si));
                                    assert(with_depth(si, d as u64) == si);
                                }
                            }
                        }
                        return r;
                    }
                    proof {
                        if hyp {
                            assert(r_arg(PArg::Expr(*e), sa));
                            assert(!sa.is_array && sa.expr == *e);
                            assert(sp.name == text_view(param.name));
                        }
                    }
                    let v = match self.eval_ref(code, *e, Ghost(nodes), Ghost(si)) {
                        Ok(v) => v,
                        Err(err) => {
                            proof {
                                if hyp {
                                    assert forall|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r)
                                        implies r_args_result(Err(err), *self, bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f), d) by {
                                        assert(r_state(e0, si));
                                        assert(done(ev(nodes, sa.expr, si, (f - i - 1) as u64)));
                                    }
                                }
                            }
                            return Err(err);
                        },
                    };
                    let ghost fv = choose|f: u64| done(#[trigger] ev(nodes, sa.expr, si, f));
                    let ghost xv = ev(nodes, sa.expr, si, fv);
                    proof {
                        if hyp {
                            assert forall|f: u64| done(#[trigger] ev(nodes, sa.expr, si, f)) implies ev(nodes, sa.expr, si, f) == xv by {
                                if fv <= f { lemma_ev_mono(nodes, sa.expr, si, fv, f); } else { lemma_ev_mono(nodes, sa.expr, si, f, fv); }
                            }
                        }
                    }
                    let ghost gv = v;
                    vals.push((param.name.clone(), ArgValue::Scalar(v)));
                    proof {
                        if hyp {
                            let av = bc_spec::eval::ArgVal { is_array: false, name: sp.name, val: xv.val, frame: bc_spec::eval::empty_frame() };
                            assert forall|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r) implies f as int >= i + 1
                                && bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f)
                                    == bc_spec::eval::ev_args(nodes, sargs.skip(i as int + 1), sparams.skip(i as int + 1), xv.st, acc.push(av), (f - i - 1) as u64) by {
                                assert(done(ev(nodes, sa.expr, si, (f - i - 1) as u64)));
                            }
                            if fin {
                                let ff = choose|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r);
                                assert(done(ev(nodes, sa.expr, si, (ff - i - 1) as u64)));
                                assert(r_state(e0, si));
                                assert(r_result(Ok(gv), *self, xv, d));
                                assert(r_argval(vals@[i as int], av));
                                assert forall|j: int| 0 <= j < vals@.len() implies #[trigger] r_argval(vals@[j], acc.push(av)[j]) by {}
                            }
                            acc = acc.push(av);
                            si = xv.st;
                        }
                    }
                },
            }
            i += 1;
        }
        proof {
            if hyp {
                assert(sargs.skip(i as int) =~= Seq::<bc_spec::parser::Arg>::empty());
                assert forall|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f).r)
                    implies r_args_result(Ok(vals), *self, bc_spec::eval::ev_args(nodes, sargs, sparams, st, Seq::empty(), f), d) by {
                }
            }
        }
        Ok(vals)
    }

    /// Pushes the parameter frames of a call, in order (the specification's `push_args`).
    pub(crate) fn push_args_ref(&mut self, vals: Vec<(String, ArgValue)>, Ghost(svals): Ghost<SpecArgVals>, Ghost(st): Ghost<SpecState>)
        requires
            old(self).inv(),
            args_ok(vals@),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_argvals(vals@, svals)) ==> r_state(*final(self), bc_spec::eval::push_args(st, svals)),
    {
        let ghost hyp = r_state(*self, st) && r_argvals(vals@, svals);
        let mut vals = vals;
        let ghost mut sj = st;
        let ghost mut rest = svals;
        let count = vals.len();
        let mut j: usize = 0;
        while j < count
            invariant
                self.inv(),
                self.eval_depth == old(self).eval_depth,
                j <= count,
                vals@.len() == count - j,
                args_ok(vals@),
                hyp ==> r_state(*self, sj) && r_argvals(vals@, rest)
                    && bc_spec::eval::push_args(st, svals) == bc_spec::eval::push_args(sj, rest),
            decreases count - j,
        {
            let ghost before = vals@;
            let (pname, v) = vals.remove(0);
            let ghost s0 = rest[0];
            proof {
                assert(vals@ =~= before.drop_first());
                assert forall|k: int| 0 <= k < vals@.len() implies match (#[trigger] vals@[k]).1 {
                    ArgValue::Array(f) => frame_ok(f@),
                    ArgValue::Scalar(x) => x.scale <= BC_SCALE_MAX,
                } by {
                    assert(vals@[k] == before[k + 1]);
                }
                assert(match before[0].1 {
                    ArgValue::Array(f) => frame_ok(f@),
                    ArgValue::Scalar(x) => x.scale <= BC_SCALE_MAX,
                });
                if hyp {
                    assert(r_argval(before[0], s0));
                }
            }
            match v {
                ArgValue::Array(frame) => self.push_arr_ref(pname, frame, Ghost(sj), Ghost(s0.frame)),
                ArgValue::Scalar(x) => self.push_var_ref(pname, x, Ghost(sj), Ghost(s0.val)),
            }
            proof {
                if hyp {
                    sj = if s0.is_array {
                        bc_spec::eval::with_arrays(sj, bc_spec::eval::arr_update(sj.arrays, s0.name, 1u8, s0.frame, Seq::empty()))
                    } else {
                        bc_spec::eval::with_vars(sj, bc_spec::eval::var_update(sj.vars, s0.name, 1u8, s0.val, Seq::empty()))
                    };
                    let rest0 = rest;
                    rest = rest.drop_first();
                    assert forall|k: int| 0 <= k < vals@.len() implies #[trigger] r_argval(vals@[k], rest[k]) by {
                        assert(vals@[k] == before[k + 1]);
                        assert(rest[k] == rest0[k + 1]);
                        assert(r_argval(before[k + 1], rest0[k + 1]));
                    }
                }
            }
            j += 1;
        }
    }

    /// Pushes the `auto` frames of a call, in order: 0, or an empty array (the
    /// specification's `push_autos`).
    #[allow(clippy::ptr_arg, reason = "the specification relates the list to the function")]
    pub(crate) fn push_autos_ref(&mut self, autos: &Vec<Param>, Ghost(sautos): Ghost<SpecParams>, Ghost(st): Ghost<SpecState>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_params(autos@, sautos)) ==> r_state(*final(self), bc_spec::eval::push_autos(st, sautos)),
    {
        let ghost hyp = r_state(*self, st) && r_params(autos@, sautos);
        let ghost mut sj = st;
        let mut j: usize = 0;
        proof {
            assert(sautos.skip(0) =~= sautos);
        }
        while j < autos.len()
            invariant
                self.inv(),
                self.eval_depth == old(self).eval_depth,
                j <= autos.len(),
                hyp == (r_state(*old(self), st) && r_params(autos@, sautos)),
                hyp ==> sautos.len() == autos.len() && r_state(*self, sj)
                    && bc_spec::eval::push_autos(st, sautos) == bc_spec::eval::push_autos(sj, sautos.skip(j as int)),
            decreases autos.len() - j,
        {
            let a = &autos[j];
            let ghost q = sautos[j as int];
            proof {
                if hyp {
                    assert(r_param(autos@[j as int], q));
                    assert(sautos.skip(j as int)[0] == q);
                    assert(sautos.skip(j as int).drop_first() =~= sautos.skip(j as int + 1));
                    assert(r_frame(Map::<usize, BCNum>::empty(), bc_spec::eval::empty_frame()));
                }
            }
            if a.is_array {
                self.push_arr_ref(a.name.clone(), BTreeMap::new(), Ghost(sj), Ghost(bc_spec::eval::empty_frame()));
            } else {
                self.push_var_ref(a.name.clone(), BCNum::zero(), Ghost(sj), Ghost(bc_spec::eval::zero_num()));
            }
            proof {
                if hyp {
                    sj = if q.is_array {
                        bc_spec::eval::with_arrays(sj, bc_spec::eval::arr_update(sj.arrays, q.name, 1u8, bc_spec::eval::empty_frame(), Seq::empty()))
                    } else {
                        bc_spec::eval::with_vars(sj, bc_spec::eval::var_update(sj.vars, q.name, 1u8, bc_spec::eval::zero_num(), Seq::empty()))
                    };
                }
            }
            j += 1;
        }
        proof {
            if hyp {
                assert(sautos.skip(j as int) =~= Seq::<bc_spec::parser::Param>::empty());
            }
        }
    }

    /// Pops the frames of `ps`, last first (the specification's `pop_frames`).
    #[allow(clippy::ptr_arg, reason = "the specification relates the list to the function")]
    pub(crate) fn pop_params_ref(&mut self, ps: &Vec<Param>, Ghost(sps): Ghost<SpecParams>, Ghost(st): Ghost<SpecState>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_params(ps@, sps)) ==> r_state(*final(self), bc_spec::eval::pop_frames(st, sps)),
    {
        let ghost hyp = r_state(*self, st) && r_params(ps@, sps);
        let ghost mut sk = st;
        let mut i = ps.len();
        proof {
            if hyp {
                assert(sps.take(sps.len() as int) =~= sps);
            }
        }
        while i > 0
            invariant
                self.inv(),
                self.eval_depth == old(self).eval_depth,
                i <= ps.len(),
                hyp == (r_state(*old(self), st) && r_params(ps@, sps)),
                hyp ==> sps.len() == ps.len() && r_state(*self, sk)
                    && bc_spec::eval::pop_frames(st, sps) == bc_spec::eval::pop_frames(sk, sps.take(i as int)),
            decreases i,
        {
            i -= 1;
            let p = &ps[i];
            let ghost q = sps[i as int];
            proof {
                if hyp {
                    assert(r_param(ps@[i as int], q));
                    assert(sps.take(i as int + 1).drop_last() =~= sps.take(i as int));
                    assert(sps.take(i as int + 1)[i as int] == q);
                }
            }
            if p.is_array {
                self.pop_arr_ref(&p.name, Ghost(sk));
            } else {
                self.pop_var_ref(&p.name, Ghost(sk));
            }
            proof {
                if hyp {
                    sk = if q.is_array {
                        bc_spec::eval::with_arrays(sk, bc_spec::eval::arr_update(sk.arrays, q.name, 2u8, bc_spec::eval::empty_frame(), Seq::empty()))
                    } else {
                        bc_spec::eval::with_vars(sk, bc_spec::eval::var_update(sk.vars, q.name, 2u8, bc_spec::eval::zero_num(), Seq::empty()))
                    };
                }
            }
        }
        proof {
            if hyp {
                assert(sps.take(0) =~= Seq::<bc_spec::parser::Param>::empty());
            }
        }
    }

    /// Leaves function `func` (the specification's `leave_call`): pops the call, restores the
    /// caller's return state and invocation `ibase`, and pops the `auto` frames and then the
    /// parameter frames, each list last first. Returns the function's return value.
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn leave_call(&mut self, autos: &Vec<Param>, params: &Vec<Param>, saved_flag: bool, saved_inv: Option<usize>, saved_val: BCNum, Ghost(g): Ghost<SpecFunc>, Ghost(s): Ghost<SpecSaved>, Ghost(st): Ghost<SpecState>) -> (ret: BCNum)
        requires
            old(self).inv(),
            saved_val.scale <= BC_SCALE_MAX,
            match saved_inv {
                Some(b) => 2 <= b <= IBASE_MAX,
                None => true,
            },
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            ret == old(self).return_value,
            (r_state(*old(self), st) && r_params(params@, g.params) && r_params(autos@, g.autos)
                && saved_flag == s.ret && r_num(saved_val, s.ret_val)
                && match saved_inv {
                    Some(b) => s.has_inv && b == s.inv_ibase,
                    None => !s.has_inv,
                }) ==> r_state(*final(self), bc_spec::eval::leave_call(st, g, s)),
    {
        let ghost hyp = r_state(*self, st) && r_params(params@, g.params) && r_params(autos@, g.autos)
            && saved_flag == s.ret && r_num(saved_val, s.ret_val)
            && match saved_inv {
                Some(b) => s.has_inv && b == s.inv_ibase,
                None => !s.has_inv,
            };
        let ghost calls0 = self.call_stack@;
        self.call_stack.pop();
        self.return_flag = saved_flag;
        let mut ret = saved_val;
        core::mem::swap(&mut self.return_value, &mut ret);
        self.invocation_ibase = saved_inv;
        let ghost st1 = {
            let calls = if st.calls.len() > 0 { st.calls.drop_last() } else { st.calls };
            let a = bc_spec::eval::with_call(st, calls, s.has_inv, s.inv_ibase);
            bc_spec::eval::with_flags(a, a.brk, s.ret, s.ret_val)
        };
        proof {
            if hyp {
                if calls0.len() > 0 {
                    assert(self.call_stack@ =~= calls0.drop_last());
                    assert forall|i: int| 0 <= i < self.call_stack@.len() implies #[trigger] text_view(self.call_stack@[i]) == st1.calls[i] by {
                        assert(self.call_stack@[i] == calls0[i]);
                    }
                }
                assert(r_state(*self, st1));
            }
        }
        self.pop_params_ref(autos, Ghost(g.autos), Ghost(st1));
        self.pop_params_ref(params, Ghost(g.params), Ghost(bc_spec::eval::pop_frames(st1, g.autos)));
        ret
    }

    /// A function body (the specification's `exec_body`): its statements in order, stopping
    /// after `return`.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "the specification relates the list to the function")]
    pub(crate) fn run_body(&mut self, code: &Rc<Code>, body: &Vec<usize>, Ghost(nodes): Ghost<SpecNodes>, Ghost(ns): Ghost<SpecIndices>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_rc(*code, nodes) && body@ == ns) ==> forall|f: u64|
                done(#[trigger] bc_spec::eval::exec_body(nodes, ns, st, f)) ==> r_unit(r, *final(self), bc_spec::eval::exec_body(nodes, ns, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes) && body@ == ns;
        let ghost fin = exists|f: u64| done(#[trigger] bc_spec::eval::exec_body(nodes, ns, st, f));
        let ghost mut si = st;
        let mut i: usize = 0;
        proof {
            if hyp {
                assert(ns.skip(0) =~= ns);
            }
        }
        while i < body.len()
            invariant
                self.inv(),
                self.eval_depth == d,
                d == old(self).eval_depth,
                i <= body.len(),
                hyp == (r_state(*old(self), st) && r_rc(*code, nodes) && body@ == ns),
                fin == exists|f: u64| done(#[trigger] bc_spec::eval::exec_body(nodes, ns, st, f)),
                hyp ==> ns.len() == body.len(),
                hyp && fin ==> r_state(*self, si),
                hyp ==> forall|f: u64| done(#[trigger] bc_spec::eval::exec_body(nodes, ns, st, f)) ==> f as int >= i
                    && bc_spec::eval::exec_body(nodes, ns, st, f) == bc_spec::eval::exec_body(nodes, ns.skip(i as int), si, (f - i) as u64),
            decreases body.len() - i,
        {
            let ghost ji = ns[i as int];
            let ghost e0 = *self;
            proof {
                if hyp {
                    assert(ns.skip(i as int)[0] == ji);
                    assert(ns.skip(i as int).drop_first() =~= ns.skip(i as int + 1));
                }
            }
            let ri = self.exec_ref(code, body[i], Ghost(nodes), Ghost(si));
            if let Err(err) = ri {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_body(nodes, ns, st, f))
                            implies r_unit(Err(err), *self, bc_spec::eval::exec_body(nodes, ns, st, f), d) by {
                            assert(r_state(e0, si));
                            assert(done(exec(nodes, ji, si, (f - i - 1) as u64)));
                        }
                    }
                }
                return Err(err);
            }
            let ghost fi = choose|f: u64| done(#[trigger] exec(nodes, ji, si, f));
            let ghost x = exec(nodes, ji, si, fi);
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec(nodes, ji, si, f)) implies exec(nodes, ji, si, f) == x by {
                        if fi <= f { lemma_exec_mono(nodes, ji, si, fi, f); } else { lemma_exec_mono(nodes, ji, si, f, fi); }
                    }
                }
            }
            if self.return_flag || self.quit_flag {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_body(nodes, ns, st, f))
                            implies r_unit(Ok(()), *self, bc_spec::eval::exec_body(nodes, ns, st, f), d) by {
                            assert(r_state(e0, si));
                            assert(done(exec(nodes, ji, si, (f - i - 1) as u64)));
                        }
                    }
                }
                return Ok(());
            }
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_body(nodes, ns, st, f)) implies f as int >= i + 1
                        && bc_spec::eval::exec_body(nodes, ns, st, f) == bc_spec::eval::exec_body(nodes, ns.skip(i as int + 1), x.st, (f - i - 1) as u64) by {
                        assert(r_state(e0, si));
                        assert(done(exec(nodes, ji, si, (f - i - 1) as u64)));
                    }
                    if fin {
                        let ff = choose|f: u64| done(#[trigger] bc_spec::eval::exec_body(nodes, ns, st, f));
                        assert(r_state(e0, si));
                        assert(done(exec(nodes, ji, si, (ff - i - 1) as u64)));
                        assert(r_state(*self, x.st));
                    }
                    si = x.st;
                }
            }
            i += 1;
        }
        proof {
            if hyp {
                assert(ns.skip(i as int) =~= Seq::<usize>::empty());
                assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_body(nodes, ns, st, f))
                    implies r_unit(Ok(()), *self, bc_spec::eval::exec_body(nodes, ns, st, f), d) by {
                }
            }
        }
        Ok(())
    }

    /// A call of a user function (the specification's `ev_call` and `run_call`). A name that is
    /// not defined goes to `-l`'s functions (`eval_math`) when the math library is enabled.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(50)]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    #[allow(clippy::ptr_arg, reason = "the specification relates the arguments to the call")]
    pub(crate) fn eval_call(&mut self, code: &Rc<Code>, Ghost(n): Ghost<usize>, name: &String, args: &Vec<PArg>, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Call(*name, *args),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_rc(*code, nodes)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes);
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let ghost sargs = if n < nodes.len() { match nodes[n as int] { Node::Call(_, a) => a, _ => Seq::empty() } } else { Seq::empty() };
        let ghost sname = text_view(*name);
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let func = match self.functions.get(name) {
            Some(fd) => fd.clone(),
            None => {
                if self.math_enabled {
                    return self.eval_math(code, name, args);
                }
                let r = Err(BcError::Runtime { kind: RuntimeError::UndefinedFunction(name.clone()), func: None });
                proof {
                    if hyp {
                        lemma_func_absent(self.functions@, st.funcs, *name);
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(r, *self, ev_node(nodes, n, st, f), d) by {
                            assert(with_depth(st, d as u64) == st);
                        }
                    }
                }
                return r;
            },
        };
        let ghost g = bc_spec::eval::find_func(st.funcs, sname)->Some_0;
        proof {
            if hyp {
                assert(self.functions@.contains_key(*name));
                assert(r_func(func, g));
                lemma_find_func_index(st.funcs, sname);
                assert(r_args(args@, sargs));
                assert(args@.len() == sargs.len());
            }
        }
        proof { if hyp { assert(r_node(func.code.nodes@[func.def as int], g.nodes[func.def as int])); } }
        if func.def >= func.code.nodes.len() {
            // A function is always the `Define` node of its unit (`r_func`).
            return Ok(BCNum::zero());
        }
        let (params, autos, body) = match &func.code.nodes[func.def] {
            PNode::Define(_, params, autos, body) => (params, autos, body),
            _ => {
                return Ok(BCNum::zero());
            },
        };
        if args.len() != params.len() {
            let r = Err(BcError::Runtime { kind: RuntimeError::ParameterMismatch, func: None });
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(r, *self, ev_node(nodes, n, st, f), d) by {
                        assert(with_depth(st, d as u64) == st);
                    }
                }
            }
            return r;
        }
        let vals = match self.ev_args_ref(code, params, args, Ghost(nodes), Ghost(sargs), Ghost(g.params), Ghost(st)) {
            Ok(vals) => vals,
            Err(err) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(err), *self, ev_node(nodes, n, st, f), d) by {
                            assert(done(bc_spec::eval::ev_args(nodes, sargs, g.params, st, Seq::empty(), (f - 2) as u64).r));
                        }
                    }
                }
                return Err(err);
            },
        };
        let ghost fa = choose|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, g.params, st, Seq::empty(), f).r);
        let ghost a = bc_spec::eval::ev_args(nodes, sargs, g.params, st, Seq::empty(), fa);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] bc_spec::eval::ev_args(nodes, sargs, g.params, st, Seq::empty(), f).r)
                    implies bc_spec::eval::ev_args(nodes, sargs, g.params, st, Seq::empty(), f) == a by {
                    if fa <= f {
                        bc_spec::fuel::lemma_ev_args_mono(nodes, sargs, g.params, st, Seq::empty(), fa, f);
                    } else {
                        bc_spec::fuel::lemma_ev_args_mono(nodes, sargs, g.params, st, Seq::empty(), f, fa);
                    }
                }
            }
        }
        let ghost e1 = *self;
        let ghost vals_g = vals;
        let r = self.run_call_ref(&func.code, autos, params, body, name, vals, Ghost(g), Ghost(a.vals), Ghost(a.r.st));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(r, *self, ev_node(nodes, n, st, f), d) by {
                    assert(done(bc_spec::eval::ev_args(nodes, sargs, g.params, st, Seq::empty(), (f - 2) as u64).r));
                    assert(r_args_result(Ok(vals_g), e1, a, d));
                    assert(r_func(func, g) && g.name == sname);
                    assert(done(bc_spec::eval::run_call(g, a.vals, a.r.st, (f - 2) as u64)));
                }
            }
        }
        r
    }

    /// Enters function `func` with the evaluated arguments, runs its body and leaves it (the
    /// specification's `run_call`).
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(50)]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    #[allow(clippy::ptr_arg, reason = "the specification relates the String to the call")]
    pub(crate) fn run_call_ref(&mut self, code: &Rc<Code>, autos: &Vec<Param>, params: &Vec<Param>, body: &Vec<usize>, name: &String, vals: Vec<(String, ArgValue)>, Ghost(g): Ghost<SpecFunc>, Ghost(svals): Ghost<SpecArgVals>, Ghost(sa): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            args_ok(vals@),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), sa) && r_rc(*code, g.nodes) && r_params(params@, g.params) && r_params(autos@, g.autos) && body@ == g.body && g.name == text_view(*name) && r_argvals(vals@, svals)) ==> forall|f: u64|
                done(#[trigger] bc_spec::eval::run_call(g, svals, sa, f)) ==> r_result(r, *final(self), bc_spec::eval::run_call(g, svals, sa, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, sa) && r_rc(*code, g.nodes) && r_params(params@, g.params) && r_params(autos@, g.autos) && body@ == g.body && g.name == text_view(*name) && r_argvals(vals@, svals);
        let ghost s = bc_spec::eval::Saved { ret: sa.ret, ret_val: sa.ret_val, has_inv: sa.has_inv, inv_ibase: sa.inv_ibase };
        self.push_args_ref(vals, Ghost(svals), Ghost(sa));
        let ghost sp = bc_spec::eval::push_args(sa, svals);
        self.push_autos_ref(autos, Ghost(g.autos), Ghost(sp));
        let ghost s1 = bc_spec::eval::push_autos(sp, g.autos);
        let saved_flag = self.return_flag;
        let saved_inv = self.invocation_ibase;
        let mut saved_val = BCNum::zero();
        core::mem::swap(&mut self.return_value, &mut saved_val);
        self.return_flag = false;
        self.invocation_ibase = Some(self.ibase);
        let ghost calls1 = self.call_stack@;
        self.call_stack.push(name.clone());
        let ghost s2 = bc_spec::eval::with_flags(s1, s1.brk, false, bc_spec::eval::zero_num());
        let ghost s3 = bc_spec::eval::with_call(s2, s2.calls.push(g.name), true, s2.ibase);
        proof {
            if hyp {
                lemma_push_args_keeps(sa, svals);
                lemma_push_autos_keeps(sp, g.autos);
                assert(r_calls(self.call_stack@, s3.calls)) by {
                    assert forall|i: int| 0 <= i < self.call_stack@.len() implies #[trigger] text_view(self.call_stack@[i]) == s3.calls[i] by {
                        if i < calls1.len() {
                            assert(self.call_stack@[i] == calls1[i]);
                        }
                    }
                }
                assert(r_state(*self, s3));
            }
        }
        let body_r = self.run_body(code, body, Ghost(g.nodes), Ghost(g.body), Ghost(s3));
        let ghost fb = choose|f: u64| done(#[trigger] bc_spec::eval::exec_body(g.nodes, g.body, s3, f));
        let ghost xb = bc_spec::eval::exec_body(g.nodes, g.body, s3, fb);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_body(g.nodes, g.body, s3, f))
                    implies bc_spec::eval::exec_body(g.nodes, g.body, s3, f) == xb by {
                    if fb <= f {
                        bc_spec::fuel::lemma_exec_body_mono(g.nodes, g.body, s3, fb, f);
                    } else {
                        bc_spec::fuel::lemma_exec_body_mono(g.nodes, g.body, s3, f, fb);
                    }
                }
            }
        }
        let ghost e3 = *self;
        let ghost sl = if body_r is Ok { xb.st } else { with_depth(xb.st, d as u64) };
        let ret_val = self.leave_call(autos, params, saved_flag, saved_inv, saved_val, Ghost(g), Ghost(s), Ghost(sl));
        let r = match body_r {
            Ok(()) => Ok(ret_val),
            Err(e) => Err(e.in_function(name)),
        };
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] bc_spec::eval::run_call(g, svals, sa, f))
                    implies r_result(r, *self, bc_spec::eval::run_call(g, svals, sa, f), d) by {
                    assert(done(bc_spec::eval::exec_body(g.nodes, g.body, s3, (f - 1) as u64)));
                    assert(r_unit(body_r, e3, xb, d));
                    lemma_leave_call_depth(xb.st, g, s, d as u64);
                }
            }
        }
        r
    }
}

} // verus!
