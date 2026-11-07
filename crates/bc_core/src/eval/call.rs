// SPDX-License-Identifier: MIT

//! The scopes of a function call (the specification's `ev_call` and `run_call`): pushing the
//! arguments and `auto` locals, and `leave_call`, which pops them and restores the caller's
//! state. The call itself runs on the machine (`machine.rs`).

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

}

} // verus!
