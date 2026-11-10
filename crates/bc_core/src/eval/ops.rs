// SPDX-License-Identifier: MIT

//! The operations on values that the machine's frames (`machine.rs` and its submodules), the
//! fast path (`machine/quick.rs`) and the leaves (`leaf.rs`) use: arithmetic and `^` (`arith`), numeric
//! constants (`literal`), array subscripts (`array_index`), stores to `scale`, `ibase` and `obase` with
//! their clamp warnings (`store_register`), reading and writing an assignment target (`load`,
//! `store`), runtime warnings (`warn`), and whether an expression statement is an assignment
//! (`is_assignment`, through `is_asg`). The theorem of each relates it to the specification's
//! function named in parentheses.

use super::*;

verus! {

impl Evaluator {
    /// `l <op> r` at the current `scale` (the specification's `arith`), for the specification
    /// numbers `a`, `b` and state `st` that `l`, `r` and the evaluator correspond to. `^` goes
    /// through `power_ref`.
    pub(crate) fn arith_ref(&mut self, op: BinOp, l: &BCNum, r: &BCNum, Ghost(a): Ghost<SpecNum>, Ghost(b): Ghost<SpecNum>, Ghost(st): Ghost<SpecState>) -> (res: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            l.scale <= BC_SCALE_MAX,
            r.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            res is Ok ==> res->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_num(*l, a) && r_num(*r, b)) ==>
                r_result(res, *final(self), spec_arith(st, bin_code(op), a, b), old(self).eval_depth),
    {
        let ghost hyp = r_state(*self, st) && r_num(*l, a) && r_num(*r, b);
        proof {
            if hyp {
                assert(with_depth(st, self.eval_depth as u64) == st);
                lemma_is_zero_mag(b.mag);
                lemma_mag_bounds(b.mag);
            }
        }
        match op {
            BinOp::Add => {
                let v = l.add(r);
                proof { if hyp { lemma_num_add(a, b); } }
                Ok(v)
            },
            BinOp::Sub => {
                let v = l.sub(r);
                proof { if hyp { lemma_num_sub(a, b); } }
                Ok(v)
            },
            BinOp::Mul => {
                let v = l.mul(r, self.scale);
                proof { if hyp { lemma_num_mul(a, b, st.scale); } }
                Ok(v)
            },
            BinOp::Div => {
                let q = l.try_div(r, self.scale);
                proof { if hyp && mag_val(b.mag) > 0 { lemma_num_div(a, b, st.scale); } }
                match q {
                    Ok(v) => Ok(v),
                    Err(k) => Err(BcError::Runtime { kind: k, func: None }),
                }
            },
            BinOp::Mod => {
                let q = l.try_mod_op(r, self.scale);
                proof { if hyp && mag_val(b.mag) > 0 && st.scale + b.scale <= 1_000_000_000 { lemma_num_mod(a, b, st.scale); } }
                match q {
                    Ok(v) => Ok(v),
                    Err(k) => Err(BcError::Runtime { kind: k, func: None }),
                }
            },
            BinOp::Pow => self.power_ref(l, r, Ghost(a), Ghost(b), Ghost(st)),
        }
    }


    /// Converts the subscript `idx` of array `name` to an index, truncating it to an integer
    /// (the specification's `array_index`). Negative subscripts and subscripts of at least
    /// `BC_DIM_MAX` are runtime errors.
    #[allow(clippy::cast_possible_truncation, reason = "the index is below BC_DIM_MAX = 2^24")]
    #[allow(clippy::ptr_arg, reason = "the specification relates the error to the String")]
    pub(crate) fn array_index_ref(name: &String, idx: &BCNum) -> (r: Result<usize, BcError>)
        requires
            idx.scale <= BC_SCALE_MAX,
        ensures
            forall|x: SpecNum| #[trigger] r_num(*idx, x) ==> match r {
                Ok(i) => array_index(x).0 && array_index(x).1 == i,
                Err(e) => !array_index(x).0 && e == BcError::Runtime {
                    kind: RuntimeError::ArraySubscriptOutOfBounds(*name),
                    func: None,
                },
            },
    {
        proof {
            lemma_pow10_pos(idx.scale as nat);
        }
        let index = big_tdiv(&idx.coeff, &pow10_within(idx.scale));
        let below = matches!(big_cmp(&index, &big_from_usize(BC_DIM_MAX)), Ordering::Less);
        let r = if big_is_negative(&idx.coeff) || !below {
            Err(BcError::Runtime { kind: RuntimeError::ArraySubscriptOutOfBounds(name.clone()), func: None })
        } else {
            Ok(big_to_u64_small(&index) as usize)
        };
        proof {
            assert forall|x: SpecNum| #[trigger] r_num(*idx, x) implies match r {
                Ok(i) => array_index(x).0 && array_index(x).1 == i,
                Err(e) => !array_index(x).0 && e == BcError::Runtime {
                    kind: RuntimeError::ArraySubscriptOutOfBounds(*name),
                    func: None,
                },
            } by {
                lemma_array_index_value(x);
                lemma_mag_bounds(x.mag);
            }
        }
        r
    }

    /// Writes `Runtime warning (func=<current function>): <msg>` to the diagnostic stream (the
    /// specification's `warn`).
    pub(crate) fn warn_ref(&mut self, msg: &[u8], Ghost(st): Ghost<SpecState>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            same_but_err(*old(self), *final(self)),
            r_state(*old(self), st) ==> r_state(*final(self), bc_spec::eval::warn(st, msg@)),
    {
        let ghost e0 = *self;
        let head: [u8; 22] = [82, 117, 110, 116, 105, 109, 101, 32, 119, 97, 114, 110, 105, 110, 103, 32, 40, 102, 117, 110, 99, 61];
        self.stderr_writer.write_bytes(&head);
        let n = self.call_stack.len();
        let main: [u8; 6] = [40, 109, 97, 105, 110, 41];
        if n > 0 {
            #[allow(
                clippy::redundant_as_str,
                reason = "Verus specifies str::as_bytes and String::as_str, not String::as_bytes"
            )]
            self.stderr_writer.write_bytes(self.call_stack[n - 1].as_str().as_bytes());
        } else {
            self.stderr_writer.write_bytes(&main);
        }
        let sep: [u8; 3] = [41, 58, 32];
        self.stderr_writer.write_bytes(&sep);
        self.stderr_writer.write_bytes(msg);
        let nl: [u8; 1] = [10];
        self.stderr_writer.write_bytes(&nl);
        proof {
            if r_state(e0, st) {
                let w = bc_spec::eval::warn(st, msg@);
                assert(head@ == seq![82u8, 117, 110, 116, 105, 109, 101, 32, 119, 97, 114, 110, 105, 110, 103, 32, 40, 102, 117, 110, 99, 61]);
                assert(main@ == seq![40u8, 109, 97, 105, 110, 41]);
                assert(sep@ == seq![41u8, 58, 32]);
                assert(nl@ == seq![10u8]);
                if n > 0 {
                    assert(text_view(e0.call_stack@[n - 1]) == st.calls[st.calls.len() - 1]);
                }
                assert(err_log(&self.stderr_writer) =~= w.err);
            }
        }
    }

    /// `l ^ r` at the current `scale` (the specification's `arith` for `^`): a warning when the
    /// exponent has a fraction, then the verified `try_pow`.
    pub(crate) fn power_ref(&mut self, l: &BCNum, r: &BCNum, Ghost(a): Ghost<SpecNum>, Ghost(b): Ghost<SpecNum>, Ghost(st): Ghost<SpecState>) -> (res: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            l.scale <= BC_SCALE_MAX,
            r.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            res is Ok ==> res->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_num(*l, a) && r_num(*r, b)) ==>
                r_result(res, *final(self), spec_arith(st, 5u8, a, b), old(self).eval_depth),
    {
        let ghost e0 = *self;
        let ghost st2 = if b.scale > 0 { bc_spec::eval::warn(st, seq![110u8, 111, 110, 45, 122, 101, 114, 111, 32, 115, 99, 97, 108, 101, 32, 105, 110, 32, 101, 120, 112, 111, 110, 101, 110, 116]) } else { st };
        if r.scale > 0 {
            let msg: [u8; 26] = [110, 111, 110, 45, 122, 101, 114, 111, 32, 115, 99, 97, 108, 101, 32, 105, 110, 32, 101, 120, 112, 111, 110, 101, 110, 116];
            proof {
                assert(msg@ == seq![110u8, 111, 110, 45, 122, 101, 114, 111, 32, 115, 99, 97, 108, 101, 32, 105, 110, 32, 101, 120, 112, 111, 110, 101, 110, 116]);
            }
            self.warn_ref(&msg, Ghost(st));
        }
        let q = l.try_pow(r, self.scale);
        let res = match q {
            Ok(v) => Ok(v),
            Err(k) => Err(BcError::Runtime { kind: k, func: None }),
        };
        proof {
            if r_state(e0, st) && r_num(*l, a) && r_num(*r, b) {
                assert(r_state(*self, st2));
                assert(with_depth(st2, self.eval_depth as u64) == st2);
                lemma_num_pow(a, b, st2.scale);
            }
        }
        res
    }

    /// A numeric constant in the `ibase` of the current invocation (the specification's
    /// `literal`): its text split into digit values by `literal_digit_values`, and converted by
    /// the verified `BCNum::from_digit_values`.
    #[allow(clippy::ptr_arg, reason = "the specification relates the constant's String")]
    pub(crate) fn literal_ref(&self, t: &String, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            self.inv(),
        ensures
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            r_state(*self, st) ==> r_result(r, *self, bc_spec::eval::literal(st, text_view(*t)), self.eval_depth),
    {
        let ib = match self.invocation_ibase {
            Some(b) => b,
            None => self.ibase,
        };
        let (ds, fs) = literal_digit_values(t.as_str().as_bytes());
        if fs.len() > BC_SCALE_MAX {
            let r = Err(BcError::Runtime { kind: RuntimeError::ScaleTooLarge, func: None });
            proof {
                if r_state(*self, st) {
                    assert(with_depth(st, self.eval_depth as u64) == st);
                }
            }
            return r;
        }
        let v = BCNum::from_digit_values(&ds, &fs, ib);
        proof {
            if r_state(*self, st) {
                lemma_num_from_digits(ds@, fs@, ib as u8);
                assert(r_num(v, num_from_digits(ds@, fs@, ib as u8)));
            }
        }
        Ok(v)
    }

    /// The integer part of `|val|`, as `max + 1` if it exceeds `max`, and whether `val` is
    /// negative: what the specification's `store_register` compares with the register's range.
    #[allow(clippy::cast_possible_truncation, reason = "a magnitude of at most max <= 2^31")]
    pub(crate) fn register_magnitude(val: &BCNum, max: usize) -> (r: (usize, bool))
        requires
            val.scale <= BC_SCALE_MAX,
            max <= BC_BASE_MAX,
        ensures
            r.0 <= max + 1,
            forall|x: SpecNum| #[trigger] r_num(*val, x) ==> {
                let m = bc_spec::power::mag_to_u64(bc_spec::num::drop_mag(x.mag, x.scale));
                &&& r.1 == (x.neg && !bc_spec::num::is_zero_mag(x.mag))
                &&& (r.0 > max) == (m > max as u64)
                &&& r.0 <= max ==> r.0 as u64 == m
            },
    {
        proof {
            lemma_pow10_pos(val.scale as nat);
        }
        let ip = big_abs(&big_tdiv(&val.coeff, &pow10_within(val.scale)));
        let negative = big_is_negative(&val.coeff);
        let magnitude = if matches!(big_cmp(&ip, &big_from_usize(max)), Ordering::Greater) {
            max + 1
        } else {
            big_to_u64_small(&ip) as usize
        };
        proof {
            assert forall|x: SpecNum| #[trigger] r_num(*val, x) implies {
                let m = bc_spec::power::mag_to_u64(bc_spec::num::drop_mag(x.mag, x.scale));
                &&& negative == (x.neg && !bc_spec::num::is_zero_mag(x.mag))
                &&& (magnitude > max) == (m > max as u64)
                &&& magnitude <= max ==> magnitude as u64 == m
            } by {
                lemma_register_input(x);
                lemma_mag_bounds(x.mag);
                let c = num_coeff(x);
                let p = spec_num::pow10(x.scale as nat);
                assert(spec_tdiv(c, p) == (if c >= 0 { c / p } else { -((-c) / p) }));
                assert(big_view(&ip) == int_mag(x));
            }
        }
        (magnitude, negative)
    }

    /// The text of a register clamp warning (the specification's `store_register`): `kind` -2
    /// negative, -1 too small, 1 too large.
    pub(crate) fn register_message(reg: Register, kind: i8, min: usize, max: usize) -> (msg: Vec<u8>)
        requires
            kind == -2 || kind == -1 || kind == 1,
        ensures
            msg@ == if kind == -2 {
                seq![110u8, 101, 103, 97, 116, 105, 118, 101, 32].add(bc_spec::eval::reg_name(reg_code(reg)))
                    .add(seq![44u8, 32, 115, 101, 116, 32, 116, 111, 32]).add(dec_str(min as u64))
            } else if kind == -1 {
                bc_spec::eval::reg_name(reg_code(reg)).add(seq![32u8, 116, 111, 111, 32, 115, 109, 97, 108, 108, 44, 32, 115, 101, 116, 32, 116, 111, 32]).add(dec_str(min as u64))
            } else {
                bc_spec::eval::reg_name(reg_code(reg)).add(seq![32u8, 116, 111, 111, 32, 108, 97, 114, 103, 101, 44, 32, 115, 101, 116, 32, 116, 111, 32]).add(dec_str(max as u64))
            },
    {
        let name: [u8; 5] = match reg {
            Register::Scale => [115, 99, 97, 108, 101],
            Register::Ibase => [105, 98, 97, 115, 101],
            Register::Obase => [111, 98, 97, 115, 101],
        };
        proof {
            assert(name@ == bc_spec::eval::reg_name(reg_code(reg)));
        }
        let mut msg: Vec<u8> = Vec::new();
        if kind == -2 {
            let neg: [u8; 9] = [110, 101, 103, 97, 116, 105, 118, 101, 32];
            let set: [u8; 9] = [44, 32, 115, 101, 116, 32, 116, 111, 32];
            msg.extend_from_slice(&neg);
            msg.extend_from_slice(&name);
            msg.extend_from_slice(&set);
            push_dec(&mut msg, min as u64);
            proof {
                assert(neg@ == seq![110u8, 101, 103, 97, 116, 105, 118, 101, 32]);
                assert(set@ == seq![44u8, 32, 115, 101, 116, 32, 116, 111, 32]);
                assert(msg@ =~= neg@.add(name@).add(set@).add(dec_str(min as u64)));
            }
        } else {
            let small: [u8; 19] = [32, 116, 111, 111, 32, 115, 109, 97, 108, 108, 44, 32, 115, 101, 116, 32, 116, 111, 32];
            let large: [u8; 19] = [32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 44, 32, 115, 101, 116, 32, 116, 111, 32];
            msg.extend_from_slice(&name);
            if kind == -1 {
                msg.extend_from_slice(&small);
                push_dec(&mut msg, min as u64);
                proof {
                    assert(small@ == seq![32u8, 116, 111, 111, 32, 115, 109, 97, 108, 108, 44, 32, 115, 101, 116, 32, 116, 111, 32]);
                    assert(msg@ =~= name@.add(small@).add(dec_str(min as u64)));
                }
            } else {
                msg.extend_from_slice(&large);
                push_dec(&mut msg, max as u64);
                proof {
                    assert(large@ == seq![32u8, 116, 111, 111, 32, 108, 97, 114, 103, 101, 44, 32, 115, 101, 116, 32, 116, 111, 32]);
                    assert(msg@ =~= name@.add(large@).add(dec_str(max as u64)));
                }
            }
        }
        msg
    }

    /// Stores `val`, truncated to an integer, into register `reg`, clamping it to the register's
    /// range with a warning (`docs/COMPATIBILITY.md` §3.3; the specification's
    /// `store_register`). Returns the stored value.
    pub(crate) fn store_register_ref(&mut self, reg: Register, val: &BCNum, Ghost(st): Ghost<SpecState>, Ghost(x): Ghost<SpecNum>) -> (r: usize)
        requires
            old(self).inv(),
            val.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_num(*val, x)) ==> ({
                let s = bc_spec::eval::store_register(st, reg_code(reg), x);
                &&& r_state(*final(self), s.st)
                &&& to_l0(s.val) == BCNum::spec_new_usize(r) && wf_num(s.val)
            }),
            r <= BC_BASE_MAX,
    {
        let ghost e0 = *self;
        let (min, max) = match reg {
            Register::Scale => (0usize, BC_SCALE_MAX),
            Register::Ibase => (2usize, IBASE_MAX),
            Register::Obase => (2usize, BC_BASE_MAX),
        };
        let (magnitude, negative) = Self::register_magnitude(val, max);
        let (v, kind) = verified_clamp_register(magnitude, negative, min, max);
        let ghost msg_spec: Seq<u8> = Seq::empty();
        if kind != 0 {
            let msg = Self::register_message(reg, kind, min, max);
            proof {
                msg_spec = msg@;
            }
            self.warn_ref(&msg, Ghost(st));
        }
        match reg {
            Register::Scale => self.scale = v,
            Register::Ibase => self.ibase = v,
            Register::Obase => self.obase = v,
        }
        proof {
            if r_state(e0, st) && r_num(*val, x) {
                let r8 = reg_code(reg);
                assert(min as int == bc_spec::eval::reg_min(r8) as int && max as int == bc_spec::eval::reg_max(r8) as int);
                lemma_u64_mag(v as u64);
                let s = bc_spec::eval::store_register(st, r8, x);
                assert(r_state(*self, s.st));
            }
        }
        v
    }

    /// The specification's place of anything but a named expression: a variable with no name.
    pub(crate) fn empty_place() -> (p: Place)
        ensures
            r_place(p, bc_spec::eval::Place { kind: 0u8, name: seq![], idx: 0u32, reg: 0u8 }),
    {
        let none: Vec<u8> = Vec::new();
        proof { assert(none@ =~= seq![]); }
        Place::Variable(crate::parser::ascii_string(none.as_slice()))
    }

    /// Reads the current value of a resolved target (the specification's `load`).
    pub(crate) fn load_ref(&self, p: &Place, Ghost(sp): Ghost<SpecPlace>, Ghost(st): Ghost<SpecState>) -> (r: BCNum)
        requires
            self.inv(),
        ensures
            r.scale <= BC_SCALE_MAX,
            (r_state(*self, st) && r_place(*p, sp)) ==> r_num(r, bc_spec::eval::load(st, sp)),
    {
        match p {
            Place::Variable(name) => {
                let v = self.var_get(name);
                proof {
                    if r_state(*self, st) && r_place(*p, sp) {
                        let nm = text_view(*name);
                        lemma_var_get(st.vars, nm);
                        if self.variables@.contains_key(*name) {
                            let ss = var_lookup(st.vars, nm)->Some_0;
                            assert(r_stack(self.variables@[*name]@, ss));
                            if ss.len() > 0 {
                                assert(r_num(self.variables@[*name]@[ss.len() - 1], ss[ss.len() - 1]));
                            }
                        } else {
                            lemma_var_absent(self.variables@, st.vars, *name);
                        }
                    }
                }
                v
            },
            Place::Element(name, i) => {
                let v = self.arr_get(name, *i);
                proof {
                    if r_state(*self, st) && r_place(*p, sp) {
                        let nm = text_view(*name);
                        lemma_arr_top(st.arrays, nm);
                        lemma_elem_get(arr_top(st.arrays, nm).elems, sp.idx);
                        let m = self.arrays@;
                        if m.contains_key(*name) {
                            let ss = arr_lookup(st.arrays, nm)->Some_0;
                            assert(r_frames(m[*name]@, ss));
                            if ss.len() > 0 {
                                assert(r_frame(m[*name]@[ss.len() - 1]@, ss[ss.len() - 1]));
                            }
                        } else {
                            lemma_arr_absent(m, st.arrays, *name);
                        }
                    }
                }
                v
            },
            Place::Register(reg) => {
                let value = match reg {
                    Register::Scale => self.scale,
                    Register::Ibase => self.ibase,
                    Register::Obase => self.obase,
                };
                proof {
                    lemma_u64_mag(value as u64);
                }
                BCNum::new(big_from_usize(value), 0)
            },
        }
    }

    /// Writes `val` to a resolved target (the specification's `store`) and returns the value now
    /// held there (registers clamp it).
    pub(crate) fn store_ref(&mut self, p: Place, val: BCNum, Ghost(sp): Ghost<SpecPlace>, Ghost(st): Ghost<SpecState>, Ghost(x): Ghost<SpecNum>) -> (r: BCNum)
        requires
            old(self).inv(),
            val.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_place(p, sp) && r_num(val, x)) ==> ({
                let s = bc_spec::eval::store(st, sp, x);
                r_state(*final(self), s.st) && r_num(r, s.val)
            }),
    {
        let ghost e0 = *self;
        let ghost hyp = r_state(*self, st) && r_place(p, sp) && r_num(val, x);
        match p {
            Place::Variable(name) => {
                let ghost m = self.variables@;
                let ghost nm = text_view(name);
                let ghost nm_name = name;
                let r = val.copy();
                self.var_set(name, val);
                proof {
                    if hyp {
                        if !m.contains_key(nm_name) {
                            lemma_var_absent(m, st.vars, nm_name);
                        }
                        let m2 = self.variables@;
                        let found = var_lookup(st.vars, nm);
                        assert(r_stack(m2[nm_name]@, upd_stack(found, 0u8, x)->Some_0));
                        lemma_r_vars_update(m, m2, st.vars, nm_name, 0u8, x);
                    }
                }
                r
            },
            Place::Element(name, i) => {
                let ghost m = self.arrays@;
                let ghost nm = text_view(name);
                let ghost nm_name = name;
                let ghost gval = val;
                let r = val.copy();
                self.arr_set(name, i, val);
                proof {
                    if hyp {
                        if !m.contains_key(nm_name) {
                            lemma_arr_absent(m, st.arrays, nm_name);
                        }
                        lemma_arr_top(st.arrays, nm);
                        let top = arr_top(st.arrays, nm);
                        let nf = bc_spec::eval::ArrFrame { elems: bc_spec::eval::elem_set(top.elems, i as u32, x, Seq::empty()) };
                        let m2 = self.arrays@;
                        let found = arr_lookup(st.arrays, nm);
                        let t = m2[nm_name]@;
                        if m.contains_key(nm_name) && m[nm_name]@.len() > 0 {
                            let ps = m[nm_name]@;
                            let ss = found->Some_0;
                            assert(r_frames(ps, ss));
                            assert(r_frame(ps[ps.len() - 1]@, ss[ss.len() - 1]));
                            lemma_r_frame_set(ps.last()@, top, i, gval, x);
                            let sn = bc_spec::eval::frame_op(ss, 0u8, nf);
                            assert(sn == ss.drop_last().push(nf));
                            assert forall|j: int| 0 <= j < t.len() implies #[trigger] r_frame(t[j]@, sn[j]) by {
                                if j < t.len() - 1 {
                                    assert(t[j] == t.drop_last()[j]);
                                    assert(t.drop_last()[j] == ps[j]);
                                }
                            }
                        } else {
                            assert(r_frame(Map::<usize, BCNum>::empty(), bc_spec::eval::ArrFrame { elems: Seq::empty() }));
                            lemma_r_frame_set(Map::<usize, BCNum>::empty(), top, i, gval, x);
                            let sn = upd_frames(found, 0u8, nf)->Some_0;
                            assert(sn.len() == 1 && sn[0] == nf);
                            assert(r_frame(t[0]@, sn[0]));
                        }
                        assert(r_frames(m2[nm_name]@, upd_frames(found, 0u8, nf)->Some_0));
                        lemma_r_arrays_update(m, m2, st.arrays, nm_name, 0u8, nf);
                    }
                }
                r
            },
            Place::Register(reg) => {
                let v = self.store_register_ref(reg, &val, Ghost(st), Ghost(x));
                proof {
                    lemma_u64_mag(v as u64);
                }
                BCNum::new(big_from_usize(v), 0)
            },
        }
    }

    /// Whether the expression is an assignment, possibly under unary minus (the specification's
    /// `is_assignment`, with the most fuel).
    pub(crate) fn is_assignment_ref(code: &Rc<Code>, e: usize, Ghost(nodes): Ghost<SpecNodes>) -> (r: bool)
        ensures
            r_rc(*code, nodes) ==> r == bc_spec::den::is_asg(nodes, e),
    {
        let ghost hyp = r_rc(*code, nodes);
        let mut i = e;
        let mut fuel: u64 = 0xFFFF_FFFF_FFFF_FFFF;
        while fuel > 0
            invariant
                hyp == r_rc(*code, nodes),
                hyp ==> bc_spec::den::is_asg(nodes, e) == is_assignment(nodes, i, fuel),
            decreases fuel,
        {
            if i >= code.nodes.len() {
                return false;
            }
            proof { if hyp { assert(r_node(code.nodes@[i as int], nodes[i as int])); } }
            match &code.nodes[i] {
                PNode::Assign(..) => { return true; },
                PNode::Neg(inner) => {
                    i = *inner;
                    fuel -= 1;
                },
                _ => { return false; },
            }
        }
        false
    }

}

} // verus!
