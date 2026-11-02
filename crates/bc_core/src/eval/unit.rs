// SPDX-License-Identifier: MIT

//! The statements of a unit, runtime diagnostics, and the `-l` functions (`eval_math`).

use super::*;

verus! {

impl Evaluator {
    /// The statements of a unit in order (the specification's `exec_items`); `quit` (never
    /// built by the parser) stops them with `BcError::Quit`.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "the specification relates the list to the unit")]
    pub(crate) fn exec_items_ref(&mut self, code: &Rc<Code>, stmts: &Vec<usize>, Ghost(nodes): Ghost<SpecNodes>, Ghost(ns): Ghost<SpecIndices>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_rc(*code, nodes) && stmts@ == ns) ==> forall|f: u64|
                done(#[trigger] bc_spec::top::exec_items(nodes, ns, st, f)) ==> r_unit(r, *final(self), bc_spec::top::exec_items(nodes, ns, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes) && stmts@ == ns;
        let ghost fin = exists|f: u64| done(#[trigger] bc_spec::top::exec_items(nodes, ns, st, f));
        let ghost mut si = st;
        let mut i: usize = 0;
        proof {
            if hyp {
                assert(ns.skip(0) =~= ns);
            }
        }
        while i < stmts.len()
            invariant
                self.inv(),
                self.eval_depth == d,
                d == old(self).eval_depth,
                i <= stmts.len(),
                hyp == (r_state(*old(self), st) && r_rc(*code, nodes) && stmts@ == ns),
                fin == exists|f: u64| done(#[trigger] bc_spec::top::exec_items(nodes, ns, st, f)),
                hyp ==> ns.len() == stmts.len(),
                hyp && fin ==> r_state(*self, si),
                hyp ==> forall|f: u64| done(#[trigger] bc_spec::top::exec_items(nodes, ns, st, f)) ==> f as int >= i
                    && bc_spec::top::exec_items(nodes, ns, st, f) == bc_spec::top::exec_items(nodes, ns.skip(i as int), si, (f - i) as u64),
            decreases stmts.len() - i,
        {
            let ghost ji = ns[i as int];
            let ghost e0 = *self;
            proof {
                if hyp {
                    assert(ns.skip(i as int)[0] == ji);
                    assert(ns.skip(i as int).drop_first() =~= ns.skip(i as int + 1));
                }
            }
            let ri = self.exec_ref(code, stmts[i], Ghost(nodes), Ghost(si));
            if let Err(err) = ri {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::top::exec_items(nodes, ns, st, f))
                            implies r_unit(Err(err), *self, bc_spec::top::exec_items(nodes, ns, st, f), d) by {
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
            if self.quit_flag {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::top::exec_items(nodes, ns, st, f)) implies false by {
                            assert(r_state(e0, si));
                            assert(done(exec(nodes, ji, si, (f - i - 1) as u64)));
                        }
                    }
                }
                return Err(BcError::Quit);
            }
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] bc_spec::top::exec_items(nodes, ns, st, f)) implies f as int >= i + 1
                        && bc_spec::top::exec_items(nodes, ns, st, f) == bc_spec::top::exec_items(nodes, ns.skip(i as int + 1), x.st, (f - i - 1) as u64) by {
                        assert(r_state(e0, si));
                        assert(done(exec(nodes, ji, si, (f - i - 1) as u64)));
                    }
                    if fin {
                        let ff = choose|f: u64| done(#[trigger] bc_spec::top::exec_items(nodes, ns, st, f));
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
                assert forall|f: u64| done(#[trigger] bc_spec::top::exec_items(nodes, ns, st, f))
                    implies r_unit(Ok(()), *self, bc_spec::top::exec_items(nodes, ns, st, f), d) by {
                }
            }
        }
        Ok(())
    }

    /// Writes the message of a runtime error (the specification's `msg_*`).
    #[allow(clippy::redundant_as_str, reason = "Verus specifies str::as_bytes and String::as_str, not String::as_bytes")]
    pub(crate) fn write_runtime_msg(&mut self, kind: &RuntimeError)
        ensures
            same_but_err(*old(self), *final(self)),
            err_log(&final(self).stderr_writer) == err_log(&old(self).stderr_writer).add(runtime_msg(*kind)),
    {
        let ghost log0 = err_log(&self.stderr_writer);
        match kind {
            RuntimeError::DivideByZero => {
                let m: [u8; 14] = [68, 105, 118, 105, 100, 101, 32, 98, 121, 32, 122, 101, 114, 111];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= bc_spec::eval::msg_divide_by_zero()); }
            },
            RuntimeError::NegativePowerOfZero => {
                let m: [u8; 14] = [100, 105, 118, 105, 100, 101, 32, 98, 121, 32, 122, 101, 114, 111];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= bc_spec::eval::msg_negative_power_of_zero()); }
            },
            RuntimeError::ModuloByZero => {
                let m: [u8; 14] = [77, 111, 100, 117, 108, 111, 32, 98, 121, 32, 122, 101, 114, 111];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= bc_spec::eval::msg_modulo_by_zero()); }
            },
            RuntimeError::NegativeSqrt => {
                let m: [u8; 32] = [83, 113, 117, 97, 114, 101, 32, 114, 111, 111, 116, 32, 111, 102, 32, 97, 32, 110, 101, 103, 97, 116, 105, 118, 101, 32, 110, 117, 109, 98, 101, 114];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= bc_spec::eval::msg_negative_sqrt()); }
            },
            RuntimeError::UndefinedFunction(name) => {
                let a: [u8; 9] = [70, 117, 110, 99, 116, 105, 111, 110, 32];
                let b: [u8; 13] = [32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 101, 100, 46];
                self.stderr_writer.write_bytes(&a);
                self.stderr_writer.write_bytes(name.as_str().as_bytes());
                self.stderr_writer.write_bytes(&b);
                proof {
                    assert(a@ =~= seq![70u8, 117, 110, 99, 116, 105, 111, 110, 32]);
                    assert(b@ =~= seq![32u8, 110, 111, 116, 32, 100, 101, 102, 105, 110, 101, 100, 46]);
                    assert(log0.add(a@).add(text_view(*name)).add(b@) =~= log0.add(bc_spec::eval::msg_undefined_function(text_view(*name))));
                }
            },
            RuntimeError::ParameterMismatch => {
                let m: [u8; 25] = [80, 97, 114, 97, 109, 101, 116, 101, 114, 32, 110, 117, 109, 98, 101, 114, 32, 109, 105, 115, 109, 97, 116, 99, 104];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= bc_spec::eval::msg_parameter_mismatch()); }
            },
            RuntimeError::ParameterTypeMismatch(name) => {
                let a: [u8; 34] = [80, 97, 114, 97, 109, 101, 116, 101, 114, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32];
                let b: [u8; 1] = [46];
                self.stderr_writer.write_bytes(&a);
                self.stderr_writer.write_bytes(name.as_str().as_bytes());
                self.stderr_writer.write_bytes(&b);
                proof {
                    assert(a@ =~= seq![80u8, 97, 114, 97, 109, 101, 116, 101, 114, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32]);
                    assert(b@ =~= seq![46u8]);
                    assert(log0.add(a@).add(text_view(*name)).add(b@) =~= log0.add(bc_spec::eval::msg_parameter_type(text_view(*name))));
                }
            },
            RuntimeError::ArraySubscriptOutOfBounds(name) => {
                let a: [u8; 6] = [65, 114, 114, 97, 121, 32];
                let b: [u8; 25] = [32, 115, 117, 98, 115, 99, 114, 105, 112, 116, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 46];
                self.stderr_writer.write_bytes(&a);
                self.stderr_writer.write_bytes(name.as_str().as_bytes());
                self.stderr_writer.write_bytes(&b);
                proof {
                    assert(a@ =~= seq![65u8, 114, 114, 97, 121, 32]);
                    assert(b@ =~= seq![32u8, 115, 117, 98, 115, 99, 114, 105, 112, 116, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 46]);
                    assert(log0.add(a@).add(text_view(*name)).add(b@) =~= log0.add(bc_spec::eval::msg_subscript(text_view(*name))));
                }
            },
            RuntimeError::ExponentTooLarge => {
                let m: [u8; 27] = [101, 120, 112, 111, 110, 101, 110, 116, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 32, 105, 110, 32, 114, 97, 105, 115, 101];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= bc_spec::eval::msg_exponent_too_large()); }
            },
            RuntimeError::ScaleTooLarge => {
                let m: [u8; 15] = [115, 99, 97, 108, 101, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= bc_spec::eval::msg_scale_too_large()); }
            },
            RuntimeError::MathArgumentTooLarge => {
                let m: [u8; 18] = [97, 114, 103, 117, 109, 101, 110, 116, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= runtime_msg(RuntimeError::MathArgumentTooLarge)); }
            },
            RuntimeError::NestingTooDeep => {
                let m: [u8; 16] = [110, 101, 115, 116, 105, 110, 103, 32, 116, 111, 111, 32, 100, 101, 101, 112];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= bc_spec::eval::msg_nesting_too_deep()); }
            },
            RuntimeError::BaseOutOfRange => {
                let m: [u8; 17] = [98, 97, 115, 101, 32, 111, 117, 116, 32, 111, 102, 32, 114, 97, 110, 103, 101];
                self.stderr_writer.write_bytes(&m);
                proof { assert(m@ =~= runtime_msg(RuntimeError::BaseOutOfRange)); }
            },
        }
    }

    /// Writes `Runtime error (func=<f>): <msg>` for a runtime error of kind `kind` raised in
    /// function `func` (`None`: at top level), the specification's `runtime_diag`.
    #[allow(clippy::redundant_as_str, reason = "Verus specifies str::as_bytes and String::as_str, not String::as_bytes")]
    pub(crate) fn write_runtime_diag(&mut self, kind: &RuntimeError, func: &Option<String>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            same_but_err(*old(self), *final(self)),
            forall|x: bc_spec::eval::RErr| r_err(BcError::Runtime { kind: *kind, func: *func }, x)
                ==> #[trigger] err_log(&final(self).stderr_writer) == err_log(&old(self).stderr_writer).add(bc_spec::top::runtime_diag(x)),
    {
        let ghost log0 = err_log(&self.stderr_writer);
        let head: [u8; 20] = [82, 117, 110, 116, 105, 109, 101, 32, 101, 114, 114, 111, 114, 32, 40, 102, 117, 110, 99, 61];
        self.stderr_writer.write_bytes(&head);
        let main: [u8; 6] = [40, 109, 97, 105, 110, 41];
        match func {
            Some(f) => self.stderr_writer.write_bytes(f.as_str().as_bytes()),
            None => self.stderr_writer.write_bytes(&main),
        }
        let sep: [u8; 3] = [41, 58, 32];
        self.stderr_writer.write_bytes(&sep);
        let ghost log1 = err_log(&self.stderr_writer);
        self.write_runtime_msg(kind);
        let nl: [u8; 1] = [10];
        self.stderr_writer.write_bytes(&nl);
        proof {
            assert(head@ =~= seq![82u8, 117, 110, 116, 105, 109, 101, 32, 101, 114, 114, 111, 114, 32, 40, 102, 117, 110, 99, 61]);
            assert(main@ =~= seq![40u8, 109, 97, 105, 110, 41]);
            assert(sep@ =~= seq![41u8, 58, 32]);
            assert(nl@ =~= seq![10u8]);
            assert forall|x: bc_spec::eval::RErr| r_err(BcError::Runtime { kind: *kind, func: *func }, x)
                implies #[trigger] err_log(&self.stderr_writer) == log0.add(bc_spec::top::runtime_diag(x)) by {
                assert(err_log(&self.stderr_writer) =~= log0.add(bc_spec::top::runtime_diag(x)));
            }
        }
    }

    /// `-l`'s functions, for a name that has no definition when the math library is enabled:
    /// `s`, `c`, `a`, `l`, `e` with one expression argument and `j` with two; any other name or
    /// argument list is undefined. The arguments are evaluated first, then the function runs at
    /// the `scale` that the evaluation left. An `Ok` result is the function's exact value at
    /// some argument values, truncated toward zero at that scale (`mathlib::math_result`); which
    /// values is not stated, because the refinement theorem excludes `-l` (`r_state` requires
    /// `!math_enabled`).
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "the call's argument list")]
    #[allow(clippy::collapsible_if, reason = "Verus does not support `let` chains")]
    pub(crate) fn eval_math(&mut self, code: &Rc<Code>, name: &String, args: &Vec<PArg>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            r is Ok ==> r->Ok_0.scale == final(self).scale,
            r is Ok ==> math_ok(text_view(*name), r->Ok_0),
    {
        let nb = name.as_str().as_bytes();
        if nb.len() == 1 && args.len() == 1 {
            let c = nb[0];
            if let PArg::Expr(expr) = &args[0] {
                // s, c, a, l, e
                if c == 115 || c == 99 || c == 97 || c == 108 || c == 101 {
                    let x = self.eval_ref(code, *expr, Ghost(arbitrary()), Ghost(arbitrary()))?;
                    let scale = self.scale;
                    let res = if c == 115 {
                        bc_sin(&x, scale)
                    } else if c == 99 {
                        bc_cos(&x, scale)
                    } else if c == 97 {
                        bc_atan(&x, scale)
                    } else if c == 108 {
                        bc_ln(&x, scale)
                    } else {
                        bc_exp(&x, scale)
                    };
                    return match res {
                        Ok(v) => {
                            proof {
                                assert(nb@ =~= seq![c]);
                                lemma_math_ok(text_view(*name), x, v, v);
                            }
                            Ok(v)
                        },
                        Err(kind) => Err(BcError::Runtime { kind, func: None }),
                    };
                }
            }
        }
        if nb.len() == 1 && nb[0] == 106 && args.len() == 2 {
            if let PArg::Expr(expr_n) = &args[0] {
                if let PArg::Expr(expr_x) = &args[1] {
                    let n_val = self.eval_ref(code, *expr_n, Ghost(arbitrary()), Ghost(arbitrary()))?;
                    let x_val = self.eval_ref(code, *expr_x, Ghost(arbitrary()), Ghost(arbitrary()))?;
                    return match bc_bessel(&n_val, &x_val, self.scale) {
                        Ok(v) => {
                            proof {
                                assert(nb@ =~= seq![106u8]);
                                lemma_math_ok(text_view(*name), n_val, x_val, v);
                            }
                            Ok(v)
                        },
                        Err(kind) => Err(BcError::Runtime { kind, func: None }),
                    };
                }
            }
        }
        Err(BcError::Runtime { kind: RuntimeError::UndefinedFunction(name.clone()), func: None })
    }
}

} // verus!
