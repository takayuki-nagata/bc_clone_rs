// SPDX-License-Identifier: MIT

//! Statement execution (the specification's `exec`): blocks, `if`, loops and `return`.

use super::*;

verus! {

impl Evaluator {
    /// `try_execute` with the arena subtree `n` of `nodes` and the specification state `st`:
    /// one nesting level around `exec_node_ref` (the specification's `exec`).
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
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes);
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_depth) {
            let r = Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
            proof {
                if hyp {
                    assert(with_depth(st, d as u64) == st);
                    assert forall|f: u64| done(#[trigger] exec(nodes, n, st, f)) implies r_unit(r, *self, exec(nodes, n, st, f), d) by {}
                }
            }
            return r;
        }
        let ghost before = *self;
        self.eval_depth += 1;
        let ghost st1 = with_depth(st, (d + 1) as u64);
        proof {
            if hyp {
                lemma_r_state_depth(before, *self, st);
            }
        }
        let r = self.exec_node_ref(code, n, Ghost(nodes), Ghost(st1));
        let ghost mid = *self;
        self.eval_depth -= 1;
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec(nodes, n, st, f)) implies r_unit(r, *self, exec(nodes, n, st, f), d) by {
                    let x = exec_node(nodes, n, st1, (f - 1) as u64);
                    assert(done(x));
                    assert(r_unit(r, mid, x, (d + 1) as usize));
                    if r is Ok {
                        lemma_r_state_depth(mid, *self, x.st);
                        assert(with_depth(with_depth(x.st, d as u64), st.depth) == with_depth(x.st, st.depth));
                    } else {
                        lemma_r_state_depth(mid, *self, with_depth(x.st, (d + 1) as u64));
                        assert(with_depth(with_depth(x.st, (d + 1) as u64), d as u64) == with_depth(x.st, d as u64));
                    }
                }
            }
        }
        r
    }

    /// One statement (the specification's `exec_node`): nothing runs while a `break` or `return`
    /// is pending.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn exec_node_ref(
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
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes);
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        if verified_should_abort_execution(self.break_flag, self.return_flag, self.quit_flag) {
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                }
            }
            return Ok(());
        }
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        if n >= code.nodes.len() {
            return Ok(());
        }
        match &code.nodes[n] {
            PNode::Block(list) => self.exec_block(code, Ghost(n), list, Ghost(nodes), Ghost(st)),
            PNode::ExprStmt(e) => self.exec_expr_stmt(code, Ghost(n), *e, Ghost(nodes), Ghost(st)),
            PNode::Str(t) => {
                self.stdout_writer.write_bytes(t.as_slice());
                self.stdout_writer.flush_out();
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                    }
                }
                Ok(())
            },
            PNode::Break => {
                self.break_flag = true;
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                    }
                }
                Ok(())
            },
            PNode::Return(v) => self.exec_return(code, Ghost(n), *v, Ghost(nodes), Ghost(st)),
            PNode::If(c, b) => self.exec_if(code, Ghost(n), *c, *b, Ghost(nodes), Ghost(st)),
            PNode::While(c, b) => {
                let ghost (jc, jb) = (*c, *b);
                let r = self.exec_loop_ref(code, *c, None, *b, Ghost(nodes), Ghost(0usize), Ghost(st));
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(r, *self, exec_node(nodes, n, st, f), d) by {
                            assert(exec_node(nodes, n, st, f) == bc_spec::eval::exec_loop(nodes, jc, 0usize, false, jb, st, (f - 1) as u64));
                        }
                    }
                }
                r
            },
            PNode::For(i, c, p, b) => self.exec_for_ref(code, Ghost(n), *i, *c, *p, *b, Ghost(nodes), Ghost(st)),
            PNode::Define(name, _, _, _) => {
                let ghost m = self.functions@;
                proof {
                    axiom_string_obeys_cmp();
                    broadcast use vstd::std_specs::btree::group_btree_axioms;
                }
                let fd = FunctionDef { code: share_code(code), def: n };
                let ghost gfd = fd;
                self.functions.insert(name.clone(), fd);
                proof {
                    if hyp {
                        match nodes[n as int] {
                            Node::Define(sname, ps, autos, body) => {
                                let g = Func { name: sname, params: ps, autos: autos, body: body, nodes: nodes };
                                assert(r_func(gfd, g));
                                lemma_r_funcs_define(m, st.funcs, *name, gfd, g);
                            },
                            _ => {},
                        }
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                    }
                }
                Ok(())
            },
            _ => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                    }
                }
                Ok(())
            },
        }
    }

    /// A block (the specification's `exec_list`): its statements in order, stopping when a
    /// `break` or `return` is pending.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "the precondition relates the list to the `Node::Block` it comes from")]
    pub(crate) fn exec_block(&mut self, code: &Rc<Code>, Ghost(n): Ghost<usize>, list: &Vec<usize>, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Block(*list),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_rc(*code, nodes)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes);
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let ghost ns = list@;
        let ghost fin = exists|f: u64| done(#[trigger] exec_node(nodes, n, st, f));
        let ghost mut sti = st;
        let mut i: usize = 0;
        proof {
            if hyp {
                assert(ns.skip(0) =~= ns);
                assert(n < nodes.len());
                assert(nodes[n as int] is Block);
                assert(nodes[n as int] == Node::Block(ns));
            }
        }
        while i < list.len()
            invariant
                self.inv(),
                self.eval_depth == d,
                d == old(self).eval_depth,
                hyp == (r_state(*old(self), st) && r_rc(*code, nodes)),
                hyp ==> nodes[n as int] == Node::Block(ns),
                i <= list.len(),
                ns == list@,
                fin == exists|f: u64| done(#[trigger] exec_node(nodes, n, st, f)),
                hyp && fin ==> r_state(*self, sti) && !sti.brk && !sti.ret,
                hyp ==> forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) ==> f as int > i + 1
                    && exec_node(nodes, n, st, f) == bc_spec::eval::exec_list(nodes, ns.skip(i as int), sti, (f - 1 - i) as u64),
            decreases list.len() - i,
        {
            let ghost si = sti;
            let ghost ji = ns[i as int];
            proof {
                if hyp {
                    assert(ns.skip(i as int)[0] == ji);
                    assert(ns.skip(i as int).drop_first() =~= ns.skip(i as int + 1));
                }
            }
            proof {
                if hyp {
                }
            }
            let ghost e_before = *self;
            let ri = self.exec_ref(code, list[i], Ghost(nodes), Ghost(si));
            if let Err(e) = ri {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(e), *self, exec_node(nodes, n, st, f), d) by {
                            let g = (f - 1 - i) as u64;
                            assert(ns.skip(i as int).len() > 0);
                            assert(bc_spec::eval::exec_list(nodes, ns.skip(i as int), si, g) == {
                                let r0 = exec(nodes, ji, si, (g - 1) as u64);
                                if !r0.ok { r0 } else if r0.st.brk || r0.st.ret { r0 } else { bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), r0.st, (g - 1) as u64) }
                            });
                            assert(done(exec(nodes, ji, si, (g - 1) as u64)));
                        }
                    }
                }
                return Err(e);
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
            if verified_should_abort_execution(self.break_flag, self.return_flag, self.quit_flag) {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {
                            assert(done(exec(nodes, ji, si, (f - 2 - i) as u64)));
                        }
                    }
                }
                return Ok(());
            }
            proof {
                if hyp && fin {
                    let ff = choose|f: u64| done(#[trigger] exec_node(nodes, n, st, f));
                    let g = (ff - 1 - i) as u64;
                    assert(ns.skip(i as int).len() > 0);
                    assert(bc_spec::eval::exec_list(nodes, ns.skip(i as int), si, g) == {
                        let r0 = exec(nodes, ji, si, (g - 1) as u64);
                        if !r0.ok { r0 } else if r0.st.brk || r0.st.ret { r0 } else { bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), r0.st, (g - 1) as u64) }
                    });
                    assert(done(exec(nodes, ji, si, (g - 1) as u64)));
                    assert(r_state(e_before, si));
                    assert(r_unit(ri, *self, exec(nodes, ji, si, (g - 1) as u64), d));
                    assert(r_state(*self, x.st));
                }
                if hyp {
                    sti = x.st;
                    assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies f as int > i + 2
                        && exec_node(nodes, n, st, f) == bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), sti, (f - 2 - i) as u64) by {
                        let g = (f - 1 - i) as u64;
                        assert(ns.skip(i as int).len() > 0);
                        assert(bc_spec::eval::exec_list(nodes, ns.skip(i as int), si, g) == {
                            let r0 = exec(nodes, ji, si, (g - 1) as u64);
                            if !r0.ok { r0 } else if r0.st.brk || r0.st.ret { r0 } else { bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), r0.st, (g - 1) as u64) }
                        });
                        assert(done(exec(nodes, ji, si, (g - 1) as u64)));
                        if f as int <= i + 2 {
                            assert(bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), sti, 0) == bc_spec::eval::er_fuel(sti));
                        }
                    }
                }
            }
            i += 1;
        }
        proof {
            if hyp {
                assert(ns.skip(i as int) =~= Seq::<usize>::empty());
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
            }
        }
        Ok(())
    }

    /// Whether an expression statement is an assignment, whose value is not printed (POSIX).
    /// As in GNU bc, unary minus keeps that property (`-a = 5` prints nothing) and parentheses
    /// remove it (`(a = 5)` prints 5).
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn is_assignment_ref(code: &Rc<Code>, e: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>, Ghost(f0): Ghost<u64>) -> (r: bool)
        ensures
            (r_rc(*code, nodes) && ev(nodes, e, st, f0).ok && f0 < u64::MAX) ==> r == is_assignment(nodes, e, (f0 + 1) as u64),
    {
        let ghost hyp = r_rc(*code, nodes) && ev(nodes, e, st, f0).ok && f0 < u64::MAX;
        let mut i = e;
        let ghost mut si = st;
        let ghost mut fi: u64 = f0;
        loop
            invariant
                hyp == (r_rc(*code, nodes) && ev(nodes, e, st, f0).ok && f0 < u64::MAX),
                hyp ==> ev(nodes, i, si, fi).ok && fi < u64::MAX && is_assignment(nodes, e, (f0 + 1) as u64) == is_assignment(nodes, i, (fi + 1) as u64),
        {
            if i >= code.nodes.len() {
                return false;
            }
            proof { if hyp { assert(r_node(code.nodes@[i as int], nodes[i as int])); } }
            match &code.nodes[i] {
                PNode::Assign(..) => { return true; },
                PNode::Neg(inner) => {
                    proof {
                        if hyp {
                            let st1 = with_depth(si, (si.depth + 1) as u64);
                            assert(ev_node(nodes, i, st1, (fi - 1) as u64).ok);
                            assert(ev_unary(nodes, 0u8, *inner, st1, (fi - 2) as u64).ok);
                            bc_spec::fuel::lemma_is_assignment_stable(nodes, *inner, st1, (fi - 3) as u64, (fi - 2) as u64, fi);
                            si = st1;
                            fi = (fi - 3) as u64;
                        }
                    }
                    i = *inner;
                },
                _ => { return false; },
            }
        }
    }

    /// An expression statement (the specification's `exec_expr_stmt`): the value is printed
    /// unless it is an assignment.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn exec_expr_stmt(&mut self, code: &Rc<Code>, Ghost(n): Ghost<usize>, e: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::ExprStmt(e),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_rc(*code, nodes)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes);
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let ghost j = e;
        let v = match self.eval_ref(code, e, Ghost(nodes), Ghost(st)) {
            Ok(v) => v,
            Err(err) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(err), *self, exec_node(nodes, n, st, f), d) by {
                            assert(done(ev(nodes, j, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(err);
            },
        };
        let ghost f0 = choose|f: u64| f < u64::MAX && done(ev(nodes, e, st, f));
        let assignment = Self::is_assignment_ref(code, e, Ghost(nodes), Ghost(st), Ghost(f0));
        let ghost e1 = *self;
        if !assignment {
            let mut text = v.format_bytes(self.obase);
            text.push(10);
            self.stdout_writer.write_bytes(&text);
            self.stdout_writer.flush_out();
        }
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(done(x));
                    let g = (f - 2) as u64;
                    assert(g < u64::MAX && done(ev(nodes, e, st, g)));
                    let f1 = choose|f: u64| f < u64::MAX && done(ev(nodes, e, st, f));
                    assert(f1 == f0);
                    if f0 <= g { lemma_ev_mono(nodes, e, st, f0, g); } else { lemma_ev_mono(nodes, e, st, g, f0); }
                    let m = if f0 <= g { f0 } else { g };
                    bc_spec::fuel::lemma_is_assignment_stable(nodes, e, st, m, (f0 + 1) as u64, (f - 1) as u64);
                    if !assignment {
                        axiom_bigint_size(&v.coeff);
                        lemma_mag_bounds(x.val.mag);
                        lemma_format_num(x.val, x.st.obase);
                    }
                }
            }
        }
        Ok(())
    }

    /// `return` and `return (e)` (the specification's `exec_return`).
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn exec_return(&mut self, code: &Rc<Code>, Ghost(n): Ghost<usize>, v: Option<usize>, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::Return(v),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_rc(*code, nodes)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes);
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let ghost j = match v { Some(e) => e, None => 0usize };
        match v {
            Some(e) => {
                let x = match self.eval_ref(code, e, Ghost(nodes), Ghost(st)) {
                    Ok(x) => x,
                    Err(err) => {
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(err), *self, exec_node(nodes, n, st, f), d) by {
                                    assert(done(ev(nodes, j, st, (f - 2) as u64)));
                                }
                            }
                        }
                        return Err(err);
                    },
                };
                self.return_value = x;
            },
            None => {
                self.return_value = BCNum::zero();
            },
        }
        self.return_flag = true;
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {
                    if v is Some {
                        assert(done(ev(nodes, j, st, (f - 2) as u64)));
                    }
                }
            }
        }
        Ok(())
    }

    /// `if (c) s` (the specification's `exec_if`).
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn exec_if(&mut self, code: &Rc<Code>, Ghost(n): Ghost<usize>, c: usize, b: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::If(c, b),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_rc(*code, nodes)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes);
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let ghost (jc, jb) = (c, b);
        let x = match self.eval_ref(code, c, Ghost(nodes), Ghost(st)) {
            Ok(x) => x,
            Err(err) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(err), *self, exec_node(nodes, n, st, f), d) by {
                            assert(done(ev(nodes, jc, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(err);
            },
        };
        let ghost fc = choose|f: u64| done(#[trigger] ev(nodes, jc, st, f));
        let ghost xc = ev(nodes, jc, st, fc);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, jc, st, f)) implies ev(nodes, jc, st, f) == xc by {
                    if fc <= f { lemma_ev_mono(nodes, jc, st, fc, f); } else { lemma_ev_mono(nodes, jc, st, f, fc); }
                }
            }
        }
        if x.is_zero() {
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {
                        assert(done(ev(nodes, jc, st, (f - 2) as u64)));
                        lemma_is_zero_mag(xc.val.mag);
                    }
                }
            }
            return Ok(());
        }
        let ghost e1 = *self;
        let r = self.exec_ref(code, b, Ghost(nodes), Ghost(xc.st));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(r, *self, exec_node(nodes, n, st, f), d) by {
                    assert(done(ev(nodes, jc, st, (f - 2) as u64)));
                    assert(r_result(Ok(x), e1, xc, d));
                    assert(r_state(e1, xc.st));
                    lemma_is_zero_mag(xc.val.mag);
                    assert(done(exec(nodes, jb, xc.st, (f - 2) as u64)));
                }
            }
        }
        r
    }

    /// The loop of `while` (no `post`) and `for` (the specification's `exec_loop`): after the
    /// body, a pending `break` or `return` ends the loop and `break` is cleared.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(30)]
    #[allow(
        clippy::too_many_arguments,
        reason = "five of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn exec_loop_ref(&mut self, code: &Rc<Code>, c: usize, post: Option<usize>, b: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(jp): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            ({
                let has_post = post is Some;
                (r_state(*old(self), st) && r_rc(*code, nodes)
                    && (has_post ==> post->Some_0 == jp)) ==> forall|f: u64|
                    done(#[trigger] bc_spec::eval::exec_loop(nodes, c, jp, has_post, b, st, f))
                        ==> r_unit(r, *final(self), bc_spec::eval::exec_loop(nodes, c, jp, has_post, b, st, f), old(self).eval_depth)
            }),
    {
        let ghost d = self.eval_depth;
        let ghost has_post = post is Some;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes)
            && (has_post ==> post->Some_0 == jp);
        let ghost (jc, jb) = (c, b);
        let ghost fin = exists|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f));
        let ghost mut sk = st;
        let ghost mut k: int = 0;
        loop
            invariant
                self.inv(),
                self.eval_depth == d,
                d == old(self).eval_depth,
                has_post == (post is Some),
                hyp == (r_state(*old(self), st) && r_rc(*code, nodes)
                    && (has_post ==> post->Some_0 == jp)),
                jc == c && jb == b,
                k >= 0,
                fin == exists|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)),
                hyp && fin ==> r_state(*self, sk),
                hyp ==> forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) ==> f as int > k
                    && bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, sk, (f - k) as u64),
        {
            let ghost s0 = sk;
            let ghost e0 = *self;
            let cv = match self.eval_ref(code, c, Ghost(nodes), Ghost(s0)) {
                Ok(cv) => cv,
                Err(err) => {
                    proof {
                        if hyp {
                            assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Err(err), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                                assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                            }
                        }
                    }
                    return Err(err);
                },
            };
            let ghost e1 = *self;
            let ghost fc = choose|f: u64| done(#[trigger] ev(nodes, jc, s0, f));
            let ghost xc = ev(nodes, jc, s0, fc);
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] ev(nodes, jc, s0, f)) implies ev(nodes, jc, s0, f) == xc by {
                        if fc <= f { lemma_ev_mono(nodes, jc, s0, fc, f); } else { lemma_ev_mono(nodes, jc, s0, f, fc); }
                    }
                }
            }
            if cv.is_zero() || self.quit_flag {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Ok(()), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                            assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                            lemma_is_zero_mag(xc.val.mag);
                        }
                    }
                }
                return Ok(());
            }
            let rb = self.exec_ref(code, b, Ghost(nodes), Ghost(xc.st));
            if let Err(err) = rb {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Err(err), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                            assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                            lemma_is_zero_mag(xc.val.mag);
                            assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                        }
                    }
                }
                return Err(err);
            }
            let ghost fb = choose|f: u64| done(#[trigger] exec(nodes, jb, xc.st, f));
            let ghost xb = exec(nodes, jb, xc.st, fb);
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec(nodes, jb, xc.st, f)) implies exec(nodes, jb, xc.st, f) == xb by {
                        if fb <= f { lemma_exec_mono(nodes, jb, xc.st, fb, f); } else { lemma_exec_mono(nodes, jb, xc.st, f, fb); }
                    }
                }
            }
            let ghost e2 = *self;
            let (should_break, next_break) = verified_loop_post_body_action(self.break_flag, self.return_flag, self.quit_flag);
            self.break_flag = next_break;
            let ghost st2 = bc_spec::eval::with_flags(xb.st, false, xb.st.ret, xb.st.ret_val);
            if should_break {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Ok(()), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                            assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                            lemma_is_zero_mag(xc.val.mag);
                            assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                        }
                    }
                }
                return Ok(());
            }
            #[allow(clippy::single_match, reason = "the `None` arm holds the proof that the loop state advances")]
            match post {
                Some(p) => {
                    let ghost e3 = *self;
                    let rp = self.eval_ref(code, p, Ghost(nodes), Ghost(st2));
                    if let Err(err) = rp {
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Err(err), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                                    assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                                    lemma_is_zero_mag(xc.val.mag);
                                    assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                                    assert(r_state(e2, xb.st));
                                    assert(done(ev(nodes, jp, st2, (f - k - 1) as u64)));
                                }
                            }
                        }
                        return Err(err);
                    }
                    let ghost fp = choose|f: u64| done(#[trigger] ev(nodes, jp, st2, f));
                    let ghost xp = ev(nodes, jp, st2, fp);
                    proof {
                        if hyp {
                            assert forall|f: u64| done(#[trigger] ev(nodes, jp, st2, f)) implies ev(nodes, jp, st2, f) == xp by {
                                if fp <= f { lemma_ev_mono(nodes, jp, st2, fp, f); } else { lemma_ev_mono(nodes, jp, st2, f, fp); }
                            }
                            let sk2 = xp.st;
                            assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies f as int > k + 1
                                && bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, sk2, (f - k - 1) as u64) by {
                                assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                                lemma_is_zero_mag(xc.val.mag);
                                assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                                assert(r_state(e2, xb.st));
                                    assert(done(ev(nodes, jp, st2, (f - k - 1) as u64)));
                                if f as int <= k + 1 {
                                    assert(bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, sk2, 0) == bc_spec::eval::er_fuel(sk2));
                                }
                            }
                            if fin {
                                let ff = choose|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f));
                                let g = (ff - k) as u64;
                                assert(bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, ff) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, s0, g));
                                assert(done(ev(nodes, jc, s0, (g - 1) as u64)));
                                assert(r_state(e0, s0));
                                assert(r_state(e1, xc.st));
                                lemma_is_zero_mag(xc.val.mag);
                                assert(done(exec(nodes, jb, xc.st, (g - 1) as u64)));
                                assert(r_state(e2, xb.st));
                                assert(r_state(e3, st2));
                                assert(done(ev(nodes, jp, st2, (g - 1) as u64)));
                                assert(r_state(*self, sk2));
                            }
                            sk = sk2;
                        }
                    }
                },
                None => {
                    proof {
                        if hyp {
                            assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies f as int > k + 1
                                && bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st2, (f - k - 1) as u64) by {
                                assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                                lemma_is_zero_mag(xc.val.mag);
                                assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                                if f as int <= k + 1 {
                                    assert(bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st2, 0) == bc_spec::eval::er_fuel(st2));
                                }
                            }
                            if fin {
                                let ff = choose|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f));
                                let g = (ff - k) as u64;
                                assert(bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, ff) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, s0, g));
                                assert(done(ev(nodes, jc, s0, (g - 1) as u64)));
                                assert(r_state(e0, s0));
                                assert(r_state(e1, xc.st));
                                lemma_is_zero_mag(xc.val.mag);
                                assert(done(exec(nodes, jb, xc.st, (g - 1) as u64)));
                                assert(r_state(e2, xb.st));
                                assert(r_state(*self, st2));
                            }
                            sk = st2;
                        }
                    }
                },
            }
            proof {
                k = k + 1;
            }
        }
    }

    /// `for (i; c; p) s` (the specification's `exec_for`).
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(
        clippy::too_many_arguments,
        reason = "four of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn exec_for_ref(&mut self, code: &Rc<Code>, Ghost(n): Ghost<usize>, init: usize, c: usize, p: usize, b: usize, Ghost(nodes): Ghost<SpecNodes>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            n < code.nodes@.len(),
            code.nodes@[n as int] == PNode::For(init, c, p, b),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_rc(*code, nodes)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_rc(*code, nodes);
        proof { if hyp && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        let ghost (ji, jc, jp, jb) = (init, c, p, b);
        if let Err(err) = self.eval_ref(code, init, Ghost(nodes), Ghost(st)) {
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(err), *self, exec_node(nodes, n, st, f), d) by {
                        assert(done(ev(nodes, ji, st, (f - 2) as u64)));
                    }
                }
            }
            return Err(err);
        }
        let ghost fi = choose|f: u64| done(#[trigger] ev(nodes, ji, st, f));
        let ghost xi = ev(nodes, ji, st, fi);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, ji, st, f)) implies ev(nodes, ji, st, f) == xi by {
                    if fi <= f { lemma_ev_mono(nodes, ji, st, fi, f); } else { lemma_ev_mono(nodes, ji, st, f, fi); }
                }
            }
        }
        let ghost e1 = *self;
        let r = self.exec_loop_ref(code, c, Some(p), b, Ghost(nodes), Ghost(jp), Ghost(xi.st));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(r, *self, exec_node(nodes, n, st, f), d) by {
                    assert(done(ev(nodes, ji, st, (f - 2) as u64)));
                    assert(r_state(e1, xi.st));
                    assert(done(bc_spec::eval::exec_loop(nodes, jc, jp, true, jb, xi.st, (f - 2) as u64)));
                }
            }
        }
        r
    }
}

} // verus!
