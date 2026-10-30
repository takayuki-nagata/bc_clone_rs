// SPDX-License-Identifier: MIT

//! Expression evaluation (the specification's `ev`): operators, names, constants,
//! assignments and `++`/`--`.

use super::*;

verus! {

impl Evaluator {
    /// `try_evaluate` with the arena subtree `n` of `nodes` and the specification state `st` it
    /// corresponds to: one nesting level around `eval_node_ref` (the specification's `ev`).
    /// Whenever the specification finishes (with any fuel), the result corresponds to it.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_ref(
        &mut self,
        node: &Expr,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(n): Ghost<usize>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(*node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev(nodes, n, st, f)) ==> r_result(r, *final(self), ev(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(*node, nodes, n);
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_depth) {
            let r = Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
            proof {
                if hyp {
                    assert(with_depth(st, d as u64) == st);
                    assert forall|f: u64| done(#[trigger] ev(nodes, n, st, f)) implies r_result(r, *self, ev(nodes, n, st, f), d) by {}
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
        let r = self.eval_node_ref(node, Ghost(nodes), Ghost(n), Ghost(st1));
        let ghost mid = *self;
        self.eval_depth -= 1;
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, n, st, f)) implies r_result(r, *self, ev(nodes, n, st, f), d) by {
                    let x = ev_node(nodes, n, st1, (f - 1) as u64);
                    assert(done(x));
                    assert(r_result(r, mid, x, (d + 1) as usize));
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

    /// `evaluate_node` (the specification's `ev_node`): one step of expression evaluation.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_node_ref(
        &mut self,
        node: &Expr,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(n): Ghost<usize>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(*node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        match node {
            Expr::RegisterAccess(reg) => self.eval_register(*reg, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Number(t) => self.eval_number(t, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Variable(name) => self.eval_variable(name, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::AssignOp(op, target, value) => self.eval_assign(Ghost(*node), *op, target, value, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Update(increment, prefix, target) => self.eval_update(Ghost(*node), *increment, *prefix, target, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::ArrayAccess(name, index) => self.eval_array(Ghost(*node), name, index, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Paren(inner) => self.eval_paren(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Negate(inner) => self.eval_negate(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::LengthCall(inner) => self.eval_length(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::ScaleCall(inner) => self.eval_scale_of(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::SqrtCall(inner) => self.eval_sqrt(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::BinaryOp(op, left, right) => self.eval_binary(Ghost(*node), *op, left, right, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::RelationalOp(op, left, right) => self.eval_rel(Ghost(*node), *op, left, right, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Call(name, args) => self.eval_call(Ghost(*node), name, args, Ghost(nodes), Ghost(n), Ghost(st)),
        }
    }

    pub(crate) fn eval_register(&mut self, reg: Register, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r is Ok && r->Ok_0.scale == 0,
            (r_state(*old(self), st) && r_expr(Expr::RegisterAccess(reg), nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let value = match reg {
            Register::Scale => self.scale,
            Register::Ibase => self.ibase,
            Register::Obase => self.obase,
        };
        let v = BCNum::new(big_from_usize(value), 0);
        proof {
            let x = num_u64(reg_get(st, reg_code(reg)) as u64);
            lemma_u64_mag(reg_get(st, reg_code(reg)) as u64);
        }
        Ok(v)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_paren(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::Paren(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Paren(j) => j, _ => 0usize } } else { 0usize };
        let r = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(r, *self, ev_node(nodes, n, st, f), d) by {
                    assert(f >= 1);
                    assert(ev_node(nodes, n, st, f) == ev(nodes, j, st, (f - 1) as u64));
                }
            }
        }
        r
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_negate(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::Negate(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Neg(j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(f >= 2);
                            assert(done(x));
                        }
                    }
                }
                return Err(e);
            },
        };
        let w = BCNum::new(big_neg(&v.coeff), v.scale);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(w), *self, ev_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(f >= 2);
                    assert(done(x));
                    lemma_is_zero_mag(x.val.mag);
                    assert(r_num(w, negate(x.val)));
                }
            }
        }
        Ok(w)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_length(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::LengthCall(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Length(j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(f >= 2);
                            assert(done(x));
                        }
                    }
                }
                return Err(e);
            },
        };
        let w = v.length();
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(w), *self, ev_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(f >= 2);
                    assert(done(x));
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
        }
        Ok(w)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_scale_of(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::ScaleCall(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::ScaleOf(j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(f >= 2);
                            assert(done(x));
                        }
                    }
                }
                return Err(e);
            },
        };
        let w = v.scale_func();
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(w), *self, ev_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(f >= 2);
                    assert(done(x));
                    lemma_num_scale(x.val);
                    assert(r_num(w, num_scale(x.val)));
                }
            }
        }
        Ok(w)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_sqrt(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::SqrtCall(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Sqrt(j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(f >= 2);
                            assert(done(x));
                        }
                    }
                }
                return Err(e);
            },
        };
        let r1 = v.try_sqrt(self.scale);
        let r = match r1 {
            Ok(w) => Ok(w),
            Err(k) => Err(BcError::Runtime { kind: k, func: None }),
        };
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(r, *self, ev_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(f >= 2);
                    assert(done(x));
                    let a = x.val;
                    lemma_num_sqrt(a, x.st.scale);
                    assert(with_depth(x.st, d as u64) == x.st);
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
        }
        r
    }

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


    /// `l <op> r` (the specification's `ev_binary`): both operands are evaluated, left first,
    /// before the operator applies.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn eval_binary(&mut self, Ghost(node): Ghost<Expr>, op: BinOp, left: &Expr, right: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::BinaryOp(op, Box::new(*left), Box::new(*right)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        let ghost (ja, jb) = if n < nodes.len() {
            match nodes[n as int] {
                Node::Binary(_, a, b) => (a, b),
                Node::Rel(_, a, b) => (a, b),
                _ => (0usize, 0usize),
            }
        } else {
            (0usize, 0usize)
        };
        let ra = self.eval_ref(left, Ghost(nodes), Ghost(ja), Ghost(st));
        let ghost fa = choose|f: u64| done(#[trigger] ev(nodes, ja, st, f));
        let ghost xa = ev(nodes, ja, st, fa);
        let l = match ra {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let rb = self.eval_ref(right, Ghost(nodes), Ghost(jb), Ghost(xa.st));
        let ghost fb = choose|f: u64| done(#[trigger] ev(nodes, jb, xa.st, f));
        let ghost xb = ev(nodes, jb, xa.st, fb);
        // Whatever fuel finishes, the operands' results are xa and xb.
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, ja, st, f)) implies ev(nodes, ja, st, f) == xa by {
                    if fa <= f { lemma_ev_mono(nodes, ja, st, fa, f); } else { lemma_ev_mono(nodes, ja, st, f, fa); }
                }
                assert forall|f: u64| done(#[trigger] ev(nodes, jb, xa.st, f)) implies ev(nodes, jb, xa.st, f) == xb by {
                    if fb <= f { lemma_ev_mono(nodes, jb, xa.st, fb, f); } else { lemma_ev_mono(nodes, jb, xa.st, f, fb); }
                }
            }
        }
        let r = match rb {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                            assert(done(ev(nodes, jb, xa.st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let res = self.arith_ref(op, &l, &r, Ghost(xa.val), Ghost(xb.val), Ghost(xb.st));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(res, *self, ev_node(nodes, n, st, f), d) by {
                    assert(f >= 2);
                    assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                    assert(done(ev(nodes, jb, xa.st, (f - 2) as u64)));
                }
            }
        }
        res
    }

    /// A relational expression (the specification's `ev_rel`): 1 if it holds, else 0.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn eval_rel(&mut self, Ghost(node): Ghost<Expr>, op: RelOp, left: &Expr, right: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::RelationalOp(op, Box::new(*left), Box::new(*right)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        let ghost (ja, jb) = if n < nodes.len() {
            match nodes[n as int] {
                Node::Binary(_, a, b) => (a, b),
                Node::Rel(_, a, b) => (a, b),
                _ => (0usize, 0usize),
            }
        } else {
            (0usize, 0usize)
        };
        let ra = self.eval_ref(left, Ghost(nodes), Ghost(ja), Ghost(st));
        let ghost fa = choose|f: u64| done(#[trigger] ev(nodes, ja, st, f));
        let ghost xa = ev(nodes, ja, st, fa);
        let l = match ra {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let rb = self.eval_ref(right, Ghost(nodes), Ghost(jb), Ghost(xa.st));
        let ghost fb = choose|f: u64| done(#[trigger] ev(nodes, jb, xa.st, f));
        let ghost xb = ev(nodes, jb, xa.st, fb);
        // Whatever fuel finishes, the operands' results are xa and xb.
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, ja, st, f)) implies ev(nodes, ja, st, f) == xa by {
                    if fa <= f { lemma_ev_mono(nodes, ja, st, fa, f); } else { lemma_ev_mono(nodes, ja, st, f, fa); }
                }
                assert forall|f: u64| done(#[trigger] ev(nodes, jb, xa.st, f)) implies ev(nodes, jb, xa.st, f) == xb by {
                    if fb <= f { lemma_ev_mono(nodes, jb, xa.st, fb, f); } else { lemma_ev_mono(nodes, jb, xa.st, f, fb); }
                }
            }
        }
        let r = match rb {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                            assert(done(ev(nodes, jb, xa.st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let ord = l.cmp_val(&r);
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
            if hyp {
                lemma_one_mag();
                lemma_u64_mag(0);
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(v), *self, ev_node(nodes, n, st, f), d) by {
                    assert(f >= 2);
                    assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                    assert(done(ev(nodes, jb, xa.st, (f - 2) as u64)));
                    lemma_num_cmp(xa.val, xb.val);
                    assert(holds == rel_holds(rel_code(op), num_cmp(xa.val, xb.val)));
                }
            }
        }
        Ok(v)
    }

    /// The value of a variable (the specification's `var_get`).
    pub(crate) fn eval_variable(&mut self, name: &String, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r is Ok && r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(Expr::Variable(*name), nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let v = self.var_get(name);
        proof {
            if r_state(*self, st) && r_expr(Expr::Variable(*name), nodes, n) {
                let nm = text_view(*name);
                lemma_var_get(st.vars, nm);
                if self.variables@.contains_key(*name) {
                    let s = var_lookup(st.vars, nm)->Some_0;
                    assert(r_stack(self.variables@[*name]@, s));
                    if s.len() > 0 {
                        assert(r_num(self.variables@[*name]@[s.len() - 1], s[s.len() - 1]));
                    }
                } else {
                    lemma_var_absent(self.variables@, st.vars, *name);
                }
                assert(r_num(v, var_get(st.vars, nm)));
            }
        }
        Ok(v)
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

    /// An array element (the specification's `ev_array`): the subscript is evaluated first.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_array(&mut self, Ghost(node): Ghost<Expr>, name: &String, index: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::ArrayAccess(*name, Box::new(*index)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Array(_, j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(index, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, j, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let i = match Self::array_index_ref(name, &v) {
            Ok(i) => i,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(done(x));
                            assert(r_num(v, x.val));
                            assert(with_depth(x.st, d as u64) == x.st);
                        }
                    }
                }
                return Err(e);
            },
        };
        let w = self.arr_get(name, i);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(w), *self, ev_node(nodes, n, st, f), d) by {
                    assert(f >= 2);
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(done(x));
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
        }
        Ok(w)
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

    /// The value of a numeric constant (the specification's `ev_node` for `Node::Number`).
    pub(crate) fn eval_number(&mut self, t: &String, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(Expr::Number(*t), nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        self.literal_ref(t, Ghost(st))
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

    /// Resolves an assignment target (the specification's `resolve`), evaluating an array
    /// subscript exactly once.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn resolve_ref(&mut self, target: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<Place, BcError>)
        requires
            old(self).inv(),
            named(*target),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_expr(*target, nodes, n)) ==> forall|f: u64|
                done(#[trigger] resolve(nodes, n, st, f).r) ==> ({
                    let pr = resolve(nodes, n, st, f);
                    match r {
                        Ok(p) => pr.r.ok && r_place(p, pr.place) && r_state(*final(self), pr.r.st),
                        Err(e) => !pr.r.ok && r_err(e, pr.r.err) && r_state(*final(self), with_depth(pr.r.st, old(self).eval_depth as u64)),
                    }
                }),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(*target, nodes, n);
        match target {
            Expr::Variable(name) => Ok(Place::Variable(name.clone())),
            Expr::RegisterAccess(reg) => Ok(Place::Register(*reg)),
            Expr::ArrayAccess(name, index) => {
                let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Array(_, j) => j, _ => 0usize } } else { 0usize };
                let v = match self.eval_ref(index, Ghost(nodes), Ghost(j), Ghost(st)) {
                    Ok(v) => v,
                    Err(e) => {
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] resolve(nodes, n, st, f).r) implies {
                                    let pr = resolve(nodes, n, st, f);
                                    !pr.r.ok && r_err(e, pr.r.err) && r_state(*self, with_depth(pr.r.st, d as u64))
                                } by {
                                    assert(done(ev(nodes, j, st, (f - 1) as u64)));
                                }
                            }
                        }
                        return Err(e);
                    },
                };
                let i = match Self::array_index_ref(name, &v) {
                    Ok(i) => i,
                    Err(e) => {
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] resolve(nodes, n, st, f).r) implies {
                                    let pr = resolve(nodes, n, st, f);
                                    !pr.r.ok && r_err(e, pr.r.err) && r_state(*self, with_depth(pr.r.st, d as u64))
                                } by {
                                    let x = ev(nodes, j, st, (f - 1) as u64);
                                    assert(done(x));
                                    assert(r_num(v, x.val));
                                    assert(with_depth(x.st, d as u64) == x.st);
                                }
                            }
                        }
                        return Err(e);
                    },
                };
                let p = Place::Element(name.clone(), i);
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] resolve(nodes, n, st, f).r) implies {
                            let pr = resolve(nodes, n, st, f);
                            pr.r.ok && r_place(p, pr.place) && r_state(*self, pr.r.st)
                        } by {
                            let x = ev(nodes, j, st, (f - 1) as u64);
                            assert(done(x));
                            assert(r_num(v, x.val));
                            lemma_array_index_value(x.val);
                        }
                    }
                }
                Ok(p)
            },
            _ => Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None }),
        }
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

    /// An assignment (the specification's `ev_assign`): the target is resolved before the value
    /// is evaluated (as in GNU bc, `a[i++] = i` stores into `a[0]`), and the value of the
    /// assignment is the value assigned, even when a register clamps it. POSIX: a single digit
    /// assigned to `ibase` or `obase` is read as hexadecimal.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(50)]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn eval_assign(&mut self, Ghost(node): Ghost<Expr>, op: AssignOp, target: &Expr, value: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::AssignOp(op, Box::new(*target), Box::new(*value)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        if !(matches!(target, Expr::Variable(_)) || matches!(target, Expr::ArrayAccess(..)) || matches!(target, Expr::RegisterAccess(_))) {
            // Not a named expression: the parser never builds this, and `r_expr` excludes it.
            // The value is computed as for a variable, and nothing is stored.
            return match op {
                AssignOp::Assign => self.eval_ref(value, Ghost(nodes), Ghost(0usize), Ghost(st)),
                AssignOp::Compound(bin) => {
                    let old_val = self.eval_ref(target, Ghost(nodes), Ghost(0usize), Ghost(st))?;
                    let rhs = self.eval_ref(value, Ghost(nodes), Ghost(0usize), Ghost(st))?;
                    self.arith_ref(bin, &old_val, &rhs, Ghost(arbitrary()), Ghost(arbitrary()), Ghost(st))
                },
            };
        }
        let ghost (jt, jv) = if n < nodes.len() { match nodes[n as int] { Node::Assign(_, a, b) => (a, b), _ => (0usize, 0usize) } } else { (0usize, 0usize) };
        let place = match self.resolve_ref(target, Ghost(nodes), Ghost(jt), Ghost(st)) {
            Ok(p) => p,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                        }
                    }
                }
                return Err(e);
            },
        };
        let ghost fr = choose|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r);
        let ghost pr = resolve(nodes, jt, st, fr);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r) implies resolve(nodes, jt, st, f) == pr by {
                    if fr <= f { lemma_resolve_mono(nodes, jt, st, fr, f); } else { lemma_resolve_mono(nodes, jt, st, f, fr); }
                }
            }
        }
        let ghost st1 = pr.r.st;
        let ghost code = assign_code(op);
        let val = match self.assign_value(op, &place, value, Ghost(nodes), Ghost(jv), Ghost(pr.place), Ghost(st1)) {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                            assert(done(assign_x(nodes, pr.place, code, jv, st1, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let ghost fx = choose|f: u64| done(#[trigger] assign_x(nodes, pr.place, code, jv, st1, f));
        let ghost x = assign_x(nodes, pr.place, code, jv, st1, fx);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] assign_x(nodes, pr.place, code, jv, st1, f)) implies assign_x(nodes, pr.place, code, jv, st1, f) == x by {
                    if fx <= f { lemma_assign_x_mono(nodes, pr.place, code, jv, st1, fx, f); } else { lemma_assign_x_mono(nodes, pr.place, code, jv, st1, f, fx); }
                }
            }
        }
        let r = val.copy();
        let _ = self.store_ref(place, val, Ghost(pr.place), Ghost(x.st), Ghost(x.val));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(r), *self, ev_node(nodes, n, st, f), d) by {
                    assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                    assert(done(assign_x(nodes, pr.place, code, jv, st1, (f - 2) as u64)));
                }
            }
        }
        Ok(r)
    }

    /// The value an assignment stores (`assign_x`): a single hexadecimal digit for `ibase` or
    /// `obase`, the value of `=`, or the old value combined with the value of `op=`.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(
        clippy::too_many_arguments,
        reason = "four of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn assign_value(&mut self, op: AssignOp, place: &Place, value: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(jv): Ghost<usize>, Ghost(sp): Ghost<SpecPlace>, Ghost(st1): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st1) && r_place(*place, sp) && r_expr(*value, nodes, jv)) ==> forall|f: u64|
                done(#[trigger] assign_x(nodes, sp, assign_code(op), jv, st1, f))
                    ==> r_result(r, *final(self), assign_x(nodes, sp, assign_code(op), jv, st1, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st1) && r_place(*place, sp) && r_expr(*value, nodes, jv);
        let ghost code = assign_code(op);
        let hex = match (place, op, value) {
            (Place::Register(Register::Ibase), AssignOp::Assign, Expr::Number(digits))
            | (Place::Register(Register::Obase), AssignOp::Assign, Expr::Number(digits)) => {
                let b = digits.as_str().as_bytes();
                if b.len() == 1 { Some(verified_hex_char_val(b[0])) } else { None }
            },
            _ => None,
        };
        if let Some(h) = hex {
            let v = BCNum::new(big_from_usize(h), 0);
            proof {
                if hyp {
                    lemma_u64_mag(h as u64);
                    assert(with_depth(st1, d as u64) == st1);
                }
            }
            return Ok(v);
        }
        let ghost fv = choose|f: u64| done(#[trigger] ev(nodes, jv, st1, f));
        let ghost xv = ev(nodes, jv, st1, fv);
        let old_val = match op {
            AssignOp::Assign => None,
            AssignOp::Compound(_) => Some(self.load_ref(place, Ghost(sp), Ghost(st1))),
        };
        let rhs = match self.eval_ref(value, Ghost(nodes), Ghost(jv), Ghost(st1)) {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] assign_x(nodes, sp, code, jv, st1, f)) implies r_result(Err(e), *self, assign_x(nodes, sp, code, jv, st1, f), d) by {
                            assert(done(ev(nodes, jv, st1, f)));
                        }
                    }
                }
                return Err(e);
            },
        };
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, jv, st1, f)) implies ev(nodes, jv, st1, f) == xv by {
                    if fv <= f { lemma_ev_mono(nodes, jv, st1, fv, f); } else { lemma_ev_mono(nodes, jv, st1, f, fv); }
                }
            }
        }
        match (op, old_val) {
            (AssignOp::Compound(bin), Some(old_v)) => {
                let res = self.arith_ref(bin, &old_v, &rhs, Ghost(bc_spec::eval::load(st1, sp)), Ghost(xv.val), Ghost(xv.st));
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] assign_x(nodes, sp, code, jv, st1, f)) implies r_result(res, *self, assign_x(nodes, sp, code, jv, st1, f), d) by {
                            assert(done(ev(nodes, jv, st1, f)));
                        }
                    }
                }
                res
            },
            _ => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] assign_x(nodes, sp, code, jv, st1, f)) implies r_result(Ok(rhs), *self, assign_x(nodes, sp, code, jv, st1, f), d) by {
                            assert(done(ev(nodes, jv, st1, f)));
                        }
                    }
                }
                Ok(rhs)
            },
        }
    }

    /// `++` / `--` (the specification's `ev_update`): a prefix form gives the stored value, a
    /// postfix form the old one.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(20)]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    pub(crate) fn eval_update(&mut self, Ghost(node): Ghost<Expr>, increment: bool, prefix: bool, target: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::Update(increment, prefix, Box::new(*target)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n);
        if !(matches!(target, Expr::Variable(_)) || matches!(target, Expr::ArrayAccess(..)) || matches!(target, Expr::RegisterAccess(_))) {
            // Not a named expression: the parser never builds this, and `r_expr` excludes it.
            // The value is computed as for a variable, and nothing is stored.
            let old_val = self.eval_ref(target, Ghost(nodes), Ghost(0usize), Ghost(st))?;
            let one = BCNum::new(big_from_usize(1), 0);
            let new_val = if increment { old_val.add(&one) } else { old_val.sub(&one) };
            return Ok(if prefix { new_val } else { old_val });
        }
        let ghost jt = if n < nodes.len() { match nodes[n as int] { Node::Update(_, _, a) => a, _ => 0usize } } else { 0usize };
        let place = match self.resolve_ref(target, Ghost(nodes), Ghost(jt), Ghost(st)) {
            Ok(p) => p,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                        }
                    }
                }
                return Err(e);
            },
        };
        let ghost fr = choose|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r);
        let ghost pr = resolve(nodes, jt, st, fr);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r) implies resolve(nodes, jt, st, f) == pr by {
                    if fr <= f { lemma_resolve_mono(nodes, jt, st, fr, f); } else { lemma_resolve_mono(nodes, jt, st, f, fr); }
                }
            }
        }
        let ghost st1 = pr.r.st;
        let ghost sold = bc_spec::eval::load(st1, pr.place);
        let old_val = self.load_ref(&place, Ghost(pr.place), Ghost(st1));
        let step = BCNum::new(big_from_usize(1), 0);
        let new_val = if increment { old_val.add(&step) } else { old_val.sub(&step) };
        let ghost snew = if increment { num_add(sold, one_num()) } else { num_sub(sold, one_num()) };
        proof {
            if hyp && exists|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r) {
                lemma_one_mag();
                if increment { lemma_num_add(sold, one_num()); } else { lemma_num_sub(sold, one_num()); }
            }
        }
        let stored = self.store_ref(place, new_val, Ghost(pr.place), Ghost(st1), Ghost(snew));
        let r = if prefix { stored } else { old_val };
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(r), *self, ev_node(nodes, n, st, f), d) by {
                    assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                }
            }
        }
        Ok(r)
    }
}

} // verus!
