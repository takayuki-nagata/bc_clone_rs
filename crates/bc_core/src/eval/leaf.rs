// SPDX-License-Identifier: MIT

//! The leaves of the machine: the forms that `machine.rs` does not split into frames
//! (`leaf_node`, `leaf_stmt_node`), because they need no sub-computation.
//!
//! `eval_leaf_ref` evaluates a register, a constant or a variable, and `exec_leaf_ref` runs a
//! string, `break`, `return` without a value, a function definition, or any statement while a
//! `break`, `return` or `quit` is pending. Their theorems are those of the specification's
//! `ev_node` and `exec_node` on such a node. The machine calls them only through `leaf_result`
//! and `leaf_stmt`.

use super::*;

verus! {

impl Evaluator {
    /// A statement that needs no sub-computation (the specification's `exec_node` on such a
    /// node): nothing runs while a `break`, `return` or `quit` is pending.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn exec_leaf_ref(
        &mut self,
        code: &Rc<Code>,
        n: usize,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            (old(self).break_flag || old(self).return_flag || old(self).quit_flag) || super::machine::leaf_stmt_node(*code, n),
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
            PNode::Return(None) => {
                self.return_value = BCNum::zero();
                self.return_flag = true;
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                    }
                }
                Ok(())
            },
            PNode::Define(decl) => {
                let name = &decl.name;
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

    /// The value of a register, a constant or a variable (the specification's `ev_node` on a
    /// leaf node). The machine never passes another node; one would give 0.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_leaf_ref(
        &mut self,
        code: &Rc<Code>,
        n: usize,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            super::machine::leaf_node(*code, n),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_rc(*code, nodes)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        proof { if r_rc(*code, nodes) && n < nodes.len() { assert(r_node(code.nodes@[n as int], nodes[n as int])); } }
        if n >= code.nodes.len() {
            return Ok(BCNum::zero());
        }
        match &code.nodes[n] {
            PNode::Reg(reg) => self.eval_register(*reg, Ghost(nodes), Ghost(n), Ghost(st)),
            PNode::Number(t) => self.eval_number(t, Ghost(nodes), Ghost(n), Ghost(st)),
            PNode::Var(name) => self.eval_variable(name, Ghost(nodes), Ghost(n), Ghost(st)),
            _ => Ok(BCNum::zero()),
        }
    }

    /// The value of register `reg` (the specification's `ev_node` for `Node::Reg`).
    pub(crate) fn eval_register(&mut self, reg: Register, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r is Ok && r->Ok_0.scale == 0,
            (r_state(*old(self), st) && n < nodes.len() && nodes[n as int] == Node::Reg(reg_code(reg))) ==> forall|f: u64|
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

    /// The value of a variable (the specification's `var_get`).
    pub(crate) fn eval_variable(&mut self, name: &String, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r is Ok && r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && n < nodes.len() && nodes[n as int] == Node::Var(text_view(*name))) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let v = self.var_get(name);
        proof {
            if r_state(*self, st) && n < nodes.len() && nodes[n as int] == Node::Var(text_view(*name)) {
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

    /// The value of a numeric constant (the specification's `ev_node` for `Node::Number`).
    pub(crate) fn eval_number(&mut self, t: &String, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && n < nodes.len() && nodes[n as int] == Node::Number(text_view(*t))) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        self.literal_ref(t, Ghost(st))
    }
}

} // verus!
