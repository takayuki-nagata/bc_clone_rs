// SPDX-License-Identifier: MIT

//! Statement execution (the specification's `exec`): blocks, `if`, loops and `return`.

use super::*;

verus! {

impl Evaluator {
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
