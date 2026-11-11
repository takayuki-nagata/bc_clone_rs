// SPDX-License-Identifier: MIT

//! Statements (the specification's `p_statement` to `p_return`): one nesting level, then
//! strings, `break`, `return`, blocks, expression statements, `if`, `while` and `for`.

use super::*;

verus! {

/// The diagnostic or description `break_outside`.
fn break_outside_text() -> (r: String)
    ensures
        text_view(r) == break_msg(),
{
    let m = [66u8, 114, 101, 97, 107, 32, 111, 117, 116, 115, 105, 100, 101, 32, 97, 32, 102, 111, 114, 47, 119, 104, 105, 108, 101];
    proof { assert(m@ =~= break_msg()); }
    ascii_string(m.as_slice())
}

/// The diagnostic or description `return_outside`.
fn return_outside_text() -> (r: String)
    ensures
        text_view(r) == return_msg(),
{
    let m = [82u8, 101, 116, 117, 114, 110, 32, 111, 117, 116, 115, 105, 100, 101, 32, 111, 102, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 46];
    proof { assert(m@ =~= return_msg()); }
    ascii_string(m.as_slice())
}

/// The diagnostic or description `comparison`.
fn comparison_text() -> (r: String)
    ensures
        text_view(r) == comparison_msg(),
{
    let m = [99u8, 111, 109, 112, 97, 114, 105, 115, 111, 110, 32, 105, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110];
    proof { assert(m@ =~= comparison_msg()); }
    ascii_string(m.as_slice())
}

/// The diagnostic or description `return_paren`.
fn return_paren_text() -> (r: String)
    ensures
        text_view(r) == return_paren_msg(),
{
    let m = [114u8, 101, 116, 117, 114, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 114, 101, 113, 117, 105, 114, 101, 115, 32, 112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 115];
    proof { assert(m@ =~= return_paren_msg()); }
    ascii_string(m.as_slice())
}

impl Parser {
    /// Adds a statement's node to the arena (the specification's `add_node`).
    pub(super) fn add_stmt(&mut self, pn: PNode, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(s0): Ghost<GState>, Ghost(s): Ghost<GState>, Ghost(n): Ghost<GNode>, Ghost(h): Ghost<u64>) -> (idx: usize)
        requires
            r_pc(*old(self), toks, cfg, s),
            r_node(pn, n),
            extends(s0.nodes, s.nodes),
            s0.nodes.len() <= 2 * s0.cur,
            s.cur > s0.cur,
            s.nodes.len() - s0.nodes.len() + 1 <= 2 * (s.cur - s0.cur),
            s.depth == s0.depth,
        ensures
            pushed(*old(self), *final(self), pn),
            ({
                let g = add_node(s, n, h);
                &&& g.ok
                &&& g.flag
                &&& g.node == idx
                &&& idx == s.nodes.len()
                &&& g.st.nodes.len() == s.nodes.len() + 1
                &&& g.st.nodes[g.node as int] == n
                &&& g.st.cur == s.cur
                &&& g.st.ext == s.ext
                &&& r_pc(*final(self), toks, cfg, g.st)
                &&& (s.cur < toks.len() ==> r_p(*final(self), toks, cfg, g.st))
                &&& extends(s.nodes, g.st.nodes)
                &&& r_sgrown(s0, g.st)
            }),
    {
        let idx = self.nodes.len();
        self.nodes.push(pn);
        proof {
            let g = add_node(s, n, h);
            assert(g.st.nodes =~= s.nodes.push(n));
            assert(cur_tok(toks, g.st) == cur_tok(toks, s));
            assert forall|i: int| 0 <= i < self.nodes@.len() implies #[trigger] r_node(self.nodes@[i], g.st.nodes[i]) by {
                if i < s.nodes.len() { assert(r_node(old(self).nodes@[i], s.nodes[i])); }
            }
        }
        idx
    }
}

impl Parser {
    /// Parses one statement as one level of nesting.
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn parse_statement(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_statement(toks, cfg, st, f)] pdone(p_statement(toks, cfg, st, f)) ==> p_statement(toks, cfg, st, f) == r.1@,
    {
        if !verified_nesting_within_limit(self.depth, 1, self.max_depth) {
            return (Err(self.too_deep_error(Ghost(toks), Ghost(cfg), Ghost(st))), Ghost(too_deep(st)));
        }
        let outer = self.depth;
        self.depth = outer + 1;
        let ghost st1 = st_set_depth(st, (st.depth + 1) as u64);
        proof { assert(cur_tok(toks, st1) == cur_tok(toks, st)); }
        let (res, Ghost(x)) = self.parse_statement_inner(Ghost(toks), Ghost(cfg), Ghost(st1));
        self.depth = outer;
        match res {
            Err(e) => {
                proof {
                    assert forall|f: u64| #![trigger p_statement(toks, cfg, st, f)] pdone(p_statement(toks, cfg, st, f)) implies p_statement(toks, cfg, st, f) == x by {
                        assert(f > 0);
                        assert(pdone(p_statement_inner(toks, cfg, st1, (f - 1) as u64)));
                    }
                }
                (Err(e), Ghost(x))
            },
            Ok(v) => {
                let ghost g = pr_node(st_set_depth(x.st, st.depth), x.node, x.h);
                proof {
                    assert(cur_tok(toks, g.st) == cur_tok(toks, x.st));
                    assert forall|f: u64| #![trigger p_statement(toks, cfg, st, f)] pdone(p_statement(toks, cfg, st, f)) implies p_statement(toks, cfg, st, f) == g by {
                        assert(f > 0);
                        assert(pdone(p_statement_inner(toks, cfg, st1, (f - 1) as u64)));
                    }
                }
                (Ok(v), Ghost(g))
            },
        }
    }

    /// Parses a loop body, tracking the loop nesting for `break`.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_loop_body(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_loop_body(toks, cfg, st, f)] pdone(p_loop_body(toks, cfg, st, f)) ==> p_loop_body(toks, cfg, st, f) == r.1@,
    {
        let outer = self.loop_depth;
        self.loop_depth = if outer < usize::MAX { outer + 1 } else { outer };
        let ghost st1 = st_set_loop(st, inc(st.loop_depth), st.in_function);
        proof { assert(cur_tok(toks, st1) == cur_tok(toks, st)); }
        let (res, Ghost(x)) = self.parse_statement(Ghost(toks), Ghost(cfg), Ghost(st1));
        self.loop_depth = outer;
        match res {
            Err(e) => {
                proof {
                    assert forall|f: u64| #![trigger p_loop_body(toks, cfg, st, f)] pdone(p_loop_body(toks, cfg, st, f)) implies p_loop_body(toks, cfg, st, f) == x by {
                        assert(f > 0);
                        assert(pdone(p_statement(toks, cfg, st1, (f - 1) as u64)));
                    }
                }
                (Err(e), Ghost(x))
            },
            Ok(v) => {
                let ghost g = pr_node(st_set_loop(x.st, st.loop_depth, x.st.in_function), x.node, x.h);
                proof {
                    assert(cur_tok(toks, g.st) == cur_tok(toks, x.st));
                    assert forall|f: u64| #![trigger p_loop_body(toks, cfg, st, f)] pdone(p_loop_body(toks, cfg, st, f)) implies p_loop_body(toks, cfg, st, f) == g by {
                        assert(f > 0);
                        assert(pdone(p_statement(toks, cfg, st1, (f - 1) as u64)));
                    }
                }
                (Ok(v), Ghost(g))
            },
        }
    }

    #[verifier::rlimit(60)]
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_statement_inner(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) ==> p_statement_inner(toks, cfg, st, f) == r.1@,
    {
        let t = self.current_token.token_type;
        if matches!(t, TokenType::String) {
            let (r0, Ghost(a)) = self.parse_string_stmt(Ghost(toks), Ghost(cfg), Ghost(st));
            proof {
                assert forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) implies p_statement_inner(toks, cfg, st, f) == a by {
                    assert(f > 0);
                }
            }
            return (r0, Ghost(a));
        }
        if matches!(t, TokenType::Break) {
            let (r0, Ghost(a)) = self.parse_break_stmt(Ghost(toks), Ghost(cfg), Ghost(st));
            proof {
                assert forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) implies p_statement_inner(toks, cfg, st, f) == a by {
                    assert(f > 0);
                }
            }
            return (r0, Ghost(a));
        }
        if matches!(t, TokenType::Quit) {
            let ghost g = pr_err(st, PErr { quit: true, out_of_fuel: false, line: 0u64, msg: seq![] });
            proof {
                assert forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) implies p_statement_inner(toks, cfg, st, f) == g by {
                    assert(f > 0);
                }
            }
            return (Err(BcError::Quit), Ghost(g));
        }
        if matches!(t, TokenType::Return) {
            let (r0, Ghost(a)) = self.parse_return_stmt(Ghost(toks), Ghost(cfg), Ghost(st));
            proof {
                assert forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) implies p_statement_inner(toks, cfg, st, f) == a by {
                    assert(f > 0);
                    assert(pdone(p_return_stmt(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (r0, Ghost(a));
        }
        if matches!(t, TokenType::For) {
            let (r0, Ghost(a)) = self.parse_for(Ghost(toks), Ghost(cfg), Ghost(st));
            proof {
                assert forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) implies p_statement_inner(toks, cfg, st, f) == a by {
                    assert(f > 0);
                    assert(pdone(p_for(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (r0, Ghost(a));
        }
        if matches!(t, TokenType::If) {
            let (r0, Ghost(a)) = self.parse_if(Ghost(toks), Ghost(cfg), Ghost(st));
            proof {
                assert forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) implies p_statement_inner(toks, cfg, st, f) == a by {
                    assert(f > 0);
                    assert(pdone(p_if(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (r0, Ghost(a));
        }
        if matches!(t, TokenType::While) {
            let (r0, Ghost(a)) = self.parse_while(Ghost(toks), Ghost(cfg), Ghost(st));
            proof {
                assert forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) implies p_statement_inner(toks, cfg, st, f) == a by {
                    assert(f > 0);
                    assert(pdone(p_while(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (r0, Ghost(a));
        }
        if matches!(t, TokenType::Lbrace) {
            let (r0, Ghost(a)) = self.parse_block(Ghost(toks), Ghost(cfg), Ghost(st));
            proof {
                assert forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) implies p_statement_inner(toks, cfg, st, f) == a by {
                    assert(f > 0);
                    assert(pdone(p_block(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (r0, Ghost(a));
        }
        let (r0, Ghost(a)) = self.parse_expr_stmt(Ghost(toks), Ghost(cfg), Ghost(st));
        proof {
            assert forall|f: u64| #![trigger p_statement_inner(toks, cfg, st, f)] pdone(p_statement_inner(toks, cfg, st, f)) implies p_statement_inner(toks, cfg, st, f) == a by {
                assert(f > 0);
                assert(pdone(p_expr_stmt(toks, cfg, st, (f - 1) as u64)));
            }
        }
        (r0, Ghost(a))
    }

    /// Parses a string statement.
    fn parse_string_stmt(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is Str,
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            r.1@ == p_string_stmt(toks, st),
    {
        let val = self.current_token.value.clone();
        let ghost e = s_eat(toks, st, Tok::Str);
        match self.eat(TokenType::String, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e)),
        }
        let idx = self.add_stmt(PNode::Str(val), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e.st), Ghost(Node::Str(val@)), Ghost(0u64));
        let ghost g = add_node(e.st, Node::Str(val@), 0u64);
        (Ok(idx), Ghost(g))
    }

    /// Parses `break`, which must be inside a loop. GNU bc reports a stray `break` on its own
    /// line, and a stray `return` on the line of the token after it.
    fn parse_break_stmt(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is Break,
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            r.1@ == p_break_stmt(toks, st),
    {
        if self.loop_depth == 0 {
            return (Err(BcError::Syntax { line: self.current_token.line, message: break_outside_text() }), Ghost(misplaced(toks, st, break_msg())));
        }
        let ghost e = s_eat(toks, st, Tok::Break);
        match self.eat(TokenType::Break, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e)),
        }
        let idx = self.add_stmt(PNode::Break, Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e.st), Ghost(Node::Break), Ghost(0u64));
        let ghost g = add_node(e.st, Node::Break, 0u64);
        (Ok(idx), Ghost(g))
    }

    /// Parses `return`, which must be inside a function.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_return_stmt(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is Return,
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_return_stmt(toks, cfg, st, f)] pdone(p_return_stmt(toks, cfg, st, f)) ==> p_return_stmt(toks, cfg, st, f) == r.1@,
    {
        let (res, Ghost(a)) = self.parse_return(Ghost(toks), Ghost(cfg), Ghost(st));
        let x = match res {
            Ok(v) => v,
            Err(y) => {
                proof {
                    assert forall|f: u64| #![trigger p_return_stmt(toks, cfg, st, f)] pdone(p_return_stmt(toks, cfg, st, f)) implies p_return_stmt(toks, cfg, st, f) == a by {
                        assert(f > 0);
                        assert(pdone(p_return(toks, cfg, st, (f - 1) as u64)));
                    }
                }
                return (Err(y), Ghost(a));
            },
        };
        if !self.in_function {
            let ghost g = misplaced(toks, a.st, return_msg());
            proof {
                assert forall|f: u64| #![trigger p_return_stmt(toks, cfg, st, f)] pdone(p_return_stmt(toks, cfg, st, f)) implies p_return_stmt(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_return(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (Err(BcError::Syntax { line: self.current_token.line, message: return_outside_text() }), Ghost(g));
        }
        proof {
            assert forall|f: u64| #![trigger p_return_stmt(toks, cfg, st, f)] pdone(p_return_stmt(toks, cfg, st, f)) implies p_return_stmt(toks, cfg, st, f) == a by {
                assert(f > 0);
                assert(pdone(p_return(toks, cfg, st, (f - 1) as u64)));
            }
        }
        (Ok(x), Ghost(a))
    }

    /// Parses `{ statement_list }`.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_block(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is Lbrace,
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_block(toks, cfg, st, f)] pdone(p_block(toks, cfg, st, f)) ==> p_block(toks, cfg, st, f) == r.1@,
    {
        let ghost e = s_eat(toks, st, Tok::Lbrace);
        match self.eat(TokenType::Lbrace, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e)),
        }
        let (res, Ghost(l)) = self.parse_statement_list(Ghost(toks), Ghost(cfg), Ghost(e.st));
        let stmts = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_block(toks, cfg, st, f)] pdone(p_block(toks, cfg, st, f)) implies p_block(toks, cfg, st, f) == l by {
                        assert(f > 0);
                        assert(pdone(p_statement_list(toks, cfg, e.st, seq![], (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(l));
            },
        };
        let ghost e2 = s_eat(toks, l.st, Tok::Rbrace);
        match self.eat(TokenType::Rbrace, Ghost(toks), Ghost(cfg), Ghost(l.st)) {
            Ok(()) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_block(toks, cfg, st, f)] pdone(p_block(toks, cfg, st, f)) implies p_block(toks, cfg, st, f) == e2 by {
                        assert(f > 0);
                        assert(pdone(p_statement_list(toks, cfg, e.st, seq![], (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(e2));
            },
        }
        let idx = self.add_stmt(PNode::Block(stmts), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e2.st), Ghost(Node::Block(l.list)), Ghost(0u64));
        let ghost g = add_node(e2.st, Node::Block(l.list), 0u64);
        proof {
            assert forall|f: u64| #![trigger p_block(toks, cfg, st, f)] pdone(p_block(toks, cfg, st, f)) implies p_block(toks, cfg, st, f) == g by {
                assert(f > 0);
                assert(pdone(p_statement_list(toks, cfg, e.st, seq![], (f - 1) as u64)));
            }
        }
        (Ok(idx), Ghost(g))
    }

    /// Parses an expression statement; a relational one is a GNU extension.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_expr_stmt(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_expr_stmt(toks, cfg, st, f)] pdone(p_expr_stmt(toks, cfg, st, f)) ==> p_expr_stmt(toks, cfg, st, f) == r.1@,
    {
        let (res, Ghost(a)) = self.parse_relational_expression(Ghost(toks), Ghost(cfg), Ghost(st));
        let x = match res {
            Ok(v) => v,
            Err(y) => {
                proof {
                    assert forall|f: u64| #![trigger p_expr_stmt(toks, cfg, st, f)] pdone(p_expr_stmt(toks, cfg, st, f)) implies p_expr_stmt(toks, cfg, st, f) == a by {
                        assert(f > 0);
                        assert(pdone(p_relational(toks, cfg, st, (f - 1) as u64)));
                    }
                }
                return (Err(y), Ghost(a));
            },
        };
        proof { assert(r_node(self.nodes@[x as int], a.st.nodes[x as int])); }
        let ghost st2 = if a.st.nodes[a.node as int] is Rel { s_extension(toks, cfg, a.st, comparison_msg()) } else { a.st };
        if matches!(self.nodes[x], PNode::Rel(..)) {
            self.extension(comparison_text(), Ghost(toks), Ghost(cfg), Ghost(a.st), Ghost(comparison_msg()));
        }
        let idx = self.add_stmt(PNode::ExprStmt(x), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(st2), Ghost(Node::ExprStmt(a.node)), Ghost(0u64));
        let ghost g = add_node(st2, Node::ExprStmt(a.node), 0u64);
        proof {
            assert(cur_tok(toks, st2) == cur_tok(toks, a.st));
            assert forall|f: u64| #![trigger p_expr_stmt(toks, cfg, st, f)] pdone(p_expr_stmt(toks, cfg, st, f)) implies p_expr_stmt(toks, cfg, st, f) == g by {
                assert(f > 0);
                assert(pdone(p_relational(toks, cfg, st, (f - 1) as u64)));
            }
        }
        (Ok(idx), Ghost(g))
    }

    /// Parses the `for` statement.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_for(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is For,
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_for(toks, cfg, st, f)] pdone(p_for(toks, cfg, st, f)) ==> p_for(toks, cfg, st, f) == r.1@,
    {
        let ghost e1 = s_eat(toks, st, Tok::For);
        match self.eat(TokenType::For, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e1)),
        }
        let ghost e2 = s_eat(toks, e1.st, Tok::Lparen);
        match self.eat(TokenType::Lparen, Ghost(toks), Ghost(cfg), Ghost(e1.st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e2)),
        }
        let (res, Ghost(i)) = self.parse_expression(Ghost(toks), Ghost(cfg), Ghost(e2.st));
        let init = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_for(toks, cfg, st, f)] pdone(p_for(toks, cfg, st, f)) implies p_for(toks, cfg, st, f) == i by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(i));
            },
        };
        let ghost e3 = s_eat(toks, i.st, Tok::Semicolon);
        match self.eat(TokenType::Semicolon, Ghost(toks), Ghost(cfg), Ghost(i.st)) {
            Ok(()) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_for(toks, cfg, st, f)] pdone(p_for(toks, cfg, st, f)) implies p_for(toks, cfg, st, f) == e3 by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(e3));
            },
        }
        let (res, Ghost(c)) = self.parse_relational_expression(Ghost(toks), Ghost(cfg), Ghost(e3.st));
        let cond = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_for(toks, cfg, st, f)] pdone(p_for(toks, cfg, st, f)) implies p_for(toks, cfg, st, f) == c by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                        assert(pdone(p_relational(toks, cfg, e3.st, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(c));
            },
        };
        let ghost e4 = s_eat(toks, c.st, Tok::Semicolon);
        match self.eat(TokenType::Semicolon, Ghost(toks), Ghost(cfg), Ghost(c.st)) {
            Ok(()) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_for(toks, cfg, st, f)] pdone(p_for(toks, cfg, st, f)) implies p_for(toks, cfg, st, f) == e4 by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                        assert(pdone(p_relational(toks, cfg, e3.st, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(e4));
            },
        }
        let (res, Ghost(u)) = self.parse_expression(Ghost(toks), Ghost(cfg), Ghost(e4.st));
        let post = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_for(toks, cfg, st, f)] pdone(p_for(toks, cfg, st, f)) implies p_for(toks, cfg, st, f) == u by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                        assert(pdone(p_relational(toks, cfg, e3.st, (f - 1) as u64)));
                        assert(pdone(p_expr_prec(toks, cfg, e4.st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(u));
            },
        };
        let ghost e5 = s_eat(toks, u.st, Tok::Rparen);
        match self.eat(TokenType::Rparen, Ghost(toks), Ghost(cfg), Ghost(u.st)) {
            Ok(()) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_for(toks, cfg, st, f)] pdone(p_for(toks, cfg, st, f)) implies p_for(toks, cfg, st, f) == e5 by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                        assert(pdone(p_relational(toks, cfg, e3.st, (f - 1) as u64)));
                        assert(pdone(p_expr_prec(toks, cfg, e4.st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(e5));
            },
        }
        let (res, Ghost(b)) = self.parse_loop_body(Ghost(toks), Ghost(cfg), Ghost(e5.st));
        let body = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_for(toks, cfg, st, f)] pdone(p_for(toks, cfg, st, f)) implies p_for(toks, cfg, st, f) == b by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                        assert(pdone(p_relational(toks, cfg, e3.st, (f - 1) as u64)));
                        assert(pdone(p_expr_prec(toks, cfg, e4.st, 0i8, (f - 1) as u64)));
                        assert(pdone(p_loop_body(toks, cfg, e5.st, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(b));
            },
        };
        let ghost nd = Node::For(i.node, c.node, u.node, b.node);
        let idx = self.add_stmt(PNode::For(init, cond, post, body), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(b.st), Ghost(nd), Ghost(0u64));
        let ghost g = add_node(b.st, nd, 0u64);
        proof {
            assert forall|f: u64| #![trigger p_for(toks, cfg, st, f)] pdone(p_for(toks, cfg, st, f)) implies p_for(toks, cfg, st, f) == g by {
                assert(f > 0);
                assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                assert(pdone(p_relational(toks, cfg, e3.st, (f - 1) as u64)));
                assert(pdone(p_expr_prec(toks, cfg, e4.st, 0i8, (f - 1) as u64)));
                assert(pdone(p_loop_body(toks, cfg, e5.st, (f - 1) as u64)));
            }
        }
        (Ok(idx), Ghost(g))
    }

    /// Parses the keyword `if` or `while` and the `( relational_expression )` after it.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_cond(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            !(cur_tok(toks, st).kind is Eof),
        ensures
            r_xres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_cond(toks, cfg, st, f)] pdone(p_cond(toks, cfg, st, f)) ==> p_cond(toks, cfg, st, f) == r.1@,
    {
        let kind = self.current_token.token_type;
        let ghost e1 = s_eat(toks, st, cur_tok(toks, st).kind);
        match self.eat(kind, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e1)),
        }
        let ghost e2 = s_eat(toks, e1.st, Tok::Lparen);
        match self.eat(TokenType::Lparen, Ghost(toks), Ghost(cfg), Ghost(e1.st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e2)),
        }
        let (res, Ghost(c)) = self.parse_relational_expression(Ghost(toks), Ghost(cfg), Ghost(e2.st));
        let cond = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_cond(toks, cfg, st, f)] pdone(p_cond(toks, cfg, st, f)) implies p_cond(toks, cfg, st, f) == c by {
                        assert(f > 0);
                        assert(pdone(p_relational(toks, cfg, e2.st, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(c));
            },
        };
        let ghost e3 = s_eat(toks, c.st, Tok::Rparen);
        let ghost g = if e3.ok { pr_node(e3.st, c.node, 0u64) } else { e3 };
        let res3 = self.eat(TokenType::Rparen, Ghost(toks), Ghost(cfg), Ghost(c.st));
        proof {
            assert forall|f: u64| #![trigger p_cond(toks, cfg, st, f)] pdone(p_cond(toks, cfg, st, f)) implies p_cond(toks, cfg, st, f) == g by {
                assert(f > 0);
                assert(pdone(p_relational(toks, cfg, e2.st, (f - 1) as u64)));
            }
        }
        match res3 {
            Ok(()) => (Ok(cond), Ghost(g)),
            Err(x) => (Err(x), Ghost(g)),
        }
    }

    /// Parses the `if` statement.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_if(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is If,
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_if(toks, cfg, st, f)] pdone(p_if(toks, cfg, st, f)) ==> p_if(toks, cfg, st, f) == r.1@,
    {
        let (res, Ghost(c)) = self.parse_cond(Ghost(toks), Ghost(cfg), Ghost(st));
        let cond = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_if(toks, cfg, st, f)] pdone(p_if(toks, cfg, st, f)) implies p_if(toks, cfg, st, f) == c by {
                        assert(f > 0);
                        assert(pdone(p_cond(toks, cfg, st, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(c));
            },
        };
        let (res, Ghost(b)) = self.parse_statement(Ghost(toks), Ghost(cfg), Ghost(c.st));
        let body = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_if(toks, cfg, st, f)] pdone(p_if(toks, cfg, st, f)) implies p_if(toks, cfg, st, f) == b by {
                        assert(f > 0);
                        assert(pdone(p_cond(toks, cfg, st, (f - 1) as u64)));
                        assert(pdone(p_statement(toks, cfg, c.st, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(b));
            },
        };
        let idx = self.add_stmt(PNode::If(cond, body), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(b.st), Ghost(Node::If(c.node, b.node)), Ghost(0u64));
        let ghost g = add_node(b.st, Node::If(c.node, b.node), 0u64);
        proof {
            assert forall|f: u64| #![trigger p_if(toks, cfg, st, f)] pdone(p_if(toks, cfg, st, f)) implies p_if(toks, cfg, st, f) == g by {
                assert(f > 0);
                assert(pdone(p_cond(toks, cfg, st, (f - 1) as u64)));
                assert(pdone(p_statement(toks, cfg, c.st, (f - 1) as u64)));
            }
        }
        (Ok(idx), Ghost(g))
    }

    /// Parses the `while` statement.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_while(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is While,
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_while(toks, cfg, st, f)] pdone(p_while(toks, cfg, st, f)) ==> p_while(toks, cfg, st, f) == r.1@,
    {
        let (res, Ghost(c)) = self.parse_cond(Ghost(toks), Ghost(cfg), Ghost(st));
        let cond = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_while(toks, cfg, st, f)] pdone(p_while(toks, cfg, st, f)) implies p_while(toks, cfg, st, f) == c by {
                        assert(f > 0);
                        assert(pdone(p_cond(toks, cfg, st, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(c));
            },
        };
        let (res, Ghost(b)) = self.parse_loop_body(Ghost(toks), Ghost(cfg), Ghost(c.st));
        let body = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_while(toks, cfg, st, f)] pdone(p_while(toks, cfg, st, f)) implies p_while(toks, cfg, st, f) == b by {
                        assert(f > 0);
                        assert(pdone(p_cond(toks, cfg, st, (f - 1) as u64)));
                        assert(pdone(p_loop_body(toks, cfg, c.st, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(b));
            },
        };
        let idx = self.add_stmt(PNode::While(cond, body), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(b.st), Ghost(Node::While(c.node, b.node)), Ghost(0u64));
        let ghost g = add_node(b.st, Node::While(c.node, b.node), 0u64);
        proof {
            assert forall|f: u64| #![trigger p_while(toks, cfg, st, f)] pdone(p_while(toks, cfg, st, f)) implies p_while(toks, cfg, st, f) == g by {
                assert(f > 0);
                assert(pdone(p_cond(toks, cfg, st, (f - 1) as u64)));
                assert(pdone(p_loop_body(toks, cfg, c.st, (f - 1) as u64)));
            }
        }
        (Ok(idx), Ghost(g))
    }

    /// Parses `return`, `return (e)`, or the GNU extension `return e`.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_return(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is Return,
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_return(toks, cfg, st, f)] pdone(p_return(toks, cfg, st, f)) ==> p_return(toks, cfg, st, f) == r.1@,
    {
        let ghost e = s_eat(toks, st, Tok::Return);
        match self.eat(TokenType::Return, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e)),
        }
        if matches!(self.current_token.token_type, TokenType::Lparen) {
            let ghost e2 = s_eat(toks, e.st, Tok::Lparen);
            match self.eat(TokenType::Lparen, Ghost(toks), Ghost(cfg), Ghost(e.st)) {
                Ok(()) => {},
                Err(x) => return (Err(x), Ghost(e2)),
            }
            // POSIX: `return ()` is `return (0)`.
            if matches!(self.current_token.token_type, TokenType::Rparen) {
                let ghost e3 = s_eat(toks, e2.st, Tok::Rparen);
                match self.eat(TokenType::Rparen, Ghost(toks), Ghost(cfg), Ghost(e2.st)) {
                    Ok(()) => {},
                    Err(x) => return (Err(x), Ghost(e3)),
                }
                let idx = self.add_stmt(PNode::Return(None), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e3.st), Ghost(Node::Return(false, 0usize)), Ghost(0u64));
                let ghost g = add_node(e3.st, Node::Return(false, 0usize), 0u64);
                return (Ok(idx), Ghost(g));
            }
            let (res, Ghost(v)) = self.parse_expression(Ghost(toks), Ghost(cfg), Ghost(e2.st));
            let x = match res {
                Ok(w) => w,
                Err(y) => {
                    proof {
                        assert forall|f: u64| #![trigger p_return(toks, cfg, st, f)] pdone(p_return(toks, cfg, st, f)) implies p_return(toks, cfg, st, f) == v by {
                            assert(f > 0);
                            assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                        }
                    }
                    return (Err(y), Ghost(v));
                },
            };
            let ghost e3 = s_eat(toks, v.st, Tok::Rparen);
            match self.eat(TokenType::Rparen, Ghost(toks), Ghost(cfg), Ghost(v.st)) {
                Ok(()) => {},
                Err(y) => {
                    proof {
                        assert forall|f: u64| #![trigger p_return(toks, cfg, st, f)] pdone(p_return(toks, cfg, st, f)) implies p_return(toks, cfg, st, f) == e3 by {
                            assert(f > 0);
                            assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                        }
                    }
                    return (Err(y), Ghost(e3));
                },
            }
            let idx = self.add_stmt(PNode::Return(Some(x)), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e3.st), Ghost(Node::Return(true, v.node)), Ghost(0u64));
            let ghost g = add_node(e3.st, Node::Return(true, v.node), 0u64);
            proof {
                assert forall|f: u64| #![trigger p_return(toks, cfg, st, f)] pdone(p_return(toks, cfg, st, f)) implies p_return(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, e2.st, 0i8, (f - 1) as u64)));
                }
            }
            return (Ok(idx), Ghost(g));
        }
        // GNU extension: return without parentheses
        let nt = self.current_token.token_type;
        if !matches!(nt, TokenType::Newline) && !matches!(nt, TokenType::Semicolon)
            && !matches!(nt, TokenType::Rbrace) && !matches!(nt, TokenType::Eof)
        {
            let (res, Ghost(v)) = self.parse_expression(Ghost(toks), Ghost(cfg), Ghost(e.st));
            let x = match res {
                Ok(w) => w,
                Err(y) => {
                    proof {
                        assert forall|f: u64| #![trigger p_return(toks, cfg, st, f)] pdone(p_return(toks, cfg, st, f)) implies p_return(toks, cfg, st, f) == v by {
                            assert(f > 0);
                            assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                        }
                    }
                    return (Err(y), Ghost(v));
                },
            };
            self.extension(return_paren_text(), Ghost(toks), Ghost(cfg), Ghost(v.st), Ghost(return_paren_msg()));
            let ghost st2 = s_extension(toks, cfg, v.st, return_paren_msg());
            let idx = self.add_stmt(PNode::Return(Some(x)), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(st2), Ghost(Node::Return(true, v.node)), Ghost(0u64));
            let ghost g = add_node(st2, Node::Return(true, v.node), 0u64);
            proof {
                assert(cur_tok(toks, st2) == cur_tok(toks, v.st));
                assert forall|f: u64| #![trigger p_return(toks, cfg, st, f)] pdone(p_return(toks, cfg, st, f)) implies p_return(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                }
            }
            (Ok(idx), Ghost(g))
        } else {
            let idx = self.add_stmt(PNode::Return(None), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e.st), Ghost(Node::Return(false, 0usize)), Ghost(0u64));
            let ghost g = add_node(e.st, Node::Return(false, 0usize), 0u64);
            proof {
                assert forall|f: u64| #![trigger p_return(toks, cfg, st, f)] pdone(p_return(toks, cfg, st, f)) implies p_return(toks, cfg, st, f) == g by {
                    assert(f > 0);
                }
            }
            (Ok(idx), Ghost(g))
        }
    }

}

} // verus!
