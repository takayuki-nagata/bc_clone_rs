// SPDX-License-Identifier: MIT

//! Expressions (the specification's `p_relational` to `p_arg_list`): Pratt precedence climbing,
//! prefix and primary expressions, calls and their argument lists.

use super::*;

verus! {

spec fn r_eres(r: Result<(usize, usize), BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok((x, h)) => p.ok && r_p(q, toks, cfg, p.st) && h as u64 == p.h && h <= q.max_depth + 2
            && r_grown(s0, p.st) && x == p.node && x < p.st.nodes.s.len(),
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

spec fn r_ares(r: Result<(Vec<PArg>, usize), BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok((a, h)) => p.ok && r_p(q, toks, cfg, p.st) && h as u64 == p.h && h <= q.max_depth + 1
            && extends(s0.nodes.s, p.st.nodes.s) && p.st.cur >= s0.cur
            && p.st.nodes.s.len() - s0.nodes.s.len() <= p.st.cur - s0.cur && p.st.depth == s0.depth
            && r_args(a@, p.args),
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

/// `Parser::parse_expr_precedence_inner` in the specification: the prefix, then the loop.
spec fn p_inner(toks: Seq<SToken>, cfg: PCfg, st: PState, min_prec: i8, f: u64) -> PR {
    let p = p_prefix(toks, cfg, st, f);
    if !p.ok { p } else { p_expr_loop(toks, cfg, p.st, p.node, p.h, min_prec, f) }
}

/// Precedence info for binary and assignment operators: `(precedence, is_assignment,
/// next_min_precedence)`.
fn infix_info(token_type: TokenType) -> (r: (i8, bool, i8))
    ensures
        r == s_infix_info(tok_of(token_type)),
{
    let tok_kind = match token_type {
        TokenType::AssignOp => TOK_ASSIGN_OP,
        TokenType::Plus | TokenType::Minus => TOK_PLUS_MINUS,
        TokenType::MulOp => TOK_MUL_OP,
        TokenType::Exp => TOK_EXP_OP,
        _ => 0,
    };
    let (op_prec, _right_assoc, next_min_prec) = verified_pratt_infix_info(tok_kind);
    (op_prec, matches!(token_type, TokenType::AssignOp), next_min_prec)
}

/// The operator of a binary token.
#[allow(clippy::len_zero, reason = "with `is_empty` here, `parse_primary` exceeds its rlimit")]
fn bin_op(t: &Token) -> (r: BinOp)
    ensures
        bin_code(r) == binop_code(tok_view(*t)),
{
    let c = if t.value.len() > 0 { t.value[0] } else { 0 };
    if c == b'+' { BinOp::Add }
    else if c == b'-' { BinOp::Sub }
    else if c == b'*' { BinOp::Mul }
    else if c == b'/' { BinOp::Div }
    else if c == b'%' { BinOp::Mod }
    else { BinOp::Pow }
}

/// The operator of a relational token.
#[allow(clippy::len_zero, reason = "with `is_empty` here, `parse_primary` exceeds its rlimit")]
fn rel_op(t: &Token) -> (r: RelOp)
    ensures
        r_rel_code(r) == s_rel_code(tok_view(*t)),
{
    let c = if t.value.len() > 0 { t.value[0] } else { 0 };
    let two = t.value.len() == 2;
    if c == b'=' { RelOp::Eq }
    else if c == b'!' { RelOp::Ne }
    else if c == b'<' { if two { RelOp::Le } else { RelOp::Lt } }
    else { if two { RelOp::Ge } else { RelOp::Gt } }
}

/// The operator of an assignment token.
fn assign_op(t: &Token) -> (r: AssignOp)
    ensures
        r_assign_code(r) == s_assign_code(tok_view(*t)),
{
    if t.value.len() == 1 { AssignOp::Assign } else { AssignOp::Compound(bin_op(t)) }
}

/// Whether an update token is `++`.
#[allow(clippy::len_zero, reason = "with `is_empty` here, `parse_primary` exceeds its rlimit")]
fn is_increment(t: &Token) -> (r: bool)
    ensures
        r == (tok_view(*t).text.len() > 0 && tok_view(*t).text[0] == 43u8),
{
    t.value.len() > 0 && t.value[0] == b'+'
}

fn max_height(a: usize, b: usize) -> (r: usize)
    ensures
        r as u64 == max_u64(a as u64, b as u64),
        r == a || r == b,
        r >= a && r >= b,
{
    if a >= b { a } else { b }
}

/// Looking ahead in the tokens left to the lexer.
proof fn lemma_rest_token(toks: Seq<SToken>, k: int, off: usize)
    requires
        toks_wf(toks),
        0 <= k <= toks.len() + 1,
        off < 8,
    ensures
        token_at(rest_of(toks, k), off) == token_at(toks, (k + off) as usize),
        rest_of(toks, k).last() == toks.last(),
        k + rest_of(toks, k).len() - 1 >= toks.len() - 1,
        k < toks.len() ==> k + rest_of(toks, k).len() - 1 == toks.len() - 1,
{
    if k < toks.len() {
        assert(toks.skip(k).last() == toks.last());
        if k + off < toks.len() {
            assert(toks.skip(k)[off as int] == toks[k + off]);
        }
    }
}

impl Parser {
    /// Adds an expression's node to the arena (the specification's `add_node`).
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn add_expr(&mut self, pn: PNode, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(s0): Ghost<GState>, Ghost(s): Ghost<GState>, Ghost(n): Ghost<GNode>, Ghost(h): Ghost<u64>) -> (idx: usize)
        requires
            r_p(*old(self), toks, cfg, s),
            r_node(pn, n),
            extends(s0.nodes.s, s.nodes.s),
            s0.nodes.s.len() <= 2 * s0.cur,
            s.nodes.s.len() - s0.nodes.s.len() + 1 <= s.cur - s0.cur,
            s.depth == s0.depth,
        ensures
            pushed(*old(self), *final(self), pn),
            ({
                let g = add_node(s, n, h);
                &&& g.ok
                &&& g.h == h
                &&& g.node == idx
                &&& idx == s.nodes.s.len()
                &&& g.st.nodes.s.len() == s.nodes.s.len() + 1
                &&& g.st.nodes.s[g.node as int] == n
                &&& g.st.cur == s.cur
                &&& g.st.ext == s.ext
                &&& r_p(*final(self), toks, cfg, g.st)
                &&& extends(s.nodes.s, g.st.nodes.s)
                &&& r_grown(s0, g.st)
            }),
    {
        let idx = self.nodes.len();
        self.nodes.push(pn);
        proof {
            // A `Vec` holds at most `usize::MAX` nodes, so the arena was not full.
            assert(self.nodes@.len() == self.nodes.len());
            let g = add_node(s, n, h);
            assert(g.st.nodes.s =~= s.nodes.s.push(n));
            assert(cur_tok(toks, g.st) == cur_tok(toks, s));
            assert forall|i: int| 0 <= i < self.nodes@.len() implies #[trigger] r_node(self.nodes@[i], g.st.nodes.s[i]) by {
                if i < s.nodes.s.len() { assert(r_node(old(self).nodes@[i], s.nodes.s[i])); }
            }
        }
        idx
    }

    /// Peeks the token type of the token at `offset`.
    fn peek_token_type(&mut self, offset: usize, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: Result<TokenType, BcError>)
        requires
            r_p(*old(self), toks, cfg, st),
            offset < 8,
        ensures
            final(self).extension_uses == old(self).extension_uses,
            match r {
                Ok(k) => r_p(*final(self), toks, cfg, st) && peek_kind(toks, st, offset).0 && peek_kind(toks, st, offset).1 == tok_of(k),
                Err(x) => !peek_kind(toks, st, offset).0 && r_perr(x, final(self).extension_uses@, lex_err(st, peek_kind(toks, st, offset).2)),
            },
    {
        proof { lemma_rest_token(toks, st.cur + 1, offset); }
        self.lexer.try_peek_token(offset)
    }

    /// Parses an arithmetic expression.
    pub(super) fn parse_expression(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_xres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_expr_prec(toks, cfg, st, 0i8, f)] pdone(p_expr_prec(toks, cfg, st, 0i8, f)) ==> p_expr_prec(toks, cfg, st, 0i8, f) == r.1@,
    {
        let (res, Ghost(x)) = self.parse_expr_precedence(0, Ghost(toks), Ghost(cfg), Ghost(st));
        match res {
            Ok((e, _)) => (Ok(e), Ghost(x)),
            Err(e) => (Err(e), Ghost(x)),
        }
    }

    /// Parses expressions, including relational ones.
    pub(super) fn parse_relational_expression(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_xres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_relational(toks, cfg, st, f)] pdone(p_relational(toks, cfg, st, f)) ==> p_relational(toks, cfg, st, f) == r.1@,
    {
        let (res, Ghost(l)) = self.parse_expr_precedence(0, Ghost(toks), Ghost(cfg), Ghost(st));
        let (left, left_h) = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_relational(toks, cfg, st, f)] pdone(p_relational(toks, cfg, st, f)) implies p_relational(toks, cfg, st, f) == l by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(l));
            },
        };
        if !matches!(self.current_token.token_type, TokenType::RelOp) {
            proof {
                assert forall|f: u64| #![trigger p_relational(toks, cfg, st, f)] pdone(p_relational(toks, cfg, st, f)) implies p_relational(toks, cfg, st, f) == l by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, st, 0i8, (f - 1) as u64)));
                }
            }
            return (Ok(left), Ghost(l));
        }
        let op = rel_op(&self.current_token);
        let ghost e = s_eat(toks, l.st, Tok::RelOp);
        match self.eat(TokenType::RelOp, Ghost(toks), Ghost(cfg), Ghost(l.st)) {
            Ok(()) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_relational(toks, cfg, st, f)] pdone(p_relational(toks, cfg, st, f)) implies p_relational(toks, cfg, st, f) == e by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(e));
            },
        }
        let (res2, Ghost(rr)) = self.parse_expr_precedence(0, Ghost(toks), Ghost(cfg), Ghost(e.st));
        let (right, right_h) = match res2 {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_relational(toks, cfg, st, f)] pdone(p_relational(toks, cfg, st, f)) implies p_relational(toks, cfg, st, f) == rr by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, st, 0i8, (f - 1) as u64)));
                        assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(rr));
            },
        }
        ;
        let h = 1 + max_height(left_h, right_h);
        let ghost sh = inc(max_u64(l.h, rr.h));
        match self.check_height(h, Ghost(toks), Ghost(cfg), Ghost(rr.st)) {
            Ok(_) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_relational(toks, cfg, st, f)] pdone(p_relational(toks, cfg, st, f)) implies p_relational(toks, cfg, st, f) == too_deep(rr.st) by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, st, 0i8, (f - 1) as u64)));
                        assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(too_deep(rr.st)));
            },
        }
        let idx = self.add_expr(PNode::Rel(op, left, right), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(rr.st), Ghost(Node::Rel(s_rel_code(cur_tok(toks, l.st)), l.node, rr.node)), Ghost(sh));
        let ghost g = add_node(rr.st, Node::Rel(s_rel_code(cur_tok(toks, l.st)), l.node, rr.node), sh);
        proof {
                assert forall|f: u64| #![trigger p_relational(toks, cfg, st, f)] pdone(p_relational(toks, cfg, st, f)) implies p_relational(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, st, 0i8, (f - 1) as u64)));
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                }
        }
        (Ok(idx), Ghost(g))
    }

    /// Checks that a subtree of height `height` below the current level is within the limit.
    fn check_height(&self, height: usize, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: Result<usize, BcError>)
        requires
            r_p(*self, toks, cfg, st),
        ensures
            match r {
                Ok(h) => h == height && height <= self.max_depth && within(st.depth, height as u64, cfg.max_depth),
                Err(x) => !within(st.depth, height as u64, cfg.max_depth) && r_perr(x, self.extension_uses@, too_deep(st)),
            },
    {
        if verified_nesting_within_limit(self.depth, height, self.max_depth) {
            Ok(height)
        } else {
            Err(self.too_deep_error(Ghost(toks), Ghost(cfg), Ghost(st)))
        }
    }

    /// Implements Precedence Climbing algorithm. Each call is one level of nesting: it is
    /// counted on entry, so deeply nested input is rejected before its tree is built, and the
    /// height of the result is checked against `max_depth` (`docs/COMPATIBILITY.md` §2).
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_expr_precedence(&mut self, min_prec: i8, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            min_prec >= 0,
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            r.0 matches Ok((_, h)) ==> h <= final(self).max_depth,
            forall|f: u64| #![trigger p_expr_prec(toks, cfg, st, min_prec, f)] pdone(p_expr_prec(toks, cfg, st, min_prec, f)) ==> p_expr_prec(toks, cfg, st, min_prec, f) == r.1@,
    {
        if !verified_nesting_within_limit(self.depth, 1, self.max_depth) {
            return (Err(self.too_deep_error(Ghost(toks), Ghost(cfg), Ghost(st))), Ghost(too_deep(st)));
        }
        let outer = self.depth;
        self.depth = outer + 1;
        let ghost st1 = st_set_depth(st, (st.depth + 1) as u64);
        proof { assert(cur_tok(toks, st1) == cur_tok(toks, st)); }
        let (res, Ghost(x)) = self.parse_expr_precedence_inner(min_prec, Ghost(toks), Ghost(cfg), Ghost(st1));
        self.depth = outer;
        match res {
            Err(e) => {
                proof {
                    assert forall|f: u64| #![trigger p_expr_prec(toks, cfg, st, min_prec, f)] pdone(p_expr_prec(toks, cfg, st, min_prec, f)) implies p_expr_prec(toks, cfg, st, min_prec, f) == x by {
                        assert(f > 0);
                        assert(pdone(p_inner(toks, cfg, st1, min_prec, (f - 1) as u64)));
                    }
                }
                (Err(e), Ghost(x))
            },
            Ok((e, h)) => {
                let ghost g = pr_node(st_set_depth(x.st, st.depth), x.node, x.h);
                proof {
                    assert(cur_tok(toks, g.st) == cur_tok(toks, x.st));
                    assert forall|f: u64| #![trigger p_expr_prec(toks, cfg, st, min_prec, f)] pdone(p_expr_prec(toks, cfg, st, min_prec, f)) implies p_expr_prec(toks, cfg, st, min_prec, f) == g by {
                        assert(f > 0);
                        assert(pdone(p_inner(toks, cfg, st1, min_prec, (f - 1) as u64)));
                    }
                }
                (Ok((e, h)), Ghost(g))
            },
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn parse_expr_precedence_inner(&mut self, min_prec: i8, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            min_prec >= 0,
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            r.0 matches Ok((_, h)) ==> h + st.depth <= final(self).max_depth,
            forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) ==> p_inner(toks, cfg, st, min_prec, f) == r.1@,
    {
        let (res, Ghost(p)) = self.parse_prefix(Ghost(toks), Ghost(cfg), Ghost(st));
        let (mut left, mut height) = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) implies p_inner(toks, cfg, st, min_prec, f) == p by {
                        assert(pdone(p_prefix(toks, cfg, st, f)));
                    }
                }
                return (Err(x), Ghost(p));
            },
        };
        let ghost mut cur = p.st;
        let ghost mut node = p.node;
        let ghost mut sh = p.h;
        proof {
            assert forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) implies
                exists|g: u64| #![trigger p_expr_loop(toks, cfg, cur, node, sh, min_prec, g)] p_expr_loop(toks, cfg, cur, node, sh, min_prec, g) == p_inner(toks, cfg, st, min_prec, f) by {
                assert(pdone(p_prefix(toks, cfg, st, f)));
                assert(p_expr_loop(toks, cfg, cur, node, sh, min_prec, f) == p_inner(toks, cfg, st, min_prec, f));
            }
        }
        loop
            invariant
                r_p(*self, toks, cfg, cur),
                r_grown(st, cur),
                st.nodes.s.len() <= 2 * st.cur,
                left == node && left < cur.nodes.s.len(),
                height as u64 == sh,
                height <= self.max_depth + 2,
                min_prec >= 0,
                forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) ==>
                    exists|g: u64| #![trigger p_expr_loop(toks, cfg, cur, node, sh, min_prec, g)] p_expr_loop(toks, cfg, cur, node, sh, min_prec, g) == p_inner(toks, cfg, st, min_prec, f),
        {
            let ghost (c, n0, h0) = (cur, node, sh);
            let (op_prec, is_assign, next_min_prec) = infix_info(self.current_token.token_type);
            let ghost t = cur_tok(toks, c);
            if op_prec < min_prec {
                return match self.check_height(height, Ghost(toks), Ghost(cfg), Ghost(c)) {
                    Ok(h) => {
                        let ghost g = pr_node(c, n0, h0);
                        proof { assert forall|k: u64| #![trigger p_expr_loop(toks, cfg, c, n0, h0, min_prec, k)] k > 0 && pdone(p_expr_loop(toks, cfg, c, n0, h0, min_prec, k)) implies p_expr_loop(toks, cfg, c, n0, h0, min_prec, k) == g by {}
                    lemma_loop_ret(toks, cfg, st, min_prec, c, n0, h0, g); }
                        (Ok((left, h)), Ghost(g))
                    },
                    Err(x) => {
                        let ghost g = too_deep(c);
                        proof { assert forall|k: u64| #![trigger p_expr_loop(toks, cfg, c, n0, h0, min_prec, k)] k > 0 && pdone(p_expr_loop(toks, cfg, c, n0, h0, min_prec, k)) implies p_expr_loop(toks, cfg, c, n0, h0, min_prec, k) == g by {}
                    lemma_loop_ret(toks, cfg, st, min_prec, c, n0, h0, g); }
                        (Err(x), Ghost(g))
                    },
                };
            }
            if is_assign {
                // Assignments to named expressions are parsed in `parse_primary`; anything
                // else on the left (`1 = 2`, `(a) = 2`, `a = 1 = 2`) is not assignable.
                let ghost g = syntax_at(c, t.line);
                proof { assert forall|k: u64| #![trigger p_expr_loop(toks, cfg, c, n0, h0, min_prec, k)] k > 0 && pdone(p_expr_loop(toks, cfg, c, n0, h0, min_prec, k)) implies p_expr_loop(toks, cfg, c, n0, h0, min_prec, k) == g by {}
                    lemma_loop_ret(toks, cfg, st, min_prec, c, n0, h0, g); }
                return (Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() }), Ghost(g));
            }
            let op = bin_op(&self.current_token);
            let kind = self.current_token.token_type;
            let ghost e = s_eat(toks, c, t.kind);
            match self.eat(kind, Ghost(toks), Ghost(cfg), Ghost(c)) {
                Ok(()) => {},
                Err(x) => {
                    proof { assert forall|g: u64| #![trigger p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)] g > 0 && pdone(p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)) implies p_expr_loop(toks, cfg, c, n0, h0, min_prec, g) == e by {}
                    lemma_loop_ret(toks, cfg, st, min_prec, c, n0, h0, e); }
                    return (Err(x), Ghost(e));
                },
            }
            let (res2, Ghost(rr)) = self.parse_expr_precedence(next_min_prec, Ghost(toks), Ghost(cfg), Ghost(e.st));
            let (right, right_height) = match res2 {
                Ok(v) => v,
                Err(x) => {
                    proof { assert forall|g: u64| #![trigger p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)] g > 0 && pdone(p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)) implies p_expr_loop(toks, cfg, c, n0, h0, min_prec, g) == rr by {
                        assert(pdone(p_expr_prec(toks, cfg, e.st, next_min_prec, (g - 1) as u64)));
                    }
                    lemma_loop_ret(toks, cfg, st, min_prec, c, n0, h0, rr); }
                    return (Err(x), Ghost(rr));
                },
            };
            // A left-associative chain grows without recursion, so its height is checked here.
            let h2 = 1 + max_height(height, right_height);
            let ghost sh2 = inc(max_u64(h0, rr.h));
            match self.check_height(h2, Ghost(toks), Ghost(cfg), Ghost(rr.st)) {
                Ok(_) => {},
                Err(x) => {
                    proof { assert forall|g: u64| #![trigger p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)] g > 0 && pdone(p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)) implies p_expr_loop(toks, cfg, c, n0, h0, min_prec, g) == too_deep(rr.st) by {
                        assert(pdone(p_expr_prec(toks, cfg, e.st, next_min_prec, (g - 1) as u64)));
                    }
                    lemma_loop_ret(toks, cfg, st, min_prec, c, n0, h0, too_deep(rr.st)); }
                    return (Err(x), Ghost(too_deep(rr.st)));
                },
            }
            let idx = self.add_expr(PNode::Binary(op, left, right), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(rr.st), Ghost(Node::Binary(binop_code(t), n0, rr.node)), Ghost(sh2));
            let ghost nd = add_node(rr.st, Node::Binary(binop_code(t), n0, rr.node), sh2);
            proof {
                assert forall|g: u64| #![trigger p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)] g > 0 && pdone(p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)) implies p_expr_loop(toks, cfg, c, n0, h0, min_prec, g) == p_expr_loop(toks, cfg, nd.st, nd.node, sh2, min_prec, (g - 1) as u64) by {
                        assert(pdone(p_expr_prec(toks, cfg, e.st, next_min_prec, (g - 1) as u64)));
                    }
                lemma_loop_next(toks, cfg, st, min_prec, c, n0, h0, nd.st, nd.node, sh2);
                cur = nd.st;
                node = nd.node;
                sh = sh2;
            }
            left = idx;
            height = h2;
        }
    }

    /// Parses prefixes (unary operators).
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_prefix(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_prefix(toks, cfg, st, f)] pdone(p_prefix(toks, cfg, st, f)) ==> p_prefix(toks, cfg, st, f) == r.1@,
    {
        let ghost t = cur_tok(toks, st);
        if matches!(self.current_token.token_type, TokenType::Minus) {
            let ghost e = s_eat(toks, st, Tok::Minus);
            match self.eat(TokenType::Minus, Ghost(toks), Ghost(cfg), Ghost(st)) {
                Ok(()) => {},
                Err(x) => return (Err(x), Ghost(e)),
            }
            let (res, Ghost(a)) = self.parse_expr_precedence(5, Ghost(toks), Ghost(cfg), Ghost(e.st));
            let (x, h) = match res {
                Ok(v) => v,
                Err(x) => {
                    proof {
                        assert forall|f: u64| #![trigger p_prefix(toks, cfg, st, f)] pdone(p_prefix(toks, cfg, st, f)) implies p_prefix(toks, cfg, st, f) == a by {
                            assert(f > 0);
                            assert(pdone(p_expr_prec(toks, cfg, e.st, 5i8, (f - 1) as u64)));
                        }
                    }
                    return (Err(x), Ghost(a));
                },
            };
            let idx = self.add_expr(PNode::Neg(x), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(a.st), Ghost(Node::Neg(a.node)), Ghost(inc(a.h)));
            let ghost g = add_node(a.st, Node::Neg(a.node), inc(a.h));
            proof {
                assert forall|f: u64| #![trigger p_prefix(toks, cfg, st, f)] pdone(p_prefix(toks, cfg, st, f)) implies p_prefix(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 5i8, (f - 1) as u64)));
                }
            }
            (Ok((idx, h + 1)), Ghost(g))
        } else if matches!(self.current_token.token_type, TokenType::IncrDecr) {
            let is_inc = is_increment(&self.current_token);
            let ghost e = s_eat(toks, st, Tok::IncrDecr);
            match self.eat(TokenType::IncrDecr, Ghost(toks), Ghost(cfg), Ghost(st)) {
                Ok(()) => {},
                Err(x) => return (Err(x), Ghost(e)),
            }
            let (res, Ghost(a)) = self.parse_named_expression(Ghost(toks), Ghost(cfg), Ghost(e.st));
            let (x, h) = match res {
                Ok(v) => v,
                Err(x) => {
                    proof {
                        assert forall|f: u64| #![trigger p_prefix(toks, cfg, st, f)] pdone(p_prefix(toks, cfg, st, f)) implies p_prefix(toks, cfg, st, f) == a by {
                            assert(f > 0);
                            assert(pdone(p_named(toks, cfg, e.st, (f - 1) as u64)));
                        }
                    }
                    return (Err(x), Ghost(a));
                },
            };
            let idx = self.add_expr(PNode::Update(is_inc, true, x), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(a.st), Ghost(Node::Update(is_inc, true, a.node)), Ghost(inc(a.h)));
            let ghost g = add_node(a.st, Node::Update(is_inc, true, a.node), inc(a.h));
            proof {
                assert forall|f: u64| #![trigger p_prefix(toks, cfg, st, f)] pdone(p_prefix(toks, cfg, st, f)) implies p_prefix(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_named(toks, cfg, e.st, (f - 1) as u64)));
                }
            }
            (Ok((idx, h + 1)), Ghost(g))
        } else {
            let (res, Ghost(a)) = self.parse_primary(Ghost(toks), Ghost(cfg), Ghost(st));
            proof {
                assert forall|f: u64| #![trigger p_prefix(toks, cfg, st, f)] pdone(p_prefix(toks, cfg, st, f)) implies p_prefix(toks, cfg, st, f) == a by {
                    assert(f > 0);
                    assert(pdone(p_primary(toks, cfg, st, (f - 1) as u64)));
                }
            }
            (res, Ghost(a))
        }
    }

    /// Parses `( expression )` after the keyword or name that precedes it.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_parenthesized(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            r.0 matches Ok((_, h)) ==> h <= final(self).max_depth,
            r.0 is Ok ==> r.1@.st.nodes.s.len() - st.nodes.s.len() + 1 <= r.1@.st.cur - st.cur,
            forall|f: u64| #![trigger p_parenthesized(toks, cfg, st, f)] pdone(p_parenthesized(toks, cfg, st, f)) ==> p_parenthesized(toks, cfg, st, f) == r.1@,
    {
        let ghost e = s_eat(toks, st, Tok::Lparen);
        match self.eat(TokenType::Lparen, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e)),
        }
        let (res, Ghost(a)) = self.parse_expr_precedence(0, Ghost(toks), Ghost(cfg), Ghost(e.st));
        let (x, h) = match res {
            Ok(v) => v,
            Err(y) => {
                proof {
                    assert forall|f: u64| #![trigger p_parenthesized(toks, cfg, st, f)] pdone(p_parenthesized(toks, cfg, st, f)) implies p_parenthesized(toks, cfg, st, f) == a by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(y), Ghost(a));
            },
        };
        let ghost e2 = s_eat(toks, a.st, Tok::Rparen);
        let ghost g = if e2.ok { pr_node(e2.st, a.node, a.h) } else { e2 };
        let res2 = self.eat(TokenType::Rparen, Ghost(toks), Ghost(cfg), Ghost(a.st));
        proof {
                assert forall|f: u64| #![trigger p_parenthesized(toks, cfg, st, f)] pdone(p_parenthesized(toks, cfg, st, f)) implies p_parenthesized(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                }
        }
        match res2 {
            Ok(()) => (Ok((x, h)), Ghost(g)),
            Err(y) => (Err(y), Ghost(g)),
        }
    }

    /// Parses a keyword followed by a parenthesized expression: `length`, `sqrt` or `scale`
    /// (`which` is 0, 1 or 2).
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_builtin(&mut self, which: u8, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            !(cur_tok(toks, st).kind is Eof),
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_builtin(toks, cfg, st, which, f)] pdone(p_builtin(toks, cfg, st, which, f)) ==> p_builtin(toks, cfg, st, which, f) == r.1@,
    {
        let kind = self.current_token.token_type;
        let ghost e = s_eat(toks, st, cur_tok(toks, st).kind);
        match self.eat(kind, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e)),
        }
        let (res, Ghost(a)) = self.parse_parenthesized(Ghost(toks), Ghost(cfg), Ghost(e.st));
        let (x, h) = match res {
            Ok(v) => v,
            Err(y) => {
                proof {
                    assert forall|f: u64| #![trigger p_builtin(toks, cfg, st, which, f)] pdone(p_builtin(toks, cfg, st, which, f)) implies p_builtin(toks, cfg, st, which, f) == a by {
                        assert(f > 0);
                        assert(pdone(p_parenthesized(toks, cfg, e.st, (f - 1) as u64)));
                    }
                }
                return (Err(y), Ghost(a));
            },
        };
        let ghost n = if which == 0 { Node::Length(a.node) } else if which == 1 { Node::Sqrt(a.node) } else { Node::ScaleOf(a.node) };
        let call = if which == 0 { PNode::Length(x) } else if which == 1 { PNode::Sqrt(x) } else { PNode::ScaleOf(x) };
        let idx = self.add_expr(call, Ghost(toks), Ghost(cfg), Ghost(st), Ghost(a.st), Ghost(n), Ghost(inc(a.h)));
        let ghost g = add_node(a.st, n, inc(a.h));
        proof {
            assert forall|f: u64| #![trigger p_builtin(toks, cfg, st, which, f)] pdone(p_builtin(toks, cfg, st, which, f)) implies p_builtin(toks, cfg, st, which, f) == g by {
                assert(f > 0);
                assert(pdone(p_parenthesized(toks, cfg, e.st, (f - 1) as u64)));
            }
        }
        (Ok((idx, h + 1)), Ghost(g))
    }

    /// Parses primary expressions (literals, variables, built-ins, calls).
    #[verifier::rlimit(60)]
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_primary(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_primary(toks, cfg, st, f)] pdone(p_primary(toks, cfg, st, f)) ==> p_primary(toks, cfg, st, f) == r.1@,
    {
        let ghost t = cur_tok(toks, st);
        let k = self.current_token.token_type;
        if matches!(k, TokenType::Number) {
            proof { lemma_cur_ascii(toks, st); }
            let val = self.current_token.text();
            let ghost e = s_eat(toks, st, Tok::Number);
            match self.eat(TokenType::Number, Ghost(toks), Ghost(cfg), Ghost(st)) {
                Ok(()) => {},
                Err(x) => return (Err(x), Ghost(e)),
            }
            let idx = self.add_expr(PNode::Number(val), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e.st), Ghost(Node::Number(t.text)), Ghost(1u64));
            let ghost g = add_node(e.st, Node::Number(t.text), 1u64);
            return (Ok((idx, 1)), Ghost(g));
        }
        if matches!(k, TokenType::Lparen) {
            let (res, Ghost(a)) = self.parse_parenthesized(Ghost(toks), Ghost(cfg), Ghost(st));
            let (x, h) = match res {
                Ok(v) => v,
                Err(y) => {
                    proof {
                        assert forall|f: u64| #![trigger p_primary(toks, cfg, st, f)] pdone(p_primary(toks, cfg, st, f)) implies p_primary(toks, cfg, st, f) == a by {
                            assert(f > 0);
                            assert(pdone(p_parenthesized(toks, cfg, st, (f - 1) as u64)));
                        }
                    }
                    return (Err(y), Ghost(a));
                },
            };
            let idx = self.add_expr(PNode::Paren(x), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(a.st), Ghost(Node::Paren(a.node)), Ghost(inc(a.h)));
            let ghost g = add_node(a.st, Node::Paren(a.node), inc(a.h));
            proof {
                assert forall|f: u64| #![trigger p_primary(toks, cfg, st, f)] pdone(p_primary(toks, cfg, st, f)) implies p_primary(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_parenthesized(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (Ok((idx, h + 1)), Ghost(g));
        }
        if matches!(k, TokenType::Length) || matches!(k, TokenType::Sqrt) {
            let which = if matches!(k, TokenType::Length) { 0 } else { 1 };
            let (res, Ghost(a)) = self.parse_builtin(which, Ghost(toks), Ghost(cfg), Ghost(st));
            proof {
                assert forall|f: u64| #![trigger p_primary(toks, cfg, st, f)] pdone(p_primary(toks, cfg, st, f)) implies p_primary(toks, cfg, st, f) == a by {
                    assert(f > 0);
                    assert(pdone(p_builtin(toks, cfg, st, which, (f - 1) as u64)));
                }
            }
            return (res, Ghost(a));
        }
        if matches!(k, TokenType::Scale) || matches!(k, TokenType::Letter) {
            let ghost pk = peek_kind(toks, st, 0usize);
            let next = match self.peek_token_type(0, Ghost(toks), Ghost(cfg), Ghost(st)) {
                Ok(n) => n,
                Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_primary(toks, cfg, st, f)] pdone(p_primary(toks, cfg, st, f)) implies p_primary(toks, cfg, st, f) == lex_err(st, pk.2) by {
                        assert(f > 0);
                    }
                }
                    return (Err(x), Ghost(lex_err(st, pk.2)));
                },
            };
            if matches!(next, TokenType::Lparen) {
                if matches!(k, TokenType::Scale) {
                    let (res, Ghost(a)) = self.parse_builtin(2, Ghost(toks), Ghost(cfg), Ghost(st));
                    proof {
                        assert forall|f: u64| #![trigger p_primary(toks, cfg, st, f)] pdone(p_primary(toks, cfg, st, f)) implies p_primary(toks, cfg, st, f) == a by {
                            assert(f > 0);
                            assert(pdone(p_builtin(toks, cfg, st, 2u8, (f - 1) as u64)));
                        }
                    }
                    return (res, Ghost(a));
                }
                let (res, Ghost(a)) = self.parse_call(Ghost(toks), Ghost(cfg), Ghost(st));
                proof {
                    assert forall|f: u64| #![trigger p_primary(toks, cfg, st, f)] pdone(p_primary(toks, cfg, st, f)) implies p_primary(toks, cfg, st, f) == a by {
                        assert(f > 0);
                        assert(pdone(p_call(toks, cfg, st, (f - 1) as u64)));
                    }
                }
                return (res, Ghost(a));
            }
        }
        let (res, Ghost(a)) = self.parse_named_tail(Ghost(toks), Ghost(cfg), Ghost(st));
        proof {
                assert forall|f: u64| #![trigger p_primary(toks, cfg, st, f)] pdone(p_primary(toks, cfg, st, f)) implies p_primary(toks, cfg, st, f) == a by {
                    assert(f > 0);
                    assert(pdone(p_named_tail(toks, cfg, st, (f - 1) as u64)));
                }
        }
        (res, Ghost(a))
    }

    /// Parses a function call `name(args)`.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_call(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is Letter,
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_call(toks, cfg, st, f)] pdone(p_call(toks, cfg, st, f)) ==> p_call(toks, cfg, st, f) == r.1@,
    {
        let ghost n = s_eat_name(toks, cfg, st);
        let name = match self.eat_name(Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(x) => x,
            Err(x) => return (Err(x), Ghost(n)),
        };
        let ghost e = s_eat(toks, n.st, Tok::Lparen);
        match self.eat(TokenType::Lparen, Ghost(toks), Ghost(cfg), Ghost(n.st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e)),
        }
        let ghost empty = cur_tok(toks, e.st).kind is Rparen;
        let (res, Ghost(a)) = if matches!(self.current_token.token_type, TokenType::Rparen) {
            (Ok((Vec::new(), 0)), Ghost(pr_args(e.st, seq![], 0u64)))
        } else {
            self.parse_argument_list(Ghost(toks), Ghost(cfg), Ghost(e.st))
        };
        let (args, h) = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_call(toks, cfg, st, f)] pdone(p_call(toks, cfg, st, f)) implies p_call(toks, cfg, st, f) == a by {
                        assert(f > 0);
                        if !empty { assert(pdone(p_arg_list(toks, cfg, e.st, seq![], 0u64, (f - 1) as u64))); }
                    }
                }
                return (Err(x), Ghost(a));
            },
        };
        let ghost e2 = s_eat(toks, a.st, Tok::Rparen);
        match self.eat(TokenType::Rparen, Ghost(toks), Ghost(cfg), Ghost(a.st)) {
            Ok(()) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_call(toks, cfg, st, f)] pdone(p_call(toks, cfg, st, f)) implies p_call(toks, cfg, st, f) == e2 by {
                        assert(f > 0);
                        if !empty { assert(pdone(p_arg_list(toks, cfg, e.st, seq![], 0u64, (f - 1) as u64))); }
                    }
                }
                return (Err(x), Ghost(e2));
            },
        }
        let idx = self.add_expr(PNode::Call(name, args), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e2.st), Ghost(Node::Call(n.name, a.args)), Ghost(inc(a.h)));
        let ghost g = add_node(e2.st, Node::Call(n.name, a.args), inc(a.h));
        proof {
            assert forall|f: u64| #![trigger p_call(toks, cfg, st, f)] pdone(p_call(toks, cfg, st, f)) implies p_call(toks, cfg, st, f) == g by {
                assert(f > 0);
                if !empty { assert(pdone(p_arg_list(toks, cfg, e.st, seq![], 0u64, (f - 1) as u64))); }
            }
        }
        (Ok((idx, h + 1)), Ghost(g))
    }

    /// Parses a named expression, then a postfix `++`/`--` or an assignment that binds to it.
    #[verifier::rlimit(40)]
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_named_tail(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) ==> p_named_tail(toks, cfg, st, f) == r.1@,
    {
        let (res, Ghost(a)) = self.parse_named_expression(Ghost(toks), Ghost(cfg), Ghost(st));
        let (target, target_h) = match res {
            Ok(v) => v,
            Err(y) => {
                proof {
                    assert forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) implies p_named_tail(toks, cfg, st, f) == a by {
                        assert(f > 0);
                        assert(pdone(p_named(toks, cfg, st, (f - 1) as u64)));
                    }
                }
                return (Err(y), Ghost(a));
            },
        };
        let ghost t = cur_tok(toks, a.st);
        let k = self.current_token.token_type;
        if matches!(k, TokenType::IncrDecr) {
            let is_inc = is_increment(&self.current_token);
            let ghost e = s_eat(toks, a.st, Tok::IncrDecr);
            match self.eat(TokenType::IncrDecr, Ghost(toks), Ghost(cfg), Ghost(a.st)) {
                Ok(()) => {},
                Err(x) => {
                    proof {
                        assert forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) implies p_named_tail(toks, cfg, st, f) == e by {
                            assert(f > 0);
                            assert(pdone(p_named(toks, cfg, st, (f - 1) as u64)));
                        }
                    }
                    return (Err(x), Ghost(e));
                },
            }
            let idx = self.add_expr(PNode::Update(is_inc, false, target), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e.st), Ghost(Node::Update(is_inc, false, a.node)), Ghost(inc(a.h)));
            let ghost g = add_node(e.st, Node::Update(is_inc, false, a.node), inc(a.h));
            proof {
                assert forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) implies p_named_tail(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_named(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (Ok((idx, target_h + 1)), Ghost(g));
        }
        if matches!(k, TokenType::AssignOp) {
            // As in GNU bc's grammar, an assignment operator binds to the named
            // expression right before it: `a + b = 3` is `a + (b = 3)` and `-a = 5`
            // is `-(a = 5)`. The right-hand side extends as far as possible.
            let op = assign_op(&self.current_token);
            let ghost e = s_eat(toks, a.st, Tok::AssignOp);
            match self.eat(TokenType::AssignOp, Ghost(toks), Ghost(cfg), Ghost(a.st)) {
                Ok(()) => {},
                Err(x) => {
                    proof {
                        assert forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) implies p_named_tail(toks, cfg, st, f) == e by {
                            assert(f > 0);
                            assert(pdone(p_named(toks, cfg, st, (f - 1) as u64)));
                        }
                    }
                    return (Err(x), Ghost(e));
                },
            }
            let (_, _, rhs_min_prec) = verified_pratt_infix_info(TOK_ASSIGN_OP);
            let (res2, Ghost(v)) = self.parse_expr_precedence(rhs_min_prec, Ghost(toks), Ghost(cfg), Ghost(e.st));
            let (value, value_h) = match res2 {
                Ok(w) => w,
                Err(x) => {
                    proof {
                        assert forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) implies p_named_tail(toks, cfg, st, f) == v by {
                            assert(f > 0);
                            assert(pdone(p_named(toks, cfg, st, (f - 1) as u64)));
                            assert(pdone(p_expr_prec(toks, cfg, e.st, 1i8, (f - 1) as u64)));
                        }
                    }
                    return (Err(x), Ghost(v));
                },
            };
            let ghost nd = Node::Assign(s_assign_code(t), a.node, v.node);
            let idx = self.add_expr(PNode::Assign(op, target, value), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(v.st), Ghost(nd), Ghost(inc(max_u64(a.h, v.h))));
            let ghost g = add_node(v.st, nd, inc(max_u64(a.h, v.h)));
            proof {
                assert forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) implies p_named_tail(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_named(toks, cfg, st, (f - 1) as u64)));
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 1i8, (f - 1) as u64)));
                }
            }
            let h = 1 + max_height(target_h, value_h);
            return (Ok((idx, h)), Ghost(g));
        }
        proof {
                assert forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) implies p_named_tail(toks, cfg, st, f) == a by {
                    assert(f > 0);
                    assert(pdone(p_named(toks, cfg, st, (f - 1) as u64)));
                }
        }
        (Ok((target, target_h)), Ghost(a))
    }

    /// Parses variables, arrays, or register accesses.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_named_expression(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            r.0 matches Ok((_, h)) ==> h <= final(self).max_depth + 1,
            forall|f: u64| #![trigger p_named(toks, cfg, st, f)] pdone(p_named(toks, cfg, st, f)) ==> p_named(toks, cfg, st, f) == r.1@,
    {
        let ghost t = cur_tok(toks, st);
        let k = self.current_token.token_type;
        if matches!(k, TokenType::Scale) || matches!(k, TokenType::Ibase) || matches!(k, TokenType::Obase) {
            let reg = if matches!(k, TokenType::Scale) { Register::Scale } else if matches!(k, TokenType::Ibase) { Register::Ibase } else { Register::Obase };
            let ghost code: u8 = if t.kind is Scale { 0u8 } else if t.kind is Ibase { 1u8 } else { 2u8 };
            let ghost e = s_eat(toks, st, t.kind);
            match self.eat(k, Ghost(toks), Ghost(cfg), Ghost(st)) {
                Ok(()) => {},
                Err(x) => return (Err(x), Ghost(e)),
            }
            let idx = self.add_expr(PNode::Reg(reg), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e.st), Ghost(Node::Reg(code)), Ghost(1u64));
            let ghost g = add_node(e.st, Node::Reg(code), 1u64);
            return (Ok((idx, 1)), Ghost(g));
        }
        if matches!(k, TokenType::Letter) {
            let ghost n = s_eat_name(toks, cfg, st);
            let name = match self.eat_name(Ghost(toks), Ghost(cfg), Ghost(st)) {
                Ok(x) => x,
                Err(x) => return (Err(x), Ghost(n)),
            };
            if matches!(self.current_token.token_type, TokenType::Lbracket) {
                let (res, Ghost(a)) = self.parse_subscript(name, Ghost(n.name), Ghost(toks), Ghost(cfg), Ghost(n.st));
                proof {
                    assert(n.st.cur > st.cur);
                    assert(n.st.nodes.s.len() == st.nodes.s.len());
                    assert forall|f: u64| #![trigger p_named(toks, cfg, st, f)] pdone(p_named(toks, cfg, st, f)) implies p_named(toks, cfg, st, f) == a by {
                        assert(f > 0);
                        assert(pdone(p_subscript(toks, cfg, n.st, n.name, (f - 1) as u64)));
                    }
                }
                return (res, Ghost(a));
            }
            let idx = self.add_expr(PNode::Var(name), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(n.st), Ghost(Node::Var(n.name)), Ghost(1u64));
            let ghost g = add_node(n.st, Node::Var(n.name), 1u64);
            return (Ok((idx, 1)), Ghost(g));
        }
        (Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() }), Ghost(syntax_at(st, t.line)))
    }

    /// Parses `[ expression ]` after the array name `name`.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_subscript(&mut self, name: String, Ghost(sname): Ghost<GBytes>, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(usize, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            text_view(name) == sname,
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            r.0 matches Ok((x, h)) ==> h <= final(self).max_depth + 1,
            forall|f: u64| #![trigger p_subscript(toks, cfg, st, sname, f)] pdone(p_subscript(toks, cfg, st, sname, f)) ==> p_subscript(toks, cfg, st, sname, f) == r.1@,
    {
        let ghost e = s_eat(toks, st, Tok::Lbracket);
        match self.eat(TokenType::Lbracket, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e)),
        }
        let (res, Ghost(a)) = self.parse_expr_precedence(0, Ghost(toks), Ghost(cfg), Ghost(e.st));
        let (idx, h) = match res {
            Ok(v) => v,
            Err(y) => {
                proof {
                    assert forall|f: u64| #![trigger p_subscript(toks, cfg, st, sname, f)] pdone(p_subscript(toks, cfg, st, sname, f)) implies p_subscript(toks, cfg, st, sname, f) == a by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(y), Ghost(a));
            },
        };
        let ghost e2 = s_eat(toks, a.st, Tok::Rbracket);
        match self.eat(TokenType::Rbracket, Ghost(toks), Ghost(cfg), Ghost(a.st)) {
            Ok(()) => {},
            Err(y) => {
                proof {
                    assert forall|f: u64| #![trigger p_subscript(toks, cfg, st, sname, f)] pdone(p_subscript(toks, cfg, st, sname, f)) implies p_subscript(toks, cfg, st, sname, f) == e2 by {
                        assert(f > 0);
                        assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                    }
                }
                return (Err(y), Ghost(e2));
            },
        }
        let node_idx = self.add_expr(PNode::Array(name, idx), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e2.st), Ghost(Node::Array(sname, a.node)), Ghost(inc(a.h)));
        let ghost g = add_node(e2.st, Node::Array(sname, a.node), inc(a.h));
        proof {
                assert forall|f: u64| #![trigger p_subscript(toks, cfg, st, sname, f)] pdone(p_subscript(toks, cfg, st, sname, f)) implies p_subscript(toks, cfg, st, sname, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                }
        }
        (Ok((node_idx, h + 1)), Ghost(g))
    }

    /// Parses function call argument list; the height is that of the highest argument.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::type_complexity, reason = "every parser function returns its result with the Ghost result of the specification")]
    fn parse_argument_list(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Vec<PArg>, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_ares(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_arg_list(toks, cfg, st, seq![], 0u64, f)] pdone(p_arg_list(toks, cfg, st, seq![], 0u64, f)) ==> p_arg_list(toks, cfg, st, seq![], 0u64, f) == r.1@,
    {
        let mut args: Vec<PArg> = Vec::new();
        let mut height: usize = 0;
        let ghost mut cur = st;
        let ghost mut acc = Seq::<Arg>::empty();
        let ghost mut sh = 0u64;
        proof {
            assert(args@ =~= Seq::<PArg>::empty());
            lemma_al_start(toks, cfg, st);
        }
        loop
            invariant
                r_p(*self, toks, cfg, cur),
                extends(st.nodes.s, cur.nodes.s),
                cur.cur >= st.cur,
                cur.nodes.s.len() - st.nodes.s.len() <= cur.cur - st.cur,
                cur.depth == st.depth,
                st.nodes.s.len() <= 2 * st.cur,
                r_args(args@, acc),
                height as u64 == sh,
                height <= self.max_depth + 1,
                al_chain(toks, cfg, st, cur, acc, sh),
        {
            let ghost (c, a0, h0) = (cur, acc, sh);
            let ghost old_args = args@;
            let is_letter = matches!(self.current_token.token_type, TokenType::Letter);
            let ghost p0 = if is_letter { peek_kind(toks, c, 0usize) } else { (true, Tok::Eof, cur_tok(toks, c)) };
            let mut is_arr = false;
            let ghost mut p1 = (true, Tok::Eof, cur_tok(toks, c));
            if is_letter {
                let k0 = match self.peek_token_type(0, Ghost(toks), Ghost(cfg), Ghost(c)) {
                    Ok(k) => k,
                    Err(x) => {
                        let ghost g = lex_err(c, p0.2);
                        proof {
                        assert forall|k: u64| #![trigger p_arg_list(toks, cfg, c, a0, h0, k)] k > 0 && pdone(p_arg_list(toks, cfg, c, a0, h0, k)) implies p_arg_list(toks, cfg, c, a0, h0, k) == g by {}
                        lemma_al_ret(toks, cfg, st, c, a0, h0, g);
                    }
                    return (Err(x), Ghost(g));
                    },
                };
                if matches!(k0, TokenType::Lbracket) {
                    proof { p1 = peek_kind(toks, c, 1usize); }
                    let k1 = match self.peek_token_type(1, Ghost(toks), Ghost(cfg), Ghost(c)) {
                        Ok(k) => k,
                        Err(x) => {
                            let ghost g = lex_err(c, p1.2);
                            proof {
                        assert forall|k: u64| #![trigger p_arg_list(toks, cfg, c, a0, h0, k)] k > 0 && pdone(p_arg_list(toks, cfg, c, a0, h0, k)) implies p_arg_list(toks, cfg, c, a0, h0, k) == g by {}
                        lemma_al_ret(toks, cfg, st, c, a0, h0, g);
                    }
                    return (Err(x), Ghost(g));
                        },
                    };
                    is_arr = matches!(k1, TokenType::Rbracket);
                }
            }
            let ghost mut a = pr_ok(c);
            let arg_h: usize = if is_arr {
                let ghost n = s_eat_name(toks, cfg, c);
                let name = match self.eat_name(Ghost(toks), Ghost(cfg), Ghost(c)) {
                    Ok(x) => x,
                    Err(x) => {
                        proof {
                        assert forall|g: u64| #![trigger p_arg_list(toks, cfg, c, a0, h0, g)] g > 0 && pdone(p_arg_list(toks, cfg, c, a0, h0, g)) implies p_arg_list(toks, cfg, c, a0, h0, g) == n by {}
                        lemma_al_ret(toks, cfg, st, c, a0, h0, n);
                    }
                    return (Err(x), Ghost(n));
                    },
                };
                let ghost e1 = s_eat(toks, n.st, Tok::Lbracket);
                match self.eat(TokenType::Lbracket, Ghost(toks), Ghost(cfg), Ghost(n.st)) {
                    Ok(()) => {},
                    Err(x) => {
                        proof {
                        assert forall|g: u64| #![trigger p_arg_list(toks, cfg, c, a0, h0, g)] g > 0 && pdone(p_arg_list(toks, cfg, c, a0, h0, g)) implies p_arg_list(toks, cfg, c, a0, h0, g) == e1 by {}
                        lemma_al_ret(toks, cfg, st, c, a0, h0, e1);
                    }
                    return (Err(x), Ghost(e1));
                    },
                }
                let ghost e2 = s_eat(toks, e1.st, Tok::Rbracket);
                match self.eat(TokenType::Rbracket, Ghost(toks), Ghost(cfg), Ghost(e1.st)) {
                    Ok(()) => {},
                    Err(x) => {
                        proof {
                        assert forall|g: u64| #![trigger p_arg_list(toks, cfg, c, a0, h0, g)] g > 0 && pdone(p_arg_list(toks, cfg, c, a0, h0, g)) implies p_arg_list(toks, cfg, c, a0, h0, g) == e2 by {}
                        lemma_al_ret(toks, cfg, st, c, a0, h0, e2);
                    }
                    return (Err(x), Ghost(e2));
                    },
                }
                proof {
                    a = PR { ok: true, err: no_err(), st: e2.st, node: 0usize, h: 1u64, flag: false, list: seq![], params: seq![], args: seq![], name: n.name };
                }
                args.push(PArg::Array(name));
                proof { assert(r_arg(args@.last(), Arg { is_array: is_arr, name: a.name, expr: a.node })); }
                1
            } else {
                let (res, Ghost(v)) = self.parse_expr_precedence(0, Ghost(toks), Ghost(cfg), Ghost(c));
                let (x, h) = match res {
                    Ok(w) => w,
                    Err(y) => {
                        proof {
                        assert forall|g: u64| #![trigger p_arg_list(toks, cfg, c, a0, h0, g)] g > 0 && pdone(p_arg_list(toks, cfg, c, a0, h0, g)) implies p_arg_list(toks, cfg, c, a0, h0, g) == v by {
                            assert(pdone(p_expr_prec(toks, cfg, c, 0i8, (g - 1) as u64)));
                        }
                        lemma_al_ret(toks, cfg, st, c, a0, h0, v);
                    }
                    return (Err(y), Ghost(v));
                    },
                };
                proof {
                    a = v;
                }
                args.push(PArg::Expr(x));
                proof { assert(r_arg(args@.last(), Arg { is_array: is_arr, name: a.name, expr: a.node })); }
                h
            };
            let ghost arg_s = Arg { is_array: is_arr, name: a.name, expr: a.node };
            let ghost a1 = a0.push(arg_s);
            let ghost h1 = max_u64(h0, a.h);
            proof {
                assert(args@ =~= old_args.push(args@.last()));
                lemma_r_args_push(old_args, a0, args@.last(), arg_s);
            }
            height = max_height(height, arg_h);
            if !matches!(self.current_token.token_type, TokenType::Comma) {
                let ghost g = pr_args(a.st, a1, h1);
                proof {
                        assert forall|k: u64| #![trigger p_arg_list(toks, cfg, c, a0, h0, k)] k > 0 && pdone(p_arg_list(toks, cfg, c, a0, h0, k)) implies p_arg_list(toks, cfg, c, a0, h0, k) == g by {
                            if !is_arr { assert(pdone(p_expr_prec(toks, cfg, c, 0i8, (k - 1) as u64))); }
                        }
                        lemma_al_ret(toks, cfg, st, c, a0, h0, g);
                    }
                    return (Ok((args, height)), Ghost(g));
            }
            let ghost e = s_eat(toks, a.st, Tok::Comma);
            match self.eat(TokenType::Comma, Ghost(toks), Ghost(cfg), Ghost(a.st)) {
                Ok(()) => {
                    proof {
                        assert forall|g: u64| #![trigger p_arg_list(toks, cfg, c, a0, h0, g)] g > 0 && pdone(p_arg_list(toks, cfg, c, a0, h0, g)) implies p_arg_list(toks, cfg, c, a0, h0, g) == p_arg_list(toks, cfg, e.st, a1, h1, (g - 1) as u64) by {
                            if !is_arr { assert(pdone(p_expr_prec(toks, cfg, c, 0i8, (g - 1) as u64))); }
                        }
                        lemma_al_next(toks, cfg, st, c, a0, h0, e.st, a1, h1);
                        cur = e.st;
                        acc = a1;
                        sh = h1;
                    }
                },
                Err(x) => {
                    proof {
                        assert forall|g: u64| #![trigger p_arg_list(toks, cfg, c, a0, h0, g)] g > 0 && pdone(p_arg_list(toks, cfg, c, a0, h0, g)) implies p_arg_list(toks, cfg, c, a0, h0, g) == e by {
                            if !is_arr { assert(pdone(p_expr_prec(toks, cfg, c, 0i8, (g - 1) as u64))); }
                        }
                        lemma_al_ret(toks, cfg, st, c, a0, h0, e);
                    }
                    return (Err(x), Ghost(e));
                },
            }
        }
    }
}

spec fn al_chain(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<Arg>, h: u64) -> bool {
    forall|f: u64| #![trigger p_arg_list(toks, cfg, st, seq![], 0u64, f)] pdone(p_arg_list(toks, cfg, st, seq![], 0u64, f)) ==>
        exists|g: u64| #![trigger p_arg_list(toks, cfg, cur, acc, h, g)] p_arg_list(toks, cfg, cur, acc, h, g) == p_arg_list(toks, cfg, st, seq![], 0u64, f)
}

proof fn lemma_al_start(toks: Seq<SToken>, cfg: PCfg, st: PState)
    ensures
        al_chain(toks, cfg, st, st, Seq::<Arg>::empty(), 0u64),
{
    let e = Seq::<Arg>::empty();
    assert(seq![] == e);
    assert forall|f: u64| #![trigger p_arg_list(toks, cfg, st, seq![], 0u64, f)] pdone(p_arg_list(toks, cfg, st, seq![], 0u64, f)) implies
        exists|g: u64| #![trigger p_arg_list(toks, cfg, st, e, 0u64, g)] p_arg_list(toks, cfg, st, e, 0u64, g) == p_arg_list(toks, cfg, st, seq![], 0u64, f) by {
        assert(p_arg_list(toks, cfg, st, e, 0u64, f) == p_arg_list(toks, cfg, st, seq![], 0u64, f));
    }
}

proof fn lemma_al_ret(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<Arg>, h: u64, r: PR)
    requires
        al_chain(toks, cfg, st, cur, acc, h),
        forall|g: u64| #![trigger p_arg_list(toks, cfg, cur, acc, h, g)] g > 0 && pdone(p_arg_list(toks, cfg, cur, acc, h, g)) ==> p_arg_list(toks, cfg, cur, acc, h, g) == r,
    ensures
        forall|f: u64| #![trigger p_arg_list(toks, cfg, st, seq![], 0u64, f)] pdone(p_arg_list(toks, cfg, st, seq![], 0u64, f)) ==> p_arg_list(toks, cfg, st, seq![], 0u64, f) == r,
{
    assert forall|f: u64| #![trigger p_arg_list(toks, cfg, st, seq![], 0u64, f)] pdone(p_arg_list(toks, cfg, st, seq![], 0u64, f)) implies p_arg_list(toks, cfg, st, seq![], 0u64, f) == r by {
        let g = choose|g: u64| #![trigger p_arg_list(toks, cfg, cur, acc, h, g)] p_arg_list(toks, cfg, cur, acc, h, g) == p_arg_list(toks, cfg, st, seq![], 0u64, f);
        assert(g > 0);
    }
}

proof fn lemma_al_next(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<Arg>, h: u64, cur2: PState, acc2: Seq<Arg>, h2: u64)
    requires
        al_chain(toks, cfg, st, cur, acc, h),
        forall|g: u64| #![trigger p_arg_list(toks, cfg, cur, acc, h, g)] g > 0 && pdone(p_arg_list(toks, cfg, cur, acc, h, g)) ==> p_arg_list(toks, cfg, cur, acc, h, g) == p_arg_list(toks, cfg, cur2, acc2, h2, (g - 1) as u64),
    ensures
        al_chain(toks, cfg, st, cur2, acc2, h2),
{
    assert forall|f: u64| #![trigger p_arg_list(toks, cfg, st, seq![], 0u64, f)] pdone(p_arg_list(toks, cfg, st, seq![], 0u64, f)) implies
        exists|g: u64| #![trigger p_arg_list(toks, cfg, cur2, acc2, h2, g)] p_arg_list(toks, cfg, cur2, acc2, h2, g) == p_arg_list(toks, cfg, st, seq![], 0u64, f) by {
        let g = choose|g: u64| #![trigger p_arg_list(toks, cfg, cur, acc, h, g)] p_arg_list(toks, cfg, cur, acc, h, g) == p_arg_list(toks, cfg, st, seq![], 0u64, f);
        assert(g > 0);
        assert(p_arg_list(toks, cfg, cur2, acc2, h2, (g - 1) as u64) == p_arg_list(toks, cfg, st, seq![], 0u64, f));
    }
}

/// `p_expr_loop` ends with `r` at this step.
proof fn lemma_loop_ret(toks: Seq<SToken>, cfg: PCfg, st: PState, min_prec: i8, c: PState, n: usize, h: u64, r: PR)
    requires
        forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) ==>
            exists|g: u64| #![trigger p_expr_loop(toks, cfg, c, n, h, min_prec, g)] p_expr_loop(toks, cfg, c, n, h, min_prec, g) == p_inner(toks, cfg, st, min_prec, f),
        forall|g: u64| #![trigger p_expr_loop(toks, cfg, c, n, h, min_prec, g)] g > 0 && pdone(p_expr_loop(toks, cfg, c, n, h, min_prec, g)) ==> p_expr_loop(toks, cfg, c, n, h, min_prec, g) == r,
    ensures
        forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) ==> p_inner(toks, cfg, st, min_prec, f) == r,
{
    assert forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) implies p_inner(toks, cfg, st, min_prec, f) == r by {
        let g = choose|g: u64| #![trigger p_expr_loop(toks, cfg, c, n, h, min_prec, g)] p_expr_loop(toks, cfg, c, n, h, min_prec, g) == p_inner(toks, cfg, st, min_prec, f);
        assert(g > 0);
    }
}

/// `p_expr_loop` continues from `c2`.
proof fn lemma_loop_next(toks: Seq<SToken>, cfg: PCfg, st: PState, min_prec: i8, c: PState, n: usize, h: u64, c2: PState, n2: usize, h2: u64)
    requires
        forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) ==>
            exists|g: u64| #![trigger p_expr_loop(toks, cfg, c, n, h, min_prec, g)] p_expr_loop(toks, cfg, c, n, h, min_prec, g) == p_inner(toks, cfg, st, min_prec, f),
        forall|g: u64| #![trigger p_expr_loop(toks, cfg, c, n, h, min_prec, g)] g > 0 && pdone(p_expr_loop(toks, cfg, c, n, h, min_prec, g)) ==> p_expr_loop(toks, cfg, c, n, h, min_prec, g) == p_expr_loop(toks, cfg, c2, n2, h2, min_prec, (g - 1) as u64),
    ensures
        forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) ==>
            exists|g: u64| #![trigger p_expr_loop(toks, cfg, c2, n2, h2, min_prec, g)] p_expr_loop(toks, cfg, c2, n2, h2, min_prec, g) == p_inner(toks, cfg, st, min_prec, f),
{
    assert forall|f: u64| #![trigger p_inner(toks, cfg, st, min_prec, f)] pdone(p_inner(toks, cfg, st, min_prec, f)) implies
        exists|g: u64| #![trigger p_expr_loop(toks, cfg, c2, n2, h2, min_prec, g)] p_expr_loop(toks, cfg, c2, n2, h2, min_prec, g) == p_inner(toks, cfg, st, min_prec, f) by {
        let g = choose|g: u64| #![trigger p_expr_loop(toks, cfg, c, n, h, min_prec, g)] p_expr_loop(toks, cfg, c, n, h, min_prec, g) == p_inner(toks, cfg, st, min_prec, f);
        assert(g > 0);
        assert(p_expr_loop(toks, cfg, c2, n2, h2, min_prec, (g - 1) as u64) == p_inner(toks, cfg, st, min_prec, f));
    }
}

} // verus!
