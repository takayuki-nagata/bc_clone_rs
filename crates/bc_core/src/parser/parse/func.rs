// SPDX-License-Identifier: MIT

//! Function definitions (the specification's `p_function` to `p_function_stmts`) and their
//! parameter and `auto` lists (`p_define_list`, `p_opt_auto`).

use super::*;

verus! {

spec fn r_plist(r: Result<Vec<Param>, BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(l) => p.ok && r_p(q, toks, cfg, p.st) && p.st.nodes == s0.nodes && p.st.cur >= s0.cur && p.st.depth == s0.depth && r_params(l@, p.params),
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

/// The diagnostic or description `end_of_line`.
fn end_of_line_text() -> (r: String)
    ensures
        text_view(r) == eol_msg(),
{
    let m = [69u8, 110, 100, 32, 111, 102, 32, 108, 105, 110, 101, 32, 114, 101, 113, 117, 105, 114, 101, 100];
    proof { assert(m@ =~= eol_msg()); }
    ascii_string(m.as_slice())
}

impl Parser {
    /// Parses optional parameters.
    fn parse_opt_define_list(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Vec<Param>, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_plist(r.0, *final(self), toks, cfg, st, r.1@),
            cur_tok(toks, st).kind is Rparen ==> r.1@ == pr_params(st, seq![]),
            !(cur_tok(toks, st).kind is Rparen) ==>
                forall|f: u64| #![trigger p_define_list(toks, cfg, st, seq![], f)] pdone(p_define_list(toks, cfg, st, seq![], f)) ==> p_define_list(toks, cfg, st, seq![], f) == r.1@,
    {
        if matches!(self.current_token.token_type, TokenType::Rparen) {
            (Ok(Vec::new()), Ghost(pr_params(st, seq![])))
        } else {
            self.parse_define_list(Ghost(toks), Ghost(cfg), Ghost(st))
        }
    }

    /// Parses a define list of parameters or auto variables.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_define_list(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Vec<Param>, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_plist(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_define_list(toks, cfg, st, seq![], f)] pdone(p_define_list(toks, cfg, st, seq![], f)) ==> p_define_list(toks, cfg, st, seq![], f) == r.1@,
    {
        let mut lst: Vec<Param> = Vec::new();
        let ghost mut cur = st;
        let ghost mut acc = Seq::<SParam>::empty();
        proof { lemma_dl_start(toks, cfg, st); }
        loop
            invariant
                r_p(*self, toks, cfg, cur),
                cur.nodes == st.nodes,
                cur.cur >= st.cur,
                cur.depth == st.depth,
                r_params(lst@, acc),
                dl_chain(toks, cfg, st, cur, acc),
        {
            let ghost c = cur;
            let ghost a0 = acc;
            if !matches!(self.current_token.token_type, TokenType::Letter) {
                let ghost e = syntax_at(c, cur_tok(toks, c).line);
                proof {
                    assert forall|g: u64| g > 0 implies #[trigger] p_define_list(toks, cfg, c, a0, g) == e by {}
                    lemma_dl_ret(toks, cfg, st, c, a0, e);
                }
                return (Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() }), Ghost(e));
            }
            let ghost n = s_eat_name(toks, cfg, c);
            let name = match self.eat_name(Ghost(toks), Ghost(cfg), Ghost(c)) {
                Ok(x) => x,
                Err(x) => {
                    proof {
                        assert forall|g: u64| g > 0 implies #[trigger] p_define_list(toks, cfg, c, a0, g) == n by {}
                        lemma_dl_ret(toks, cfg, st, c, a0, n);
                    }
                    return (Err(x), Ghost(n));
                },
            };
            let ghost mut s1 = n.st;
            let mut is_arr = false;
            if matches!(self.current_token.token_type, TokenType::Lbracket) {
                let ghost e1 = s_eat(toks, n.st, Tok::Lbracket);
                match self.eat(TokenType::Lbracket, Ghost(toks), Ghost(cfg), Ghost(n.st)) {
                    Ok(()) => {},
                    Err(x) => {
                        proof {
                            assert forall|g: u64| g > 0 implies #[trigger] p_define_list(toks, cfg, c, a0, g) == e1 by {}
                            lemma_dl_ret(toks, cfg, st, c, a0, e1);
                        }
                        return (Err(x), Ghost(e1));
                    },
                }
                let ghost e2 = s_eat(toks, e1.st, Tok::Rbracket);
                match self.eat(TokenType::Rbracket, Ghost(toks), Ghost(cfg), Ghost(e1.st)) {
                    Ok(()) => {},
                    Err(x) => {
                        proof {
                            assert forall|g: u64| g > 0 implies #[trigger] p_define_list(toks, cfg, c, a0, g) == e2 by {}
                            lemma_dl_ret(toks, cfg, st, c, a0, e2);
                        }
                        return (Err(x), Ghost(e2));
                    },
                }
                is_arr = true;
                proof { s1 = e2.st; }
            }
            let ghost a1 = a0.push(SParam { name: n.name, is_array: is_arr });
            let ghost l0 = lst@;
            let p = Param { name, is_array: is_arr };
            lst.push(p);
            proof {
                assert forall|i: int| 0 <= i < lst@.len() implies #[trigger] r_param(lst@[i], a1[i]) by {
                    if i < l0.len() { assert(lst@[i] == l0[i]); assert(a1[i] == a0[i]); assert(r_param(l0[i], a0[i])); }
                }
            }
            if !matches!(self.current_token.token_type, TokenType::Comma) {
                let ghost e = pr_params(s1, a1);
                proof {
                    assert forall|g: u64| g > 0 implies #[trigger] p_define_list(toks, cfg, c, a0, g) == e by {}
                    lemma_dl_ret(toks, cfg, st, c, a0, e);
                }
                return (Ok(lst), Ghost(e));
            }
            let ghost e3 = s_eat(toks, s1, Tok::Comma);
            match self.eat(TokenType::Comma, Ghost(toks), Ghost(cfg), Ghost(s1)) {
                Ok(()) => {
                    proof {
                        assert forall|g: u64| g > 0 implies #[trigger] p_define_list(toks, cfg, c, a0, g) == p_define_list(toks, cfg, e3.st, a1, (g - 1) as u64) by {}
                        lemma_dl_next(toks, cfg, st, c, a0, e3.st, a1);
                        cur = e3.st;
                        acc = a1;
                    }
                },
                Err(x) => {
                    proof {
                        assert forall|g: u64| g > 0 implies #[trigger] p_define_list(toks, cfg, c, a0, g) == e3 by {}
                        lemma_dl_ret(toks, cfg, st, c, a0, e3);
                    }
                    return (Err(x), Ghost(e3));
                },
            }
        }
    }

    /// Parses auto list declarations `auto a, b[]`.
    fn parse_opt_auto_define_list(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Vec<Param>, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_plist(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_opt_auto(toks, cfg, st, f)] pdone(p_opt_auto(toks, cfg, st, f)) ==> p_opt_auto(toks, cfg, st, f) == r.1@,
    {
        if !matches!(self.current_token.token_type, TokenType::Auto) {
            return (Ok(Vec::new()), Ghost(pr_params(st, seq![])));
        }
        let ghost e = s_eat(toks, st, Tok::Auto);
        match self.eat(TokenType::Auto, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e)),
        }
        let (res, Ghost(l)) = self.parse_define_list(Ghost(toks), Ghost(cfg), Ghost(e.st));
        let lst = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_opt_auto(toks, cfg, st, f)] pdone(p_opt_auto(toks, cfg, st, f)) implies p_opt_auto(toks, cfg, st, f) == l by {
                        assert(f > 0);
                        assert(pdone(p_define_list(toks, cfg, e.st, seq![], (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(l));
            },
        };
        let ghost lk = cur_tok(toks, l.st).kind;
        let ghost e2 = if lk is Newline { s_eat(toks, l.st, Tok::Newline) }
            else if lk is Semicolon { s_eat(toks, l.st, Tok::Semicolon) }
            else { syntax_at(l.st, cur_tok(toks, l.st).line) };
        let res2 = if matches!(self.current_token.token_type, TokenType::Newline) {
            self.eat(TokenType::Newline, Ghost(toks), Ghost(cfg), Ghost(l.st))
        } else if matches!(self.current_token.token_type, TokenType::Semicolon) {
            self.eat(TokenType::Semicolon, Ghost(toks), Ghost(cfg), Ghost(l.st))
        } else {
            Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() })
        };
        let ghost g = if e2.ok { pr_params(e2.st, l.params) } else { e2 };
        proof {
            assert forall|f: u64| #![trigger p_opt_auto(toks, cfg, st, f)] pdone(p_opt_auto(toks, cfg, st, f)) implies p_opt_auto(toks, cfg, st, f) == g by {
                assert(f > 0);
                assert(pdone(p_define_list(toks, cfg, e.st, seq![], (f - 1) as u64)));
            }
        }
        match res2 {
            Ok(()) => (Ok(lst), Ghost(g)),
            Err(x) => (Err(x), Ghost(g)),
        }
    }

}


spec fn dl_chain(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<SParam>) -> bool {
    forall|f: u64| #![trigger p_define_list(toks, cfg, st, seq![], f)] pdone(p_define_list(toks, cfg, st, seq![], f)) ==>
        exists|g: u64| #![trigger p_define_list(toks, cfg, cur, acc, g)] p_define_list(toks, cfg, cur, acc, g) == p_define_list(toks, cfg, st, seq![], f)
}

proof fn lemma_dl_start(toks: Seq<SToken>, cfg: PCfg, st: PState)
    ensures
        dl_chain(toks, cfg, st, st, Seq::<SParam>::empty()),
{
    let e = Seq::<SParam>::empty();
    assert(seq![] == e);
    assert forall|f: u64| #![trigger p_define_list(toks, cfg, st, seq![], f)] pdone(p_define_list(toks, cfg, st, seq![], f)) implies
        exists|g: u64| #![trigger p_define_list(toks, cfg, st, e, g)] p_define_list(toks, cfg, st, e, g) == p_define_list(toks, cfg, st, seq![], f) by {
        assert(p_define_list(toks, cfg, st, e, f) == p_define_list(toks, cfg, st, seq![], f));
    }
}

proof fn lemma_dl_ret(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<SParam>, r: PR)
    requires
        dl_chain(toks, cfg, st, cur, acc),
        forall|g: u64| g > 0 ==> #[trigger] p_define_list(toks, cfg, cur, acc, g) == r,
    ensures
        forall|f: u64| #![trigger p_define_list(toks, cfg, st, seq![], f)] pdone(p_define_list(toks, cfg, st, seq![], f)) ==> p_define_list(toks, cfg, st, seq![], f) == r,
{
    assert forall|f: u64| #![trigger p_define_list(toks, cfg, st, seq![], f)] pdone(p_define_list(toks, cfg, st, seq![], f)) implies p_define_list(toks, cfg, st, seq![], f) == r by {
        let g = choose|g: u64| #![trigger p_define_list(toks, cfg, cur, acc, g)] p_define_list(toks, cfg, cur, acc, g) == p_define_list(toks, cfg, st, seq![], f);
        assert(g > 0);
    }
}

proof fn lemma_dl_next(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<SParam>, cur2: PState, acc2: Seq<SParam>)
    requires
        dl_chain(toks, cfg, st, cur, acc),
        forall|g: u64| g > 0 ==> #[trigger] p_define_list(toks, cfg, cur, acc, g) == p_define_list(toks, cfg, cur2, acc2, (g - 1) as u64),
    ensures
        dl_chain(toks, cfg, st, cur2, acc2),
{
    assert forall|f: u64| #![trigger p_define_list(toks, cfg, st, seq![], f)] pdone(p_define_list(toks, cfg, st, seq![], f)) implies
        exists|g: u64| #![trigger p_define_list(toks, cfg, cur2, acc2, g)] p_define_list(toks, cfg, cur2, acc2, g) == p_define_list(toks, cfg, st, seq![], f) by {
        let g = choose|g: u64| #![trigger p_define_list(toks, cfg, cur, acc, g)] p_define_list(toks, cfg, cur, acc, g) == p_define_list(toks, cfg, st, seq![], f);
        assert(g > 0);
        assert(p_define_list(toks, cfg, cur2, acc2, (g - 1) as u64) == p_define_list(toks, cfg, st, seq![], f));
    }
}

impl Parser {
    /// Parses a function definition `define f(x) { ... }`.
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn parse_function(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is Define,
        ensures
            r_sres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_function(toks, cfg, st, f)] pdone(p_function(toks, cfg, st, f)) ==> p_function(toks, cfg, st, f) == r.1@,
    {
        let ghost e1 = s_eat(toks, st, Tok::Define);
        match self.eat(TokenType::Define, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e1)),
        }
        if !matches!(self.current_token.token_type, TokenType::Letter) {
            return (Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() }), Ghost(syntax_at(e1.st, cur_tok(toks, e1.st).line)));
        }
        proof { lemma_cur_ascii(toks, e1.st); }
        let ghost sname = cur_tok(toks, e1.st).text;
        let name = self.current_token.text();
        let name_bytes = self.current_token.value.clone();
        let ghost e2 = s_eat(toks, e1.st, Tok::Letter);
        match self.eat(TokenType::Letter, Ghost(toks), Ghost(cfg), Ghost(e1.st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e2)),
        }
        let ghost e3 = s_eat(toks, e2.st, Tok::Lparen);
        match self.eat(TokenType::Lparen, Ghost(toks), Ghost(cfg), Ghost(e2.st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e3)),
        }
        let ghost empty = cur_tok(toks, e3.st).kind is Rparen;
        let (res, Ghost(ps)) = self.parse_opt_define_list(Ghost(toks), Ghost(cfg), Ghost(e3.st));
        let params = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_function(toks, cfg, st, f)] pdone(p_function(toks, cfg, st, f)) implies p_function(toks, cfg, st, f) == ps by {
                        assert(f > 0);
                        if !empty { assert(pdone(p_define_list(toks, cfg, e3.st, seq![], (f - 1) as u64))); }
                    }
                }
                return (Err(x), Ghost(ps));
            },
        };
        let (res, Ghost(b)) = self.parse_function_body(name, name_bytes.as_slice(), params, Ghost(sname), Ghost(ps.params), Ghost(toks), Ghost(cfg), Ghost(ps.st));
        proof {
            assert forall|f: u64| #![trigger p_function(toks, cfg, st, f)] pdone(p_function(toks, cfg, st, f)) implies p_function(toks, cfg, st, f) == b by {
                assert(f > 0);
                if !empty { assert(pdone(p_define_list(toks, cfg, e3.st, seq![], (f - 1) as u64))); }
                assert(pdone(p_function_body(toks, cfg, ps.st, sname, ps.params, (f - 1) as u64)));
            }
        }
        (res, Ghost(b))
    }

    /// Parses the rest of a function definition after its parameter list.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn parse_function_body(&mut self, name: String, name_bytes: &[u8], params: Vec<Param>, Ghost(sname): Ghost<GBytes>, Ghost(sparams): Ghost<GParams>, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            text_view(name) == sname,
            name_bytes@ == sname,
            all_ascii(sname),
            r_params(params@, sparams),
        ensures
            match r.0 {
                Ok(x) => r.1@.ok && r.1@.flag && r_p(*final(self), toks, cfg, r.1@.st) && extends(st.nodes, r.1@.st.nodes) && r.1@.st.cur > st.cur
                    && r.1@.st.nodes.len() - st.nodes.len() <= 2 * (r.1@.st.cur - st.cur) && r.1@.st.depth == st.depth
                    && x == r.1@.node && x < r.1@.st.nodes.len(),
                Err(x) => r_perr(x, final(self).extension_uses@, r.1@),
            },
            forall|f: u64| #![trigger p_function_body(toks, cfg, st, sname, sparams, f)] pdone(p_function_body(toks, cfg, st, sname, sparams, f)) ==> p_function_body(toks, cfg, st, sname, sparams, f) == r.1@,
    {
        let ghost e4 = s_eat(toks, st, Tok::Rparen);
        match self.eat(TokenType::Rparen, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e4)),
        }
        let ghost e5 = s_eat(toks, e4.st, Tok::Lbrace);
        match self.eat(TokenType::Lbrace, Ghost(toks), Ghost(cfg), Ghost(e4.st)) {
            Ok(()) => {},
            Err(x) => return (Err(x), Ghost(e5)),
        }
        // POSIX requires a newline after `{`; GNU bc checks the name at this point too.
        let ghost st6 = if !(cur_tok(toks, e5.st).kind is Newline) { s_extension(toks, cfg, e5.st, eol_msg()) } else { e5.st };
        if !matches!(self.current_token.token_type, TokenType::Newline) {
            self.extension(end_of_line_text(), Ghost(toks), Ghost(cfg), Ghost(e5.st), Ghost(eol_msg()));
        }
        proof { assert(cur_tok(toks, st6) == cur_tok(toks, e5.st)); }
        self.note_name(name_bytes, Ghost(toks), Ghost(cfg), Ghost(st6));
        let ghost st7 = s_note_name(toks, cfg, st6, sname);
        proof { assert(cur_tok(toks, st7) == cur_tok(toks, st6)); }
        let (res, Ghost(sk)) = self.skip_newlines(Ghost(toks), Ghost(cfg), Ghost(st7));
        match res {
            Ok(()) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_function_body(toks, cfg, st, sname, sparams, f)] pdone(p_function_body(toks, cfg, st, sname, sparams, f)) implies p_function_body(toks, cfg, st, sname, sparams, f) == sk by {
                        assert(f > 0);
                        assert(pdone(p_skip_newlines(toks, st7, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(sk));
            },
        }
        let (res, Ghost(au)) = self.parse_opt_auto_define_list(Ghost(toks), Ghost(cfg), Ghost(sk.st));
        let autos = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_function_body(toks, cfg, st, sname, sparams, f)] pdone(p_function_body(toks, cfg, st, sname, sparams, f)) implies p_function_body(toks, cfg, st, sname, sparams, f) == au by {
                        assert(f > 0);
                        assert(pdone(p_skip_newlines(toks, st7, (f - 1) as u64)));
                        assert(pdone(p_opt_auto(toks, cfg, sk.st, (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(au));
            },
        };
        let (res, Ghost(b)) = self.parse_function_stmts(name, params, autos, Ghost(sname), Ghost(sparams), Ghost(au.params), Ghost(toks), Ghost(cfg), Ghost(au.st));
        proof {
            assert forall|f: u64| #![trigger p_function_body(toks, cfg, st, sname, sparams, f)] pdone(p_function_body(toks, cfg, st, sname, sparams, f)) implies p_function_body(toks, cfg, st, sname, sparams, f) == b by {
                assert(f > 0);
                assert(pdone(p_skip_newlines(toks, st7, (f - 1) as u64)));
                assert(pdone(p_opt_auto(toks, cfg, sk.st, (f - 1) as u64)));
                assert(pdone(p_function_stmts(toks, cfg, au.st, sname, sparams, au.params, (f - 1) as u64)));
            }
        }
        (res, Ghost(b))
    }

    /// Parses the statements of a function body, with `in_function` set and no enclosing loop.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::too_many_arguments, reason = "the Ghost arguments of the refinement proof")]
    fn parse_function_stmts(&mut self, name: String, params: Vec<Param>, autos: Vec<Param>, Ghost(sname): Ghost<GBytes>, Ghost(sparams): Ghost<GParams>, Ghost(sautos): Ghost<GParams>, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            text_view(name) == sname,
            r_params(params@, sparams),
            r_params(autos@, sautos),
        ensures
            match r.0 {
                Ok(x) => r.1@.ok && r.1@.flag && r_p(*final(self), toks, cfg, r.1@.st) && extends(st.nodes, r.1@.st.nodes) && r.1@.st.cur > st.cur
                    && r.1@.st.nodes.len() - st.nodes.len() <= 2 * (r.1@.st.cur - st.cur) && r.1@.st.depth == st.depth
                    && x == r.1@.node && x < r.1@.st.nodes.len(),
                Err(x) => r_perr(x, final(self).extension_uses@, r.1@),
            },
            forall|f: u64| #![trigger p_function_stmts(toks, cfg, st, sname, sparams, sautos, f)] pdone(p_function_stmts(toks, cfg, st, sname, sparams, sautos, f)) ==> p_function_stmts(toks, cfg, st, sname, sparams, sautos, f) == r.1@,
    {
        let outer_loop = self.loop_depth;
        let outer_function = self.in_function;
        self.loop_depth = 0;
        self.in_function = true;
        let ghost st1 = st_set_loop(st, 0u64, true);
        proof { assert(cur_tok(toks, st1) == cur_tok(toks, st)); }
        let (res, Ghost(l)) = self.parse_statement_list(Ghost(toks), Ghost(cfg), Ghost(st1));
        self.loop_depth = outer_loop;
        self.in_function = outer_function;
        let body = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_function_stmts(toks, cfg, st, sname, sparams, sautos, f)] pdone(p_function_stmts(toks, cfg, st, sname, sparams, sautos, f)) implies p_function_stmts(toks, cfg, st, sname, sparams, sautos, f) == l by {
                        assert(f > 0);
                        assert(pdone(p_statement_list(toks, cfg, st1, seq![], (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(l));
            },
        };
        let ghost s2 = st_set_loop(l.st, st.loop_depth, st.in_function);
        proof { assert(cur_tok(toks, s2) == cur_tok(toks, l.st)); }
        let ghost e8 = s_eat(toks, s2, Tok::Rbrace);
        match self.eat(TokenType::Rbrace, Ghost(toks), Ghost(cfg), Ghost(s2)) {
            Ok(()) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_function_stmts(toks, cfg, st, sname, sparams, sautos, f)] pdone(p_function_stmts(toks, cfg, st, sname, sparams, sautos, f)) implies p_function_stmts(toks, cfg, st, sname, sparams, sautos, f) == e8 by {
                        assert(f > 0);
                        assert(pdone(p_statement_list(toks, cfg, st1, seq![], (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(e8));
            },
        }
        let ghost nd = Node::Define(sname, sparams, sautos, l.list);
        let idx = self.add_stmt(PNode::Define(Box::new(FunctionDecl { name, params, autos, body })), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e8.st), Ghost(nd), Ghost(0u64));
        let ghost g = add_node(e8.st, nd, 0u64);
        proof {
            assert forall|f: u64| #![trigger p_function_stmts(toks, cfg, st, sname, sparams, sautos, f)] pdone(p_function_stmts(toks, cfg, st, sname, sparams, sautos, f)) implies p_function_stmts(toks, cfg, st, sname, sparams, sautos, f) == g by {
                assert(f > 0);
                assert(pdone(p_statement_list(toks, cfg, st1, seq![], (f - 1) as u64)));
            }
        }
        (Ok(idx), Ghost(g))
    }

}

} // verus!
