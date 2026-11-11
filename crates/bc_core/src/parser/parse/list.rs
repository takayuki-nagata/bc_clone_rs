// SPDX-License-Identifier: MIT

//! Sequences of statements and the input items of a unit (the specification's `p_program`,
//! `p_input_item`, `p_semicolon_list` and `p_statement_list`).

use super::*;

verus! {

/// `Parser::parse_input_item`: `flag` tells whether there is an item.
spec fn r_ires(r: Result<Option<usize>, BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(o) => p.ok && r_pc(q, toks, cfg, p.st) && extends(s0.nodes, p.st.nodes) && p.st.cur >= s0.cur
            && p.st.nodes.len() - s0.nodes.len() <= 2 * (p.st.cur - s0.cur) && p.st.depth == s0.depth
            && match o {
                Some(x) => p.flag && x == p.node && x < p.st.nodes.len(),
                None => !p.flag,
            },
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

spec fn semi_chain(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>) -> bool {
    forall|f: u64| #![trigger p_semicolon_list(toks, cfg, st, seq![], f)] pdone(p_semicolon_list(toks, cfg, st, seq![], f)) ==>
        exists|g: u64| #![trigger p_semicolon_list(toks, cfg, cur, acc, g)] p_semicolon_list(toks, cfg, cur, acc, g) == p_semicolon_list(toks, cfg, st, seq![], f)
}

proof fn lemma_semi_start(toks: Seq<SToken>, cfg: PCfg, st: PState)
    ensures
        semi_chain(toks, cfg, st, st, Seq::<usize>::empty()),
{
    let e = Seq::<usize>::empty();
    assert(seq![] == e);
    assert forall|f: u64| #![trigger p_semicolon_list(toks, cfg, st, seq![], f)] pdone(p_semicolon_list(toks, cfg, st, seq![], f)) implies
        exists|g: u64| #![trigger p_semicolon_list(toks, cfg, st, e, g)] p_semicolon_list(toks, cfg, st, e, g) == p_semicolon_list(toks, cfg, st, seq![], f) by {
        assert(p_semicolon_list(toks, cfg, st, e, f) == p_semicolon_list(toks, cfg, st, seq![], f));
    }
}

proof fn lemma_semi_ret(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>, r: PR)
    requires
        semi_chain(toks, cfg, st, cur, acc),
        forall|g: u64| #![trigger p_semicolon_list(toks, cfg, cur, acc, g)] g > 0 && pdone(p_semicolon_list(toks, cfg, cur, acc, g)) ==> p_semicolon_list(toks, cfg, cur, acc, g) == r,
    ensures
        forall|f: u64| #![trigger p_semicolon_list(toks, cfg, st, seq![], f)] pdone(p_semicolon_list(toks, cfg, st, seq![], f)) ==> p_semicolon_list(toks, cfg, st, seq![], f) == r,
{
    assert forall|f: u64| #![trigger p_semicolon_list(toks, cfg, st, seq![], f)] pdone(p_semicolon_list(toks, cfg, st, seq![], f)) implies p_semicolon_list(toks, cfg, st, seq![], f) == r by {
        let g = choose|g: u64| #![trigger p_semicolon_list(toks, cfg, cur, acc, g)] p_semicolon_list(toks, cfg, cur, acc, g) == p_semicolon_list(toks, cfg, st, seq![], f);
        assert(g > 0);
    }
}

proof fn lemma_semi_next(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>, cur2: PState, acc2: Seq<usize>)
    requires
        semi_chain(toks, cfg, st, cur, acc),
        forall|g: u64| #![trigger p_semicolon_list(toks, cfg, cur, acc, g)] g > 0 && pdone(p_semicolon_list(toks, cfg, cur, acc, g)) ==> p_semicolon_list(toks, cfg, cur, acc, g) == p_semicolon_list(toks, cfg, cur2, acc2, (g - 1) as u64),
    ensures
        semi_chain(toks, cfg, st, cur2, acc2),
{
    assert forall|f: u64| #![trigger p_semicolon_list(toks, cfg, st, seq![], f)] pdone(p_semicolon_list(toks, cfg, st, seq![], f)) implies
        exists|g: u64| #![trigger p_semicolon_list(toks, cfg, cur2, acc2, g)] p_semicolon_list(toks, cfg, cur2, acc2, g) == p_semicolon_list(toks, cfg, st, seq![], f) by {
        let g = choose|g: u64| #![trigger p_semicolon_list(toks, cfg, cur, acc, g)] p_semicolon_list(toks, cfg, cur, acc, g) == p_semicolon_list(toks, cfg, st, seq![], f);
        assert(g > 0);
        assert(p_semicolon_list(toks, cfg, cur2, acc2, (g - 1) as u64) == p_semicolon_list(toks, cfg, st, seq![], f));
    }
}

spec fn sl_chain(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>) -> bool {
    forall|f: u64| #![trigger p_statement_list(toks, cfg, st, seq![], f)] pdone(p_statement_list(toks, cfg, st, seq![], f)) ==>
        exists|g: u64| #![trigger p_statement_list(toks, cfg, cur, acc, g)] p_statement_list(toks, cfg, cur, acc, g) == p_statement_list(toks, cfg, st, seq![], f)
}

proof fn lemma_sl_start(toks: Seq<SToken>, cfg: PCfg, st: PState)
    ensures
        sl_chain(toks, cfg, st, st, Seq::<usize>::empty()),
{
    let e = Seq::<usize>::empty();
    assert(seq![] == e);
    assert forall|f: u64| #![trigger p_statement_list(toks, cfg, st, seq![], f)] pdone(p_statement_list(toks, cfg, st, seq![], f)) implies
        exists|g: u64| #![trigger p_statement_list(toks, cfg, st, e, g)] p_statement_list(toks, cfg, st, e, g) == p_statement_list(toks, cfg, st, seq![], f) by {
        assert(p_statement_list(toks, cfg, st, e, f) == p_statement_list(toks, cfg, st, seq![], f));
    }
}

proof fn lemma_sl_ret(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>, r: PR)
    requires
        sl_chain(toks, cfg, st, cur, acc),
        forall|g: u64| #![trigger p_statement_list(toks, cfg, cur, acc, g)] g > 0 && pdone(p_statement_list(toks, cfg, cur, acc, g)) ==> p_statement_list(toks, cfg, cur, acc, g) == r,
    ensures
        forall|f: u64| #![trigger p_statement_list(toks, cfg, st, seq![], f)] pdone(p_statement_list(toks, cfg, st, seq![], f)) ==> p_statement_list(toks, cfg, st, seq![], f) == r,
{
    assert forall|f: u64| #![trigger p_statement_list(toks, cfg, st, seq![], f)] pdone(p_statement_list(toks, cfg, st, seq![], f)) implies p_statement_list(toks, cfg, st, seq![], f) == r by {
        let g = choose|g: u64| #![trigger p_statement_list(toks, cfg, cur, acc, g)] p_statement_list(toks, cfg, cur, acc, g) == p_statement_list(toks, cfg, st, seq![], f);
        assert(g > 0);
    }
}

proof fn lemma_sl_next(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>, cur2: PState, acc2: Seq<usize>)
    requires
        sl_chain(toks, cfg, st, cur, acc),
        forall|g: u64| #![trigger p_statement_list(toks, cfg, cur, acc, g)] g > 0 && pdone(p_statement_list(toks, cfg, cur, acc, g)) ==> p_statement_list(toks, cfg, cur, acc, g) == p_statement_list(toks, cfg, cur2, acc2, (g - 1) as u64),
    ensures
        sl_chain(toks, cfg, st, cur2, acc2),
{
    assert forall|f: u64| #![trigger p_statement_list(toks, cfg, st, seq![], f)] pdone(p_statement_list(toks, cfg, st, seq![], f)) implies
        exists|g: u64| #![trigger p_statement_list(toks, cfg, cur2, acc2, g)] p_statement_list(toks, cfg, cur2, acc2, g) == p_statement_list(toks, cfg, st, seq![], f) by {
        let g = choose|g: u64| #![trigger p_statement_list(toks, cfg, cur, acc, g)] p_statement_list(toks, cfg, cur, acc, g) == p_statement_list(toks, cfg, st, seq![], f);
        assert(g > 0);
        assert(p_statement_list(toks, cfg, cur2, acc2, (g - 1) as u64) == p_statement_list(toks, cfg, st, seq![], f));
    }
}

/// Every finishing fuel of `p_statement_list` from `st` gives `r`.
spec fn sl_res(toks: Seq<SToken>, cfg: PCfg, st: PState, r: PR) -> bool {
    forall|f: u64| #![trigger p_statement_list(toks, cfg, st, seq![], f)] pdone(p_statement_list(toks, cfg, st, seq![], f)) ==> p_statement_list(toks, cfg, st, seq![], f) == r
}

/// `p_statement_list` at `cur` skips newlines with result `sk`, then stops at the end or `}`.
proof fn lemma_sl_skip(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>, sk: PR)
    requires
        sl_chain(toks, cfg, st, cur, acc),
        forall|f: u64| #![trigger p_skip_newlines(toks, cur, f)] pdone(p_skip_newlines(toks, cur, f)) ==> p_skip_newlines(toks, cur, f) == sk,
    ensures
        !sk.ok ==> sl_res(toks, cfg, st, sk),
        sk.ok && (cur_tok(toks, sk.st).kind is Eof || cur_tok(toks, sk.st).kind is Rbrace) ==> sl_res(toks, cfg, st, pr_list(sk.st, acc)),
{
    if !sk.ok {
        assert forall|k: u64| #![trigger p_statement_list(toks, cfg, cur, acc, k)] k > 0 && pdone(p_statement_list(toks, cfg, cur, acc, k)) implies p_statement_list(toks, cfg, cur, acc, k) == sk by {
            assert(pdone(p_skip_newlines(toks, cur, (k - 1) as u64)));
        }
        lemma_sl_ret(toks, cfg, st, cur, acc, sk);
    } else if cur_tok(toks, sk.st).kind is Eof || cur_tok(toks, sk.st).kind is Rbrace {
        let g = pr_list(sk.st, acc);
        assert forall|k: u64| #![trigger p_statement_list(toks, cfg, cur, acc, k)] k > 0 && pdone(p_statement_list(toks, cfg, cur, acc, k)) implies p_statement_list(toks, cfg, cur, acc, k) == g by {
            assert(pdone(p_skip_newlines(toks, cur, (k - 1) as u64)));
        }
        lemma_sl_ret(toks, cfg, st, cur, acc, g);
    }
}

/// `p_statement_list` at `cur`, after skipping newlines with result `sk`, parses a statement with
/// result `i`, then eats a `;` or a newline after it, stops, or reports a syntax error.
proof fn lemma_sl_stmt(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>, sk: PR, i: PR)
    requires
        sl_chain(toks, cfg, st, cur, acc),
        forall|f: u64| #![trigger p_skip_newlines(toks, cur, f)] pdone(p_skip_newlines(toks, cur, f)) ==> p_skip_newlines(toks, cur, f) == sk,
        sk.ok,
        !(cur_tok(toks, sk.st).kind is Eof || cur_tok(toks, sk.st).kind is Rbrace),
        forall|f: u64| #![trigger p_statement(toks, cfg, sk.st, f)] pdone(p_statement(toks, cfg, sk.st, f)) ==> p_statement(toks, cfg, sk.st, f) == i,
    ensures
        !i.ok ==> sl_res(toks, cfg, st, i),
        i.ok && (cur_tok(toks, i.st).kind is Rbrace || cur_tok(toks, i.st).kind is Eof) ==> sl_res(toks, cfg, st, pr_list(i.st, acc.push(i.node))),
        i.ok && !(cur_tok(toks, i.st).kind is Rbrace || cur_tok(toks, i.st).kind is Eof || cur_tok(toks, i.st).kind is Semicolon || cur_tok(toks, i.st).kind is Newline)
            ==> sl_res(toks, cfg, st, syntax_at(i.st, cur_tok(toks, i.st).line)),
        i.ok && (cur_tok(toks, i.st).kind is Semicolon || cur_tok(toks, i.st).kind is Newline) ==> ({
            let e = s_eat(toks, i.st, cur_tok(toks, i.st).kind);
            &&& e.ok ==> sl_chain(toks, cfg, st, e.st, acc.push(i.node))
            &&& !e.ok ==> sl_res(toks, cfg, st, e)
        }),
{
    let a1 = acc.push(i.node);
    let nk = cur_tok(toks, i.st).kind;
    if !i.ok {
        assert forall|k: u64| #![trigger p_statement_list(toks, cfg, cur, acc, k)] k > 0 && pdone(p_statement_list(toks, cfg, cur, acc, k)) implies p_statement_list(toks, cfg, cur, acc, k) == i by {
            assert(pdone(p_skip_newlines(toks, cur, (k - 1) as u64)));
            assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
        }
        lemma_sl_ret(toks, cfg, st, cur, acc, i);
    } else if nk is Rbrace || nk is Eof {
        let g = pr_list(i.st, a1);
        assert forall|k: u64| #![trigger p_statement_list(toks, cfg, cur, acc, k)] k > 0 && pdone(p_statement_list(toks, cfg, cur, acc, k)) implies p_statement_list(toks, cfg, cur, acc, k) == g by {
            assert(pdone(p_skip_newlines(toks, cur, (k - 1) as u64)));
            assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
        }
        lemma_sl_ret(toks, cfg, st, cur, acc, g);
    } else if !(nk is Semicolon || nk is Newline) {
        let g = syntax_at(i.st, cur_tok(toks, i.st).line);
        assert forall|k: u64| #![trigger p_statement_list(toks, cfg, cur, acc, k)] k > 0 && pdone(p_statement_list(toks, cfg, cur, acc, k)) implies p_statement_list(toks, cfg, cur, acc, k) == g by {
            assert(pdone(p_skip_newlines(toks, cur, (k - 1) as u64)));
            assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
        }
        lemma_sl_ret(toks, cfg, st, cur, acc, g);
    } else {
        let e = s_eat(toks, i.st, nk);
        if e.ok {
            assert forall|k: u64| #![trigger p_statement_list(toks, cfg, cur, acc, k)] k > 0 && pdone(p_statement_list(toks, cfg, cur, acc, k)) implies p_statement_list(toks, cfg, cur, acc, k) == p_statement_list(toks, cfg, e.st, a1, (k - 1) as u64) by {
                assert(pdone(p_skip_newlines(toks, cur, (k - 1) as u64)));
                assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
            }
            lemma_sl_next(toks, cfg, st, cur, acc, e.st, a1);
        } else {
            assert forall|k: u64| #![trigger p_statement_list(toks, cfg, cur, acc, k)] k > 0 && pdone(p_statement_list(toks, cfg, cur, acc, k)) implies p_statement_list(toks, cfg, cur, acc, k) == e by {
                assert(pdone(p_skip_newlines(toks, cur, (k - 1) as u64)));
                assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
            }
            lemma_sl_ret(toks, cfg, st, cur, acc, e);
        }
    }
}

spec fn prog_chain(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>) -> bool {
    forall|f: u64| #![trigger p_program(toks, cfg, st, seq![], f)] pdone(p_program(toks, cfg, st, seq![], f)) ==>
        exists|g: u64| #![trigger p_program(toks, cfg, cur, acc, g)] p_program(toks, cfg, cur, acc, g) == p_program(toks, cfg, st, seq![], f)
}

proof fn lemma_prog_start(toks: Seq<SToken>, cfg: PCfg, st: PState)
    ensures
        prog_chain(toks, cfg, st, st, Seq::<usize>::empty()),
{
    let e = Seq::<usize>::empty();
    assert(seq![] == e);
    assert forall|f: u64| #![trigger p_program(toks, cfg, st, seq![], f)] pdone(p_program(toks, cfg, st, seq![], f)) implies
        exists|g: u64| #![trigger p_program(toks, cfg, st, e, g)] p_program(toks, cfg, st, e, g) == p_program(toks, cfg, st, seq![], f) by {
        assert(p_program(toks, cfg, st, e, f) == p_program(toks, cfg, st, seq![], f));
    }
}

proof fn lemma_prog_ret(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>, r: PR)
    requires
        prog_chain(toks, cfg, st, cur, acc),
        forall|g: u64| #![trigger p_program(toks, cfg, cur, acc, g)] g > 0 && pdone(p_program(toks, cfg, cur, acc, g)) ==> p_program(toks, cfg, cur, acc, g) == r,
    ensures
        forall|f: u64| #![trigger p_program(toks, cfg, st, seq![], f)] pdone(p_program(toks, cfg, st, seq![], f)) ==> p_program(toks, cfg, st, seq![], f) == r,
{
    assert forall|f: u64| #![trigger p_program(toks, cfg, st, seq![], f)] pdone(p_program(toks, cfg, st, seq![], f)) implies p_program(toks, cfg, st, seq![], f) == r by {
        let g = choose|g: u64| #![trigger p_program(toks, cfg, cur, acc, g)] p_program(toks, cfg, cur, acc, g) == p_program(toks, cfg, st, seq![], f);
        assert(g > 0);
    }
}

proof fn lemma_prog_next(toks: Seq<SToken>, cfg: PCfg, st: PState, cur: PState, acc: Seq<usize>, cur2: PState, acc2: Seq<usize>)
    requires
        prog_chain(toks, cfg, st, cur, acc),
        forall|g: u64| #![trigger p_program(toks, cfg, cur, acc, g)] g > 0 && pdone(p_program(toks, cfg, cur, acc, g)) ==> p_program(toks, cfg, cur, acc, g) == p_program(toks, cfg, cur2, acc2, (g - 1) as u64),
    ensures
        prog_chain(toks, cfg, st, cur2, acc2),
{
    assert forall|f: u64| #![trigger p_program(toks, cfg, st, seq![], f)] pdone(p_program(toks, cfg, st, seq![], f)) implies
        exists|g: u64| #![trigger p_program(toks, cfg, cur2, acc2, g)] p_program(toks, cfg, cur2, acc2, g) == p_program(toks, cfg, st, seq![], f) by {
        let g = choose|g: u64| #![trigger p_program(toks, cfg, cur, acc, g)] p_program(toks, cfg, cur, acc, g) == p_program(toks, cfg, st, seq![], f);
        assert(g > 0);
        assert(p_program(toks, cfg, cur2, acc2, (g - 1) as u64) == p_program(toks, cfg, st, seq![], f));
    }
}

impl Parser {
    /// Parses the program fully, returning Err on lexical/syntax error or `"quit"`.
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn parse_program_ref(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Vec<usize>, BcError>, Ghost<GResult>))
        requires
            r_pc(*old(self), toks, cfg, st),
        ensures
            match r.0 {
                Ok(l) => r.1@.ok && l@ == r.1@.list && r_nodes(final(self).nodes@, r.1@.st.nodes) && r_ext(final(self).extension_uses@, r.1@.st.ext),
                Err(x) => r_perr(x, final(self).extension_uses@, r.1@),
            },
            forall|f: u64| #![trigger p_program(toks, cfg, st, seq![], f)] pdone(p_program(toks, cfg, st, seq![], f)) ==> p_program(toks, cfg, st, seq![], f) == r.1@,
    {
        let mut stmts: Vec<usize> = Vec::new();
        let ghost mut cur = st;
        let ghost mut acc = Seq::<usize>::empty();
        proof { lemma_prog_start(toks, cfg, st); }
        loop
            invariant
                r_pc(*self, toks, cfg, cur),
                extends(st.nodes, cur.nodes),
                st.nodes.len() <= 2 * st.cur,
                cur.nodes.len() <= 2 * cur.cur,
                stmts@ == acc,
                prog_chain(toks, cfg, st, cur, acc),
        {
            let ghost (c, a0) = (cur, acc);
            if matches!(self.current_token.token_type, TokenType::Eof) {
                let ghost g = pr_list(c, a0);
                proof {
                    assert forall|k: u64| #![trigger p_program(toks, cfg, c, a0, k)] k > 0 && pdone(p_program(toks, cfg, c, a0, k)) implies p_program(toks, cfg, c, a0, k) == g by {
                    }
                    lemma_prog_ret(toks, cfg, st, c, a0, g);
                }
                return (Ok(stmts), Ghost(g));
            }
            proof {
                if c.cur == toks.len() { assert(cur_tok(toks, c) == toks.last()); }
            }
            let ghost old_stmts = stmts@;
            let (res, Ghost(i)) = self.parse_input_item(Ghost(toks), Ghost(cfg), Ghost(c));
            let item = match res {
                Ok(v) => v,
                Err(x) => {
                    proof {
                        assert forall|k: u64| #![trigger p_program(toks, cfg, c, a0, k)] k > 0 && pdone(p_program(toks, cfg, c, a0, k)) implies p_program(toks, cfg, c, a0, k) == i by {
                            assert(pdone(p_input_item(toks, cfg, c, (k - 1) as u64)));
                        }
                        lemma_prog_ret(toks, cfg, st, c, a0, i);
                    }
                    return (Err(x), Ghost(i));
                },
            };
            match item {
                Some(x) => {
                    let ghost a1 = a0.push(i.node);
                    stmts.push(x);
                    proof { assert(stmts@ =~= old_stmts.push(x)); }
                    proof {
                        assert forall|k: u64| #![trigger p_program(toks, cfg, c, a0, k)] k > 0 && pdone(p_program(toks, cfg, c, a0, k)) implies p_program(toks, cfg, c, a0, k) == p_program(toks, cfg, i.st, a1, (k - 1) as u64) by {
                            assert(pdone(p_input_item(toks, cfg, c, (k - 1) as u64)));
                        }
                        lemma_prog_next(toks, cfg, st, c, a0, i.st, a1);
                        cur = i.st;
                        acc = a1;
                    }
                },
                None => {
                    proof {
                        assert forall|k: u64| #![trigger p_program(toks, cfg, c, a0, k)] k > 0 && pdone(p_program(toks, cfg, c, a0, k)) implies p_program(toks, cfg, c, a0, k) == p_program(toks, cfg, i.st, a0, (k - 1) as u64) by {
                            assert(pdone(p_input_item(toks, cfg, c, (k - 1) as u64)));
                        }
                        lemma_prog_next(toks, cfg, st, c, a0, i.st, a0);
                        cur = i.st;
                        acc = a0;
                    }
                },
            }
        }
    }

    /// Parses a single top-level item (statement block or function definition).
    #[verifier::rlimit(60)]
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_input_item(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Option<usize>, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_ires(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_input_item(toks, cfg, st, f)] pdone(p_input_item(toks, cfg, st, f)) ==> p_input_item(toks, cfg, st, f) == r.1@,
    {
        if matches!(self.current_token.token_type, TokenType::Define) {
            let (res, Ghost(d)) = self.parse_function(Ghost(toks), Ghost(cfg), Ghost(st));
        proof {
            assert forall|f: u64| #![trigger p_input_item(toks, cfg, st, f)] pdone(p_input_item(toks, cfg, st, f)) implies p_input_item(toks, cfg, st, f) == d by {
                assert(f > 0);
                assert(pdone(p_function(toks, cfg, st, (f - 1) as u64)));
            }
        }
            return match res {
                Ok(x) => (Ok(Some(x)), Ghost(d)),
                Err(x) => (Err(x), Ghost(d)),
            };
        }
        let (res, Ghost(l)) = self.parse_semicolon_list(Ghost(toks), Ghost(cfg), Ghost(st));
        let lst = match res {
            Ok(v) => v,
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_input_item(toks, cfg, st, f)] pdone(p_input_item(toks, cfg, st, f)) implies p_input_item(toks, cfg, st, f) == l by {
                        assert(f > 0);
                        assert(pdone(p_semicolon_list(toks, cfg, st, seq![], (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(l));
            },
        };
        let ghost e = if cur_tok(toks, l.st).kind is Newline { s_eat(toks, l.st, Tok::Newline) } else { s_eat(toks, l.st, Tok::Eof) };
        let eaten = if matches!(self.current_token.token_type, TokenType::Newline) {
            self.eat(TokenType::Newline, Ghost(toks), Ghost(cfg), Ghost(l.st))
        } else {
            self.eat_eof(Ghost(toks), Ghost(cfg), Ghost(l.st))
        };
        match eaten {
            Ok(()) => {},
            Err(x) => {
                proof {
                    assert forall|f: u64| #![trigger p_input_item(toks, cfg, st, f)] pdone(p_input_item(toks, cfg, st, f)) implies p_input_item(toks, cfg, st, f) == e by {
                        assert(f > 0);
                        assert(pdone(p_semicolon_list(toks, cfg, st, seq![], (f - 1) as u64)));
                    }
                }
                return (Err(x), Ghost(e));
            },
        }
        if lst.len() == 0 {
            let ghost g = pr_ok(e.st);
            proof {
                assert forall|f: u64| #![trigger p_input_item(toks, cfg, st, f)] pdone(p_input_item(toks, cfg, st, f)) implies p_input_item(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_semicolon_list(toks, cfg, st, seq![], (f - 1) as u64)));
                }
            }
            (Ok(None), Ghost(g))
        } else {
            let idx = self.add_stmt(PNode::Block(lst), Ghost(toks), Ghost(cfg), Ghost(st), Ghost(e.st), Ghost(Node::Block(l.list)), Ghost(0u64));
            let ghost g = add_node(e.st, Node::Block(l.list), 0u64);
            proof {
                assert(e.st.cur == l.st.cur + 1);
                assert(lst@.len() == l.list.len());
                assert forall|f: u64| #![trigger p_input_item(toks, cfg, st, f)] pdone(p_input_item(toks, cfg, st, f)) implies p_input_item(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_semicolon_list(toks, cfg, st, seq![], (f - 1) as u64)));
                }
            }
            (Ok(Some(idx)), Ghost(g))
        }
    }

    /// Parses a list of statements separated by semicolons.
    #[verifier::rlimit(20)]
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_semicolon_list(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Vec<usize>, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_lres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_semicolon_list(toks, cfg, st, seq![], f)] pdone(p_semicolon_list(toks, cfg, st, seq![], f)) ==> p_semicolon_list(toks, cfg, st, seq![], f) == r.1@,
    {
        let mut stmts: Vec<usize> = Vec::new();
        let ghost mut cur = st;
        let ghost mut acc = Seq::<usize>::empty();
        proof { lemma_semi_start(toks, cfg, st); }
        loop
            invariant
                r_p(*self, toks, cfg, cur),
                extends(st.nodes, cur.nodes),
                cur.cur >= st.cur,
                cur.nodes.len() - st.nodes.len() <= 2 * (cur.cur - st.cur),
                cur.depth == st.depth,
                st.nodes.len() <= 2 * st.cur,
                stmts@ == acc,
                semi_chain(toks, cfg, st, cur, acc),
        {
            let ghost (c, a0) = (cur, acc);
            let k = self.current_token.token_type;
            if matches!(k, TokenType::Newline) || matches!(k, TokenType::Eof) || matches!(k, TokenType::Rbrace) {
                let ghost g = pr_list(c, a0);
                proof {
                    assert forall|k: u64| #![trigger p_semicolon_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_semicolon_list(toks, cfg, c, a0, k)) implies p_semicolon_list(toks, cfg, c, a0, k) == g by {
                    }
                    lemma_semi_ret(toks, cfg, st, c, a0, g);
                }
                return (Ok(stmts), Ghost(g));
            }
            if matches!(k, TokenType::Semicolon) {
                let ghost e = s_eat(toks, c, Tok::Semicolon);
                match self.eat(TokenType::Semicolon, Ghost(toks), Ghost(cfg), Ghost(c)) {
                    Ok(()) => {
                        proof {
                            assert forall|k: u64| #![trigger p_semicolon_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_semicolon_list(toks, cfg, c, a0, k)) implies p_semicolon_list(toks, cfg, c, a0, k) == p_semicolon_list(toks, cfg, e.st, a0, (k - 1) as u64) by {
                            }
                            lemma_semi_next(toks, cfg, st, c, a0, e.st, a0);
                            cur = e.st;
                            acc = a0;
                        }
                    },
                    Err(x) => {
                        proof {
                            assert forall|k: u64| #![trigger p_semicolon_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_semicolon_list(toks, cfg, c, a0, k)) implies p_semicolon_list(toks, cfg, c, a0, k) == e by {
                            }
                            lemma_semi_ret(toks, cfg, st, c, a0, e);
                        }
                        return (Err(x), Ghost(e));
                    },
                }
            } else {
                let ghost old_stmts = stmts@;
                let (res, Ghost(i)) = self.parse_statement(Ghost(toks), Ghost(cfg), Ghost(c));
                let x = match res {
                    Ok(v) => v,
                    Err(y) => {
                        proof {
                            assert forall|k: u64| #![trigger p_semicolon_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_semicolon_list(toks, cfg, c, a0, k)) implies p_semicolon_list(toks, cfg, c, a0, k) == i by {
                                assert(pdone(p_statement(toks, cfg, c, (k - 1) as u64)));
                            }
                            lemma_semi_ret(toks, cfg, st, c, a0, i);
                        }
                        return (Err(y), Ghost(i));
                    },
                };
                let ghost a1 = a0.push(i.node);
                stmts.push(x);
                proof { assert(stmts@ =~= old_stmts.push(x)); }
                if !matches!(self.current_token.token_type, TokenType::Semicolon) {
                    let ghost g = pr_list(i.st, a1);
                    proof {
                        assert forall|k: u64| #![trigger p_semicolon_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_semicolon_list(toks, cfg, c, a0, k)) implies p_semicolon_list(toks, cfg, c, a0, k) == g by {
                            assert(pdone(p_statement(toks, cfg, c, (k - 1) as u64)));
                        }
                        lemma_semi_ret(toks, cfg, st, c, a0, g);
                    }
                    return (Ok(stmts), Ghost(g));
                }
                let ghost e = s_eat(toks, i.st, Tok::Semicolon);
                match self.eat(TokenType::Semicolon, Ghost(toks), Ghost(cfg), Ghost(i.st)) {
                    Ok(()) => {
                        proof {
                            assert forall|k: u64| #![trigger p_semicolon_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_semicolon_list(toks, cfg, c, a0, k)) implies p_semicolon_list(toks, cfg, c, a0, k) == p_semicolon_list(toks, cfg, e.st, a1, (k - 1) as u64) by {
                                assert(pdone(p_statement(toks, cfg, c, (k - 1) as u64)));
                            }
                            lemma_semi_next(toks, cfg, st, c, a0, e.st, a1);
                            cur = e.st;
                            acc = a1;
                        }
                    },
                    Err(y) => {
                        proof {
                            assert forall|k: u64| #![trigger p_semicolon_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_semicolon_list(toks, cfg, c, a0, k)) implies p_semicolon_list(toks, cfg, c, a0, k) == e by {
                                assert(pdone(p_statement(toks, cfg, c, (k - 1) as u64)));
                            }
                            lemma_semi_ret(toks, cfg, st, c, a0, e);
                        }
                        return (Err(y), Ghost(e));
                    },
                }
            }
        }
    }

    /// Parses a list of statements within a block (with newline and semicolon separations).
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn parse_statement_list(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Vec<usize>, BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_lres(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_statement_list(toks, cfg, st, seq![], f)] pdone(p_statement_list(toks, cfg, st, seq![], f)) ==> p_statement_list(toks, cfg, st, seq![], f) == r.1@,
    {
        let mut stmts: Vec<usize> = Vec::new();
        let ghost mut cur = st;
        let ghost mut acc = Seq::<usize>::empty();
        proof { lemma_sl_start(toks, cfg, st); }
        loop
            invariant
                r_p(*self, toks, cfg, cur),
                extends(st.nodes, cur.nodes),
                cur.cur >= st.cur,
                cur.nodes.len() - st.nodes.len() <= 2 * (cur.cur - st.cur),
                cur.depth == st.depth,
                st.nodes.len() <= 2 * st.cur,
                stmts@ == acc,
                sl_chain(toks, cfg, st, cur, acc),
        {
            let ghost (c, a0) = (cur, acc);
            let (res, Ghost(sk)) = self.skip_newlines(Ghost(toks), Ghost(cfg), Ghost(c));
            proof { lemma_sl_skip(toks, cfg, st, c, a0, sk); }
            match res {
                Ok(()) => {},
                Err(y) => return (Err(y), Ghost(sk)),
            }
            let k = self.current_token.token_type;
            if matches!(k, TokenType::Eof) || matches!(k, TokenType::Rbrace) {
                let ghost g = pr_list(sk.st, a0);
                return (Ok(stmts), Ghost(g));
            }
            let ghost old_stmts = stmts@;
            let (res2, Ghost(i)) = self.parse_statement(Ghost(toks), Ghost(cfg), Ghost(sk.st));
            proof { lemma_sl_stmt(toks, cfg, st, c, a0, sk, i); }
            let x = match res2 {
                Ok(v) => v,
                Err(y) => return (Err(y), Ghost(i)),
            };
            let ghost a1 = a0.push(i.node);
            stmts.push(x);
            proof { assert(stmts@ =~= old_stmts.push(x)); }
            let nk = self.current_token.token_type;
            let ghost line = cur_tok(toks, i.st).line;
            if matches!(nk, TokenType::Rbrace) || matches!(nk, TokenType::Eof) {
                let ghost g = pr_list(i.st, a1);
                return (Ok(stmts), Ghost(g));
            }
            if !matches!(nk, TokenType::Semicolon) && !matches!(nk, TokenType::Newline) {
                let ghost g = syntax_at(i.st, line);
                return (Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() }), Ghost(g));
            }
            let ghost e = s_eat(toks, i.st, tok_of(nk));
            match self.eat(nk, Ghost(toks), Ghost(cfg), Ghost(i.st)) {
                Ok(()) => {
                    proof {
                        cur = e.st;
                        acc = a1;
                    }
                },
                Err(y) => return (Err(y), Ghost(e)),
            }
        }
    }

}

} // verus!
