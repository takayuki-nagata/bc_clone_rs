// SPDX-License-Identifier: MIT

//! The parser: recursive descent, with Pratt precedence climbing for expressions.
//!
//! This module holds the parser's state, the relations between it and the specification's
//! (`bc_spec::parser`), the token helpers and the entry point `parse_unit_ref`. The grammar is in
//! the submodules: expressions (`expr`), statements (`stmt`), sequences of statements and the
//! input items (`list`), and function definitions (`func`).

#[cfg(verus_keep_ghost)]
use super::all_ascii;
use super::ascii_string;
use super::lexer::syntax_error_text;
#[cfg(verus_keep_ghost)]
use super::lexer::{r_lex_err, r_next, tok_of, tok_view};
use super::{
    Arg as PArg, AssignOp, BinOp, Code, ExtensionPolicy, FunctionDecl, Lexer, Node as PNode, Param,
    Register, RelOp, Token, TokenType,
};
#[cfg(verus_keep_ghost)]
use crate::driver::{r_ext, r_parsed};
use crate::error::BcError;
#[cfg(verus_keep_ghost)]
use crate::refine::{
    assign_code as r_assign_code, bin_code, extends, lemma_r_args_push, r_arg, r_args, r_node,
    r_nodes, r_param, r_params, rel_code as r_rel_code, text_view,
};
use crate::verified_kernels::{
    TOK_ASSIGN_OP, TOK_EXP_OP, TOK_MUL_OP, TOK_PLUS_MINUS, verified_nesting_within_limit,
    verified_pratt_infix_info,
};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use bc_spec::lexer::{Tok, Token as SToken, normal, syntax_error_msg, tokenize};
#[cfg(verus_keep_ghost)]
use bc_spec::lexer_lemmas::{ascii_bytes, lemma_lex_len, lemma_lex_shape, tok_good};
#[cfg(verus_keep_ghost)]
use bc_spec::parser::Param as SParam;
#[cfg(verus_keep_ghost)]
use bc_spec::parser::{
    Arg, ExtUse, Node, PCfg, PErr, PR, PState, add_node, assign_code as s_assign_code, binop_code,
    break_msg, comparison_msg, cur_tok, eat as s_eat, eat_name as s_eat_name, eol_msg,
    extension as s_extension, inc, infix_info as s_infix_info, lex_err, max_u64, misplaced,
    multi_letter_prefix, no_err, note_name as s_note_name, p_arg_list, p_block, p_break_stmt,
    p_builtin, p_call, p_cond, p_define_list, p_expr_loop, p_expr_prec, p_expr_stmt, p_for,
    p_function, p_function_body, p_function_stmts, p_if, p_input_item, p_loop_body, p_named,
    p_named_tail, p_opt_auto, p_parenthesized, p_prefix, p_primary, p_program, p_relational,
    p_return, p_return_stmt, p_semicolon_list, p_skip_newlines, p_statement, p_statement_inner,
    p_statement_list, p_string_stmt, p_subscript, p_while, parse_unit, peek_kind, pr_args, pr_err,
    pr_list, pr_node, pr_ok, pr_params, rel_code as s_rel_code, return_msg, return_paren_msg,
    st_set_depth, st_set_loop, syntax_at, token_at, too_deep, within,
};
#[cfg(not(verus_keep_ghost))]
use verus_builtin::Ghost;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

mod expr;
mod func;
mod list;
mod stmt;

/// Diagnostic for input nested deeper than the limit (`docs/COMPATIBILITY.md` §3.2).
pub const NESTING_TOO_DEEP: &str = "nesting too deep";

/// Default nesting limit for parsing and evaluation (`docs/COMPATIBILITY.md` §2). One level
/// takes at most about 1.9 KB of stack in an x86-64 release build and 800 bytes on RV32, so the
/// default suits a stack of 256 KiB or more. Front ends set `Evaluator::max_depth` for their own
/// stack.
pub const DEFAULT_MAX_DEPTH: usize = 128;

verus! {

/// Recursive descent parser with operator precedence support for bc.
pub struct Parser {
    lexer: Lexer,
    current_token: Token,
    /// Number of enclosing `for`/`while` bodies, for rejecting a stray `break`.
    loop_depth: usize,
    /// Whether a function body is being parsed, for rejecting a stray `return`.
    in_function: bool,
    extension_policy: ExtensionPolicy,
    /// Uses of extensions as `(line, description)`, recorded unless the policy is `Allow`.
    extension_uses: Vec<(usize, String)>,
    /// Number of enclosing statements and expression levels being parsed.
    depth: usize,
    /// Line of the last consumed token.
    last_line: usize,
    /// Largest nesting depth of the syntax tree (`docs/COMPATIBILITY.md` §2).
    max_depth: usize,
    /// The arena of the nodes built so far.
    nodes: Vec<PNode>,
}

broadcast use vstd::std_specs::vec::group_vec_axioms;

#[cfg(verus_keep_ghost)]
type GNode = Node;
#[cfg(not(verus_keep_ghost))]
type GNode = ();
#[cfg(verus_keep_ghost)]
type GBytes = Seq<u8>;
#[cfg(not(verus_keep_ghost))]
type GBytes = ();
#[cfg(verus_keep_ghost)]
type GToks = Seq<SToken>;
#[cfg(not(verus_keep_ghost))]
type GToks = ();
#[cfg(verus_keep_ghost)]
type GCfg = PCfg;
#[cfg(not(verus_keep_ghost))]
type GCfg = ();
#[cfg(verus_keep_ghost)]
type GState = PState;
#[cfg(not(verus_keep_ghost))]
type GState = ();
#[cfg(verus_keep_ghost)]
type GParams = Seq<SParam>;
#[cfg(not(verus_keep_ghost))]
type GParams = ();
#[cfg(verus_keep_ghost)]
type GResult = PR;
#[cfg(not(verus_keep_ghost))]
type GResult = ();

/// Whether two kinds are equal: `tok_of` is injective, so this is the specification's comparison.
fn kind_eq(a: TokenType, b: TokenType) -> (r: bool)
    ensures
        r == (tok_of(a) == tok_of(b)),
{
    matches!(
        (a, b),
        (TokenType::Eof, TokenType::Eof) | (TokenType::Newline, TokenType::Newline) | (TokenType::Semicolon, TokenType::Semicolon)
        | (TokenType::Comma, TokenType::Comma) | (TokenType::Lparen, TokenType::Lparen) | (TokenType::Rparen, TokenType::Rparen)
        | (TokenType::Lbracket, TokenType::Lbracket) | (TokenType::Rbracket, TokenType::Rbracket) | (TokenType::Lbrace, TokenType::Lbrace)
        | (TokenType::Rbrace, TokenType::Rbrace) | (TokenType::Plus, TokenType::Plus) | (TokenType::Minus, TokenType::Minus)
        | (TokenType::Exp, TokenType::Exp) | (TokenType::MulOp, TokenType::MulOp) | (TokenType::RelOp, TokenType::RelOp)
        | (TokenType::IncrDecr, TokenType::IncrDecr) | (TokenType::AssignOp, TokenType::AssignOp) | (TokenType::Letter, TokenType::Letter)
        | (TokenType::Number, TokenType::Number) | (TokenType::String, TokenType::String) | (TokenType::Auto, TokenType::Auto)
        | (TokenType::Break, TokenType::Break) | (TokenType::Define, TokenType::Define) | (TokenType::Ibase, TokenType::Ibase)
        | (TokenType::If, TokenType::If) | (TokenType::For, TokenType::For) | (TokenType::Length, TokenType::Length)
        | (TokenType::Obase, TokenType::Obase) | (TokenType::Quit, TokenType::Quit) | (TokenType::Return, TokenType::Return)
        | (TokenType::Scale, TokenType::Scale) | (TokenType::Sqrt, TokenType::Sqrt) | (TokenType::While, TokenType::While)
    )
}

/// A token sequence as `tokenize` produces it.
pub open spec fn toks_wf(toks: Seq<SToken>) -> bool {
    &&& 0 < toks.len() < 0x7000_0000
    &&& toks.last().kind is Eof || toks.last().kind is LexError
    &&& forall|i: int| 0 <= i < toks.len() - 1 ==> !(#[trigger] toks[i].kind is Eof) && !(toks[i].kind is LexError)
    &&& forall|i: int| 0 <= i < toks.len() && (#[trigger] toks[i].kind is Letter || toks[i].kind is Number) ==> all_ascii(toks[i].text)
}

/// The tokens that the lexer has not returned when the next token is number `k`.
pub open spec fn rest_of(toks: Seq<SToken>, k: int) -> Seq<SToken> {
    if k < toks.len() { toks.skip(k) } else { seq![toks.last()] }
}

/// The parsing function finished: it succeeded, or it failed other than by running out of fuel.
pub open spec fn pdone(p: PR) -> bool {
    p.ok || !p.err.out_of_fuel
}

/// The parser corresponds to the specification's state `st` on the tokens `toks`.
spec fn r_p(p: Parser, toks: Seq<SToken>, cfg: PCfg, st: PState) -> bool {
    &&& r_pc(p, toks, cfg, st)
    &&& st.cur < toks.len()
}

/// [`r_p`], possibly after the final `Eof` was consumed.
spec fn r_pc(p: Parser, toks: Seq<SToken>, cfg: PCfg, st: PState) -> bool {
    &&& toks_wf(toks)
    &&& r_nodes(p.nodes@, st.nodes)
    &&& st.cur <= toks.len()
    &&& st.nodes.len() <= 2 * st.cur
    &&& p.max_depth < usize::MAX - 2
    &&& p.lexer.inv()
    &&& p.lexer.text_len() <= 1_000_000_000
    &&& tok_view(p.current_token) == cur_tok(toks, st)
    &&& !(cur_tok(toks, st).kind is LexError)
    &&& p.lexer.rest() == rest_of(toks, st.cur + 1)
    &&& (p.extension_policy != ExtensionPolicy::Allow) == cfg.record_extensions
    &&& p.max_depth as u64 == cfg.max_depth
    &&& p.depth as u64 == st.depth
    &&& p.last_line as u64 == st.last_line
    &&& (p.loop_depth == 0) == (st.loop_depth == 0)
    &&& p.in_function == st.in_function
    &&& r_ext(p.extension_uses@, st.ext)
}

/// A syntax or lexical error of the specification's result.
spec fn r_perr(e: BcError, ext: Seq<(usize, String)>, p: PR) -> bool {
    &&& !p.ok
    &&& r_ext(ext, p.st.ext)
    &&& match e {
        BcError::Quit => p.err.quit,
        BcError::Syntax { line, message } => !p.err.quit && !p.err.out_of_fuel && p.err.line == line as u64
            && p.err.msg == text_view(message),
        BcError::Runtime { .. } => false,
    }
}

spec fn r_unit(r: Result<(), BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(()) => p.ok && r_p(q, toks, cfg, p.st) && p.st.nodes == s0.nodes && p.st.cur >= s0.cur && p.st.depth == s0.depth,
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

proof fn lemma_rest_step(toks: Seq<SToken>, k: int)
    requires
        toks_wf(toks),
        0 <= k <= toks.len() + 1,
    ensures
        rest_of(toks, k).len() > 0,
        rest_of(toks, k)[0] == token_at(toks, k as usize),
        !(rest_of(toks, k)[0].kind is Eof) && !(rest_of(toks, k)[0].kind is LexError) ==> rest_of(toks, k + 1) == rest_of(toks, k).drop_first(),
        rest_of(toks, k)[0].kind is Eof ==> rest_of(toks, k) == seq![rest_of(toks, k)[0]] && rest_of(toks, k + 1) == rest_of(toks, k),
        rest_of(toks, k).len() == 1 ==> rest_of(toks, k)[0] == toks.last(),
{
    if k < toks.len() {
        assert(toks.skip(k)[0] == toks[k]);
        if k + 1 < toks.len() {
            assert(toks.skip(k).drop_first() =~= toks.skip(k + 1));
            assert(!(toks[k].kind is Eof));
        } else {
            assert(toks.skip(k) =~= seq![toks.last()]);
        }
    }
}

impl Parser {
    /// Consumes a token of the expected type, otherwise raises error.
    fn eat(&mut self, k: TokenType, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: Result<(), BcError>)
        requires
            r_p(*old(self), toks, cfg, st),
            !(tok_of(k) is Eof),
        ensures
            r_unit(r, *final(self), toks, cfg, st, s_eat(toks, st, tok_of(k))),
            r is Ok ==> s_eat(toks, st, tok_of(k)).st.cur == st.cur + 1,
    {
        proof {
            lemma_rest_step(toks, st.cur + 1);
            if st.cur == toks.len() - 1 { assert(cur_tok(toks, st) == toks.last()); }
        }
        if kind_eq(self.current_token.token_type, k) {
            let line = self.current_token.line;
            match self.lexer.try_get_next_token() {
                Ok(t) => {
                    self.last_line = line;
                    self.current_token = t;
                    Ok(())
                },
                Err(e) => Err(e),
            }
        } else {
            Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() })
        }
    }

    /// Consumes the final `Eof` of an item, otherwise raises error.
    fn eat_eof(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: Result<(), BcError>)
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            match r {
                Ok(()) => s_eat(toks, st, Tok::Eof).ok && r_pc(*final(self), toks, cfg, s_eat(toks, st, Tok::Eof).st)
                    && s_eat(toks, st, Tok::Eof).st.nodes == st.nodes && s_eat(toks, st, Tok::Eof).st.cur == st.cur + 1 && s_eat(toks, st, Tok::Eof).st.depth == st.depth,
                Err(x) => r_perr(x, final(self).extension_uses@, s_eat(toks, st, Tok::Eof)),
            },
    {
        proof { lemma_rest_step(toks, st.cur + 1); }
        if matches!(self.current_token.token_type, TokenType::Eof) {
            let line = self.current_token.line;
            match self.lexer.try_get_next_token() {
                Ok(t) => {
                    self.last_line = line;
                    self.current_token = t;
                    proof { assert(cur_tok(toks, st) == toks.last()); }
                    Ok(())
                },
                Err(e) => Err(e),
            }
        } else {
            Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() })
        }
    }

    /// Records a use of non-POSIX syntax on the line of the current token, as GNU bc does.
    fn extension(&mut self, description: String, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>, Ghost(desc): Ghost<GBytes>)
        requires
            r_p(*old(self), toks, cfg, st),
            text_view(description) == desc,
        ensures
            r_p(*final(self), toks, cfg, s_extension(toks, cfg, st, desc)),
    {
        if !matches!(self.extension_policy, ExtensionPolicy::Allow) {
            self.extension_uses.push((self.current_token.line, description));
            proof {
                let s2 = s_extension(toks, cfg, st, desc);
                assert(s2.ext == st.ext.push(ExtUse { line: cur_tok(toks, st).line, desc }));
                assert forall|i: int| 0 <= i < self.extension_uses@.len() implies s2.ext[i].line == (#[trigger] self.extension_uses@[i]).0 as u64
                    && s2.ext[i].desc == text_view(self.extension_uses@[i].1) by {
                    if i < st.ext.len() {
                        assert(old(self).extension_uses@[i] == self.extension_uses@[i]);
                    }
                }
            }
        }
    }

    fn note_name(&mut self, name: &[u8], Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>)
        requires
            r_p(*old(self), toks, cfg, st),
            all_ascii(name@),
        ensures
            r_p(*final(self), toks, cfg, s_note_name(toks, cfg, st, name@)),
    {
        if name.len() > 1 {
            let prefix: [u8; 23] = [109u8, 117, 108, 116, 105, 112, 108, 101, 32, 108, 101, 116, 116, 101, 114, 32, 110, 97, 109, 101, 32, 45, 32];
            let mut v: Vec<u8> = Vec::new();
            let mut i: usize = 0;
            proof { assert(prefix@ =~= multi_letter_prefix()); }
            while i < 23
                invariant
                    0 <= i <= 23,
                    prefix@ == multi_letter_prefix(),
                    v@ == prefix@.subrange(0, i as int),
                decreases 23 - i,
            {
                v.push(prefix[i]);
                proof { assert(v@ =~= prefix@.subrange(0, i + 1)); }
                i += 1;
            }
            let mut j: usize = 0;
            while j < name.len()
                invariant
                    0 <= j <= name@.len(),
                    prefix@ == multi_letter_prefix(),
                    v@ == prefix@.add(name@.subrange(0, j as int)),
                decreases name@.len() - j,
            {
                v.push(name[j]);
                proof { assert(v@ =~= prefix@.add(name@.subrange(0, j + 1))); }
                j += 1;
            }
            proof {
                assert(name@.subrange(0, name@.len() as int) =~= name@);
                assert forall|i: int| 0 <= i < v@.len() implies v@[i] < 0x80 by {
                    if i >= 23 { assert(v@[i] == name@[i - 23]); }
                    else { assert(v@[i] == multi_letter_prefix()[i]); }
                }
            }
            let d = ascii_string(v.as_slice());
            self.extension(d, Ghost(toks), Ghost(cfg), Ghost(st), Ghost(multi_letter_prefix().add(name@)));
        }
    }

    /// Consumes an identifier, recording it if it is longer than one letter (an extension).
    fn eat_name(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: Result<String, BcError>)
        requires
            r_p(*old(self), toks, cfg, st),
            cur_tok(toks, st).kind is Letter,
        ensures
            match r {
                Ok(s) => s_eat_name(toks, cfg, st).ok && r_p(*final(self), toks, cfg, s_eat_name(toks, cfg, st).st)
                    && text_view(s) == s_eat_name(toks, cfg, st).name
                    && s_eat_name(toks, cfg, st).st.nodes == st.nodes && s_eat_name(toks, cfg, st).st.cur >= st.cur,
                Err(x) => r_perr(x, final(self).extension_uses@, s_eat_name(toks, cfg, st)),
            },
    {
        let v = self.current_token.value.clone();
        proof {
            if st.cur < toks.len() {
                assert(toks[st.cur as int].kind is Letter);
            } else {
                assert(toks[toks.len() - 1].kind is Letter);
            }
            assert(v@ == cur_tok(toks, st).text);
        }
        let name = ascii_string(v.as_slice());
        let ghost e = s_eat(toks, st, Tok::Letter);
        match self.eat(TokenType::Letter, Ghost(toks), Ghost(cfg), Ghost(st)) {
            Ok(()) => {},
            Err(x) => return Err(x),
        }
        self.note_name(v.as_slice(), Ghost(toks), Ghost(cfg), Ghost(e.st));
        Ok(name)
    }

    /// Skips sequence of newline tokens.
    #[verifier::exec_allows_no_decreases_clause]
    fn skip_newlines(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_unit(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_skip_newlines(toks, st, f)] pdone(p_skip_newlines(toks, st, f)) ==> p_skip_newlines(toks, st, f) == r.1@,
    {
        let ghost mut cur = st;
        loop
            invariant
                r_p(*self, toks, cfg, cur),
                cur.nodes == st.nodes,
                cur.cur >= st.cur,
                cur.depth == st.depth,
                forall|f: u64| #![trigger p_skip_newlines(toks, st, f)] pdone(p_skip_newlines(toks, st, f)) ==>
                    exists|g: u64| #![trigger p_skip_newlines(toks, cur, g)] p_skip_newlines(toks, cur, g) == p_skip_newlines(toks, st, f),
        {
            let ghost c0 = cur;
            if !matches!(self.current_token.token_type, TokenType::Newline) {
                proof { lemma_skip_done(toks, st, cur); }
                return (Ok(()), Ghost(pr_ok(cur)));
            }
            let ghost e = s_eat(toks, c0, Tok::Newline);
            proof { lemma_skip_step(toks, st, c0); }
            match self.eat(TokenType::Newline, Ghost(toks), Ghost(cfg), Ghost(c0)) {
                Ok(()) => { proof { cur = e.st; } },
                Err(x) => return (Err(x), Ghost(e)),
            }
        }
    }

}

/// `p_skip_newlines` stops at a token other than a newline.
proof fn lemma_skip_done(toks: Seq<SToken>, st: PState, cur: PState)
    requires
        !(cur_tok(toks, cur).kind is Newline),
        forall|f: u64| #![trigger p_skip_newlines(toks, st, f)] pdone(p_skip_newlines(toks, st, f)) ==>
            exists|g: u64| #![trigger p_skip_newlines(toks, cur, g)] p_skip_newlines(toks, cur, g) == p_skip_newlines(toks, st, f),
    ensures
        forall|f: u64| #![trigger p_skip_newlines(toks, st, f)] pdone(p_skip_newlines(toks, st, f)) ==> p_skip_newlines(toks, st, f) == pr_ok(cur),
{
    assert forall|f: u64| #![trigger p_skip_newlines(toks, st, f)] pdone(p_skip_newlines(toks, st, f)) implies p_skip_newlines(toks, st, f) == pr_ok(cur) by {
        let g = choose|g: u64| #![trigger p_skip_newlines(toks, cur, g)] p_skip_newlines(toks, cur, g) == p_skip_newlines(toks, st, f);
        assert(g > 0);
    }
}

/// `p_skip_newlines` takes a newline and continues, or stops with the error of `eat`.
proof fn lemma_skip_step(toks: Seq<SToken>, st: PState, cur: PState)
    requires
        cur_tok(toks, cur).kind is Newline,
        forall|f: u64| #![trigger p_skip_newlines(toks, st, f)] pdone(p_skip_newlines(toks, st, f)) ==>
            exists|g: u64| #![trigger p_skip_newlines(toks, cur, g)] p_skip_newlines(toks, cur, g) == p_skip_newlines(toks, st, f),
    ensures
        ({
            let e = s_eat(toks, cur, Tok::Newline);
            if e.ok {
                forall|f: u64| #![trigger p_skip_newlines(toks, st, f)] pdone(p_skip_newlines(toks, st, f)) ==>
                    exists|g: u64| #![trigger p_skip_newlines(toks, e.st, g)] p_skip_newlines(toks, e.st, g) == p_skip_newlines(toks, st, f)
            } else {
                forall|f: u64| #![trigger p_skip_newlines(toks, st, f)] pdone(p_skip_newlines(toks, st, f)) ==> p_skip_newlines(toks, st, f) == e
            }
        }),
{
    let e = s_eat(toks, cur, Tok::Newline);
    assert forall|f: u64| #![trigger p_skip_newlines(toks, st, f)] pdone(p_skip_newlines(toks, st, f)) implies
        (if e.ok { exists|g: u64| #![trigger p_skip_newlines(toks, e.st, g)] p_skip_newlines(toks, e.st, g) == p_skip_newlines(toks, st, f) } else { p_skip_newlines(toks, st, f) == e }) by {
        let g = choose|g: u64| #![trigger p_skip_newlines(toks, cur, g)] p_skip_newlines(toks, cur, g) == p_skip_newlines(toks, st, f);
        assert(g > 0);
        if e.ok {
            assert(p_skip_newlines(toks, e.st, (g - 1) as u64) == p_skip_newlines(toks, st, f));
        }
    }
}

/// The state `s` came after `s0` in an expression: the arena grew by at most one node per token.
spec fn r_grown(s0: PState, s: PState) -> bool {
    &&& extends(s0.nodes, s.nodes)
    &&& s.cur > s0.cur
    &&& s.nodes.len() - s0.nodes.len() <= s.cur - s0.cur
    &&& s.depth == s0.depth
}

spec fn r_xres(r: Result<usize, BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(x) => p.ok && r_p(q, toks, cfg, p.st) && r_grown(s0, p.st) && x == p.node && x < p.st.nodes.len(),
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

/// A name or a number is ASCII.
proof fn lemma_cur_ascii(toks: Seq<SToken>, st: PState)
    requires
        toks_wf(toks),
        cur_tok(toks, st).kind is Letter || cur_tok(toks, st).kind is Number,
    ensures
        all_ascii(cur_tok(toks, st).text),
{
    if st.cur >= toks.len() {
        assert(toks[toks.len() - 1].kind is Eof || toks[toks.len() - 1].kind is LexError);
    }
}

/// The parser `b` is `a` with the node `n` added.
spec fn pushed(a: Parser, b: Parser, n: PNode) -> bool {
    &&& b.nodes@ == a.nodes@.push(n)
    &&& b.lexer == a.lexer
    &&& b.current_token == a.current_token
    &&& b.loop_depth == a.loop_depth
    &&& b.in_function == a.in_function
    &&& b.extension_policy == a.extension_policy
    &&& b.extension_uses == a.extension_uses
    &&& b.depth == a.depth
    &&& b.last_line == a.last_line
    &&& b.max_depth == a.max_depth
}

impl Parser {
    /// Reports input nested deeper than `max_depth`, on the line of the last consumed token
    /// (the limit is often detected when the current token is already the next line's).
    fn too_deep_error(&self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (e: BcError)
        requires
            r_p(*self, toks, cfg, st),
        ensures
            r_perr(e, self.extension_uses@, too_deep(st)),
    {
        let m = [110u8, 101, 115, 116, 105, 110, 103, 32, 116, 111, 111, 32, 100, 101, 101, 112];
        proof { assert(m@ =~= too_deep(st).err.msg); }
        BcError::Syntax { line: self.last_line, message: ascii_string(m.as_slice()) }
    }
}

/// The state `s` came after `s0` in a statement.
spec fn r_sgrown(s0: PState, s: PState) -> bool {
    &&& extends(s0.nodes, s.nodes)
    &&& s.cur > s0.cur
    &&& s.nodes.len() - s0.nodes.len() <= 2 * (s.cur - s0.cur)
    &&& s.depth == s0.depth
}

spec fn r_sres(r: Result<usize, BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(x) => p.ok && p.flag && r_p(q, toks, cfg, p.st) && r_sgrown(s0, p.st) && x == p.node && x < p.st.nodes.len(),
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

spec fn r_lres(r: Result<Vec<usize>, BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(l) => p.ok && r_p(q, toks, cfg, p.st) && extends(s0.nodes, p.st.nodes) && p.st.cur >= s0.cur
            && p.st.nodes.len() - s0.nodes.len() <= 2 * (p.st.cur - s0.cur) && p.st.depth == s0.depth
            && l@ == p.list,
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

impl Parser {
    /// Parses the program fully, returning Err on lexical/syntax error or `"quit"`. The proved
    /// theorem is that of `parse_program_ref` (connected to the specification in `run_unit`).
    #[verifier::external_body]
    /// Parses the program: the indices of its statements in the arena [`Parser::take_code`].
    pub fn try_parse_program(&mut self) -> Result<Vec<usize>, BcError> {
        self.parse_program_ref(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary())).0
    }
}


/// The tokens of a unit within the limit are as the parser's proofs expect them.
proof fn lemma_tokenize_wf(t: Seq<u8>)
    requires
        t.len() <= 1_000_000_000,
    ensures
        toks_wf(tokenize(t)),
{
    let r = tokenize(t);
    lemma_lex_shape(t, normal(1u64), seq![]);
    lemma_lex_len(t, normal(1u64), seq![]);
    assert forall|i: int| 0 <= i < r.len() - 1 implies !(#[trigger] r[i].kind is Eof) && !(r[i].kind is LexError) by {
        assert(tok_good(r[i]));
    }
    assert forall|i: int| 0 <= i < r.len() && (#[trigger] r[i].kind is Letter || r[i].kind is Number) implies all_ascii(r[i].text) by {
        if i < r.len() - 1 {
            assert(tok_good(r[i]));
            assert(ascii_bytes(r[i].text));
        }
    }
}

/// A parsed unit: its statements (indices into the arena) or its error, the uses of extensions
/// (line and name), and the arena.
pub(crate) type ParsedUnit = (Result<Vec<usize>, BcError>, Vec<(usize, String)>, Code);

/// Parses a unit of at most `BC_UNIT_MAX` bytes: the statements or the error, and the extension
/// uses, are those of the specification's `parse_unit`, unless the specification runs out of fuel.
pub(crate) fn parse_unit_ref(unit: &[u8], policy: ExtensionPolicy, max_depth: usize, Ghost(cfg): Ghost<GCfg>) -> (r: ParsedUnit)
    requires
        unit@.len() <= 1_000_000_000,
        max_depth < usize::MAX - 2,
        (policy != ExtensionPolicy::Allow) == cfg.record_extensions,
        max_depth as u64 == cfg.max_depth,
    ensures
        pdone(parse_unit(tokenize(unit@), cfg)) ==> r_parsed(r.0, r.1@, r.2, parse_unit(tokenize(unit@), cfg)),
{
    let ghost toks = tokenize(unit@);
    let ghost st0 = PState { cur: 0usize, depth: 0u64, last_line: 1u64, loop_depth: 0u64, in_function: false, ext: seq![], nodes: seq![] };
    let mut lexer = Lexer::new(unit);
    proof { lemma_tokenize_wf(unit@); lemma_rest_step(toks, 0); }
    let current_token = match lexer.try_get_next_token() {
        Ok(t) => t,
        Err(e) => {
            let none = Vec::new();
            proof { assert(r_ext(none@, st0.ext)); }
            return (Err(e), none, Code { nodes: Vec::new() });
        },
    };
    let mut parser = Parser {
        lexer,
        current_token,
        loop_depth: 0,
        in_function: false,
        extension_policy: policy,
        extension_uses: Vec::new(),
        depth: 0,
        last_line: 1,
        max_depth,
        nodes: Vec::with_capacity(8),
    };
    proof {
        assert(toks.skip(0) =~= toks);
        assert(rest_of(toks, 0) == toks);
        assert(r_ext(parser.extension_uses@, st0.ext));
    }
    let (res, Ghost(p)) = parser.parse_program_ref(Ghost(toks), Ghost(cfg), Ghost(st0));
    let ext = parser.extension_uses;
    let code = Code { nodes: parser.nodes };
    proof {
        let whole = parse_unit(toks, cfg);
        if pdone(whole) {
            assert(whole == p_program(toks, cfg, st0, seq![], 0x4000_0000_0000_0000u64));
            assert(whole == p);
        }
    }
    (res, ext, code)
}

} // verus!

impl Parser {
    /// Creates a new Parser from the Lexer, returning Err on initial lexical error.
    pub fn try_new(mut lexer: Lexer) -> Result<Self, BcError> {
        let current_token = lexer.try_get_next_token()?;
        Ok(Self {
            lexer,
            current_token,
            loop_depth: 0,
            in_function: false,
            extension_policy: ExtensionPolicy::Allow,
            extension_uses: Vec::new(),
            depth: 0,
            last_line: 1,
            max_depth: DEFAULT_MAX_DEPTH,
            nodes: Vec::new(),
        })
    }

    /// Sets the nesting limit (see [`DEFAULT_MAX_DEPTH`]).
    /// The arena of the nodes parsed so far, which it leaves empty.
    pub fn take_code(&mut self) -> Code {
        Code {
            nodes: core::mem::take(&mut self.nodes),
        }
    }

    pub fn set_max_depth(&mut self, max_depth: usize) {
        self.max_depth = max_depth;
    }

    /// Creates a new Parser from the Lexer.
    #[cfg(test)]
    pub fn new(lexer: Lexer) -> Self {
        Self::try_new(lexer).unwrap_or_else(|e| panic!("{:?}", e))
    }

    /// Sets how uses of non-POSIX syntax are treated.
    pub fn set_extension_policy(&mut self, policy: ExtensionPolicy) {
        self.extension_policy = policy;
    }

    /// Returns and clears the recorded uses of non-POSIX syntax, as `(line, description)` with
    /// GNU bc's descriptions (e.g. `multiple letter name - abc`).
    pub fn take_extension_uses(&mut self) -> Vec<(usize, String)> {
        core::mem::take(&mut self.extension_uses)
    }
}
