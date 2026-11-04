// SPDX-License-Identifier: MIT

//! The parser: recursive descent, with Pratt precedence climbing for expressions.

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
    match (a, b) {
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
        | (TokenType::Scale, TokenType::Scale) | (TokenType::Sqrt, TokenType::Sqrt) | (TokenType::While, TokenType::While) => true,
        _ => false,
    }
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

spec fn r_plist(r: Result<Vec<Param>, BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(l) => p.ok && r_p(q, toks, cfg, p.st) && p.st.nodes == s0.nodes && p.st.cur >= s0.cur && p.st.depth == s0.depth && r_params(l@, p.params),
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

spec fn r_eres(r: Result<(usize, usize), BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok((x, h)) => p.ok && r_p(q, toks, cfg, p.st) && h as u64 == p.h && h <= q.max_depth + 2
            && r_grown(s0, p.st) && x == p.node && x < p.st.nodes.len(),
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

spec fn r_xres(r: Result<usize, BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(x) => p.ok && r_p(q, toks, cfg, p.st) && r_grown(s0, p.st) && x == p.node && x < p.st.nodes.len(),
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

spec fn r_ares(r: Result<(Vec<PArg>, usize), BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok((a, h)) => p.ok && r_p(q, toks, cfg, p.st) && h as u64 == p.h && h <= q.max_depth + 1
            && extends(s0.nodes, p.st.nodes) && p.st.cur >= s0.cur
            && p.st.nodes.len() - s0.nodes.len() <= p.st.cur - s0.cur && p.st.depth == s0.depth
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
    /// Adds an expression's node to the arena (the specification's `add_node`).
    fn add_expr(&mut self, pn: PNode, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(s0): Ghost<GState>, Ghost(s): Ghost<GState>, Ghost(n): Ghost<GNode>, Ghost(h): Ghost<u64>) -> (idx: usize)
        requires
            r_p(*old(self), toks, cfg, s),
            r_node(pn, n),
            extends(s0.nodes, s.nodes),
            s0.nodes.len() <= 2 * s0.cur,
            s.nodes.len() - s0.nodes.len() + 1 <= s.cur - s0.cur,
            s.depth == s0.depth,
        ensures
            pushed(*old(self), *final(self), pn),
            ({
                let g = add_node(s, n, h);
                &&& g.ok
                &&& g.h == h
                &&& g.node == idx
                &&& idx == s.nodes.len()
                &&& g.st.nodes.len() == s.nodes.len() + 1
                &&& g.st.nodes[g.node as int] == n
                &&& g.st.cur == s.cur
                &&& g.st.ext == s.ext
                &&& r_p(*final(self), toks, cfg, g.st)
                &&& extends(s.nodes, g.st.nodes)
                &&& r_grown(s0, g.st)
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
    fn parse_expression(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
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
    fn parse_relational_expression(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
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
                st.nodes.len() <= 2 * st.cur,
                left == node && left < cur.nodes.len(),
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
            r.0 is Ok ==> r.1@.st.nodes.len() - st.nodes.len() + 1 <= r.1@.st.cur - st.cur,
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
    #[verifier::rlimit(60)]
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
                    assert(n.st.nodes.len() == st.nodes.len());
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
                extends(st.nodes, cur.nodes),
                cur.cur >= st.cur,
                cur.nodes.len() - st.nodes.len() <= cur.cur - st.cur,
                cur.depth == st.depth,
                st.nodes.len() <= 2 * st.cur,
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
            let arg_h: usize;
            if is_arr {
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
                arg_h = 1;
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
                arg_h = h;
            }
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

/// The diagnostic or description `end_of_line`.
fn end_of_line_text() -> (r: String)
    ensures
        text_view(r) == eol_msg(),
{
    let m = [69u8, 110, 100, 32, 111, 102, 32, 108, 105, 110, 101, 32, 114, 101, 113, 117, 105, 114, 101, 100];
    proof { assert(m@ =~= eol_msg()); }
    ascii_string(m.as_slice())
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

impl Parser {
    /// Adds a statement's node to the arena (the specification's `add_node`).
    fn add_stmt(&mut self, pn: PNode, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(s0): Ghost<GState>, Ghost(s): Ghost<GState>, Ghost(n): Ghost<GNode>, Ghost(h): Ghost<u64>) -> (idx: usize)
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
    fn parse_program_ref(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Vec<usize>, BcError>, Ghost<GResult>))
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
    #[verifier::rlimit(300)]
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
    #[verifier::rlimit(300)]
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_statement_list(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Vec<usize>, BcError>, Ghost<GResult>))
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
            match res {
                Ok(()) => {},
                Err(y) => {
                    proof {
                        assert forall|k: u64| #![trigger p_statement_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_statement_list(toks, cfg, c, a0, k)) implies p_statement_list(toks, cfg, c, a0, k) == sk by {
                            assert(pdone(p_skip_newlines(toks, c, (k - 1) as u64)));
                        }
                        lemma_sl_ret(toks, cfg, st, c, a0, sk);
                    }
                    return (Err(y), Ghost(sk));
                },
            }
            let k = self.current_token.token_type;
            if matches!(k, TokenType::Eof) || matches!(k, TokenType::Rbrace) {
                let ghost g = pr_list(sk.st, a0);
                proof {
                    assert forall|k: u64| #![trigger p_statement_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_statement_list(toks, cfg, c, a0, k)) implies p_statement_list(toks, cfg, c, a0, k) == g by {
                        assert(pdone(p_skip_newlines(toks, c, (k - 1) as u64)));
                    }
                    lemma_sl_ret(toks, cfg, st, c, a0, g);
                }
                return (Ok(stmts), Ghost(g));
            }
            let ghost old_stmts = stmts@;
            let (res2, Ghost(i)) = self.parse_statement(Ghost(toks), Ghost(cfg), Ghost(sk.st));
            let x = match res2 {
                Ok(v) => v,
                Err(y) => {
                    proof {
                        assert forall|k: u64| #![trigger p_statement_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_statement_list(toks, cfg, c, a0, k)) implies p_statement_list(toks, cfg, c, a0, k) == i by {
                            assert(pdone(p_skip_newlines(toks, c, (k - 1) as u64)));
                            assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
                        }
                        lemma_sl_ret(toks, cfg, st, c, a0, i);
                    }
                    return (Err(y), Ghost(i));
                },
            };
            let ghost a1 = a0.push(i.node);
            stmts.push(x);
            proof { assert(stmts@ =~= old_stmts.push(x)); }
            let nk = self.current_token.token_type;
            let ghost line = cur_tok(toks, i.st).line;
            if matches!(nk, TokenType::Rbrace) || matches!(nk, TokenType::Eof) {
                let ghost g = pr_list(i.st, a1);
                proof {
                    assert forall|k: u64| #![trigger p_statement_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_statement_list(toks, cfg, c, a0, k)) implies p_statement_list(toks, cfg, c, a0, k) == g by {
                        assert(pdone(p_skip_newlines(toks, c, (k - 1) as u64)));
                        assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
                    }
                    lemma_sl_ret(toks, cfg, st, c, a0, g);
                }
                return (Ok(stmts), Ghost(g));
            }
            if !matches!(nk, TokenType::Semicolon) && !matches!(nk, TokenType::Newline) {
                let ghost g = syntax_at(i.st, line);
                proof {
                    assert forall|k: u64| #![trigger p_statement_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_statement_list(toks, cfg, c, a0, k)) implies p_statement_list(toks, cfg, c, a0, k) == g by {
                        assert(pdone(p_skip_newlines(toks, c, (k - 1) as u64)));
                        assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
                    }
                    lemma_sl_ret(toks, cfg, st, c, a0, g);
                }
                return (Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() }), Ghost(g));
            }
            let ghost e = s_eat(toks, i.st, tok_of(nk));
            match self.eat(nk, Ghost(toks), Ghost(cfg), Ghost(i.st)) {
                Ok(()) => {
                    proof {
                        assert forall|k: u64| #![trigger p_statement_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_statement_list(toks, cfg, c, a0, k)) implies p_statement_list(toks, cfg, c, a0, k) == p_statement_list(toks, cfg, e.st, a1, (k - 1) as u64) by {
                            assert(pdone(p_skip_newlines(toks, c, (k - 1) as u64)));
                            assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
                        }
                        lemma_sl_next(toks, cfg, st, c, a0, e.st, a1);
                        cur = e.st;
                        acc = a1;
                    }
                },
                Err(y) => {
                    proof {
                        assert forall|k: u64| #![trigger p_statement_list(toks, cfg, c, a0, k)] k > 0 && pdone(p_statement_list(toks, cfg, c, a0, k)) implies p_statement_list(toks, cfg, c, a0, k) == e by {
                            assert(pdone(p_skip_newlines(toks, c, (k - 1) as u64)));
                            assert(pdone(p_statement(toks, cfg, sk.st, (k - 1) as u64)));
                        }
                        lemma_sl_ret(toks, cfg, st, c, a0, e);
                    }
                    return (Err(y), Ghost(e));
                },
            }
        }
    }

    /// Parses one statement as one level of nesting.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_statement(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
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

    #[verifier::rlimit(100)]
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
    #[verifier::rlimit(60)]
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
    #[verifier::rlimit(60)]
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

    /// Parses a function definition `define f(x) { ... }`.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_function(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<usize, BcError>, Ghost<GResult>))
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

/// Parses a unit of at most `BC_UNIT_MAX` bytes: the statements or the error, and the extension
/// uses, are those of the specification's `parse_unit`, unless the specification runs out of fuel.
pub(crate) fn parse_unit_ref(unit: &[u8], policy: ExtensionPolicy, max_depth: usize, Ghost(cfg): Ghost<GCfg>) -> (r: (Result<Vec<usize>, BcError>, Vec<(usize, String)>, Code))
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
