// SPDX-License-Identifier: MIT

//! The parser: recursive descent, with Pratt precedence climbing for expressions.

#[cfg(verus_keep_ghost)]
use super::all_ascii;
use super::ascii_string;
use super::lexer::syntax_error_text;
#[cfg(verus_keep_ghost)]
use super::lexer::{r_lex_err, r_next, tok_of, tok_view};
use super::{
    AssignOp, BinOp, Expr, ExprOrArray, ExtensionPolicy, FunctionDef, Lexer, Param, Register,
    RelOp, Stmt, Token, TokenType,
};
#[cfg(verus_keep_ghost)]
use crate::driver::r_ext;
use crate::error::BcError;
#[cfg(verus_keep_ghost)]
use crate::refine::{
    assign_code as r_assign_code, bin_code, extends, lemma_r_args_extend, lemma_r_args_push,
    lemma_r_expr_extend, named, r_arg, r_args, r_expr, r_param, r_params, rel_code as r_rel_code,
    text_view,
};
use crate::verified_kernels::{
    TOK_ASSIGN_OP, TOK_EXP_OP, TOK_MUL_OP, TOK_PLUS_MINUS, verified_nesting_within_limit,
    verified_pratt_infix_info,
};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use bc_spec::lexer::{Tok, Token as SToken, syntax_error_msg};
#[cfg(verus_keep_ghost)]
use bc_spec::parser::Param as SParam;
#[cfg(verus_keep_ghost)]
use bc_spec::parser::{
    Arg, ExtUse, Node, PCfg, PR, PState, add_node, assign_code as s_assign_code, binop_code,
    cur_tok, eat as s_eat, eat_name as s_eat_name, extension as s_extension, inc,
    infix_info as s_infix_info, lex_err, max_u64, multi_letter_prefix, no_err,
    note_name as s_note_name, p_arg_list, p_builtin, p_call, p_define_list, p_expr_loop,
    p_expr_prec, p_named, p_named_tail, p_opt_auto, p_parenthesized, p_prefix, p_primary,
    p_relational, p_skip_newlines, p_subscript, peek_kind, pr_args, pr_node, pr_ok, pr_params,
    rel_code as s_rel_code, st_set_depth, syntax_at, token_at, too_deep, within,
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
}

broadcast use vstd::std_specs::vec::group_vec_axioms;

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
    &&& toks_wf(toks)
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
        Ok(()) => p.ok && r_p(q, toks, cfg, p.st) && p.st.nodes == s0.nodes && p.st.cur >= s0.cur,
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

spec fn r_plist(r: Result<Vec<Param>, BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(l) => p.ok && r_p(q, toks, cfg, p.st) && p.st.nodes == s0.nodes && p.st.cur >= s0.cur && r_params(l@, p.params),
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
            st.cur < toks.len() || !(tok_of(k) is Eof),
        ensures
            r_unit(r, *final(self), toks, cfg, st, s_eat(toks, st, tok_of(k))),
    {
        proof { lemma_rest_step(toks, st.cur + 1); }
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

    #[verifier::external_body]
    fn parse_relational_expression_(&mut self) -> Result<Expr, BcError> {
        self.parse_relational_expression(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary())).0
    }

    #[verifier::external_body]
    fn parse_expression_(&mut self) -> Result<Expr, BcError> {
        self.parse_expression(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary())).0
    }

    #[verifier::external_body]
    fn too_deep_(&self) -> BcError {
        self.too_deep_error(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }

    #[verifier::external_body]
    fn eat_(&mut self, k: TokenType) -> Result<(), BcError> {
        self.eat(k, Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }

    #[verifier::external_body]
    fn extension_(&mut self, description: String) {
        self.extension(description, Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }

    #[verifier::external_body]
    fn note_name_(&mut self, name: &str) {
        self.note_name(name.as_bytes(), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }

    #[verifier::external_body]
    fn skip_newlines_(&mut self) -> Result<(), BcError> {
        self.skip_newlines(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary())).0
    }

    #[verifier::external_body]
    fn parse_opt_define_list_(&mut self) -> Result<Vec<Param>, BcError> {
        self.parse_opt_define_list(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary())).0
    }

    #[verifier::external_body]
    fn parse_opt_auto_define_list_(&mut self) -> Result<Vec<Param>, BcError> {
        self.parse_opt_auto_define_list(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary())).0
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

spec fn r_eres(r: Result<(Expr, usize), BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok((x, h)) => p.ok && r_p(q, toks, cfg, p.st) && h as u64 == p.h && h <= q.max_depth + 2
            && r_grown(s0, p.st) && r_expr(x, p.st.nodes, p.node),
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

spec fn r_xres(r: Result<Expr, BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok(x) => p.ok && r_p(q, toks, cfg, p.st) && r_grown(s0, p.st) && r_expr(x, p.st.nodes, p.node),
        Err(x) => r_perr(x, q.extension_uses@, p),
    }
}

spec fn r_ares(r: Result<(Vec<ExprOrArray>, usize), BcError>, q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, p: PR) -> bool {
    match r {
        Ok((a, h)) => p.ok && r_p(q, toks, cfg, p.st) && h as u64 == p.h && h <= q.max_depth + 1
            && extends(s0.nodes, p.st.nodes) && p.st.cur >= s0.cur
            && p.st.nodes.len() - s0.nodes.len() <= p.st.cur - s0.cur && p.st.depth == s0.depth
            && r_args(a@, p.st.nodes, p.args),
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

/// Adding a node to the arena after at least one more token.
proof fn lemma_node(q: Parser, toks: Seq<SToken>, cfg: PCfg, s0: PState, s: PState, n: Node, h: u64)
    requires
        r_p(q, toks, cfg, s),
        extends(s0.nodes, s.nodes),
        s0.nodes.len() <= 2 * s0.cur,
        s.nodes.len() - s0.nodes.len() + 1 <= s.cur - s0.cur,
        s.depth == s0.depth,
    ensures
        ({
            let g = add_node(s, n, h);
            &&& g.ok
            &&& g.h == h
            &&& g.node == s.nodes.len()
            &&& g.st.nodes.len() == s.nodes.len() + 1
            &&& g.st.nodes[g.node as int] == n
            &&& g.st.cur == s.cur
            &&& g.st.ext == s.ext
            &&& r_p(q, toks, cfg, g.st)
            &&& extends(s.nodes, g.st.nodes)
            &&& r_grown(s0, g.st)
        }),
{
    let g = add_node(s, n, h);
    assert(g.st.nodes =~= s.nodes.push(n));
    assert(cur_tok(toks, g.st) == cur_tok(toks, s));
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
    fn parse_expression(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Expr, BcError>, Ghost<GResult>))
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
    fn parse_relational_expression(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<Expr, BcError>, Ghost<GResult>))
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
        let ghost g = add_node(rr.st, Node::Rel(s_rel_code(cur_tok(toks, l.st)), l.node, rr.node), sh);
        proof {
            lemma_node(*self, toks, cfg, st, rr.st, Node::Rel(s_rel_code(cur_tok(toks, l.st)), l.node, rr.node), sh);
            lemma_r_expr_extend(left, l.st.nodes, g.st.nodes, l.node);
            lemma_r_expr_extend(right, rr.st.nodes, g.st.nodes, rr.node);
                assert forall|f: u64| #![trigger p_relational(toks, cfg, st, f)] pdone(p_relational(toks, cfg, st, f)) implies p_relational(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, st, 0i8, (f - 1) as u64)));
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                }
        }
        (Ok(Expr::RelationalOp(op, Box::new(left), Box::new(right))), Ghost(g))
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
    fn parse_expr_precedence(&mut self, min_prec: i8, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
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
    fn parse_expr_precedence_inner(&mut self, min_prec: i8, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
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
                r_expr(left, cur.nodes, node),
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
            let ghost nd = add_node(rr.st, Node::Binary(binop_code(t), n0, rr.node), sh2);
            proof {
                lemma_node(*self, toks, cfg, st, rr.st, Node::Binary(binop_code(t), n0, rr.node), sh2);
                lemma_r_expr_extend(left, c.nodes, nd.st.nodes, n0);
                lemma_r_expr_extend(right, rr.st.nodes, nd.st.nodes, rr.node);
                assert forall|g: u64| #![trigger p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)] g > 0 && pdone(p_expr_loop(toks, cfg, c, n0, h0, min_prec, g)) implies p_expr_loop(toks, cfg, c, n0, h0, min_prec, g) == p_expr_loop(toks, cfg, nd.st, nd.node, sh2, min_prec, (g - 1) as u64) by {
                        assert(pdone(p_expr_prec(toks, cfg, e.st, next_min_prec, (g - 1) as u64)));
                    }
                lemma_loop_next(toks, cfg, st, min_prec, c, n0, h0, nd.st, nd.node, sh2);
                cur = nd.st;
                node = nd.node;
                sh = sh2;
            }
            left = Expr::BinaryOp(op, Box::new(left), Box::new(right));
            height = h2;
        }
    }

    /// Parses prefixes (unary operators).
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_prefix(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
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
            let ghost g = add_node(a.st, Node::Neg(a.node), inc(a.h));
            proof {
                lemma_node(*self, toks, cfg, st, a.st, Node::Neg(a.node), inc(a.h));
                lemma_r_expr_extend(x, a.st.nodes, g.st.nodes, a.node);
                assert forall|f: u64| #![trigger p_prefix(toks, cfg, st, f)] pdone(p_prefix(toks, cfg, st, f)) implies p_prefix(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 5i8, (f - 1) as u64)));
                }
            }
            (Ok((Expr::Negate(Box::new(x)), h + 1)), Ghost(g))
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
            let ghost g = add_node(a.st, Node::Update(is_inc, true, a.node), inc(a.h));
            proof {
                lemma_node(*self, toks, cfg, st, a.st, Node::Update(is_inc, true, a.node), inc(a.h));
                lemma_r_expr_extend(x, a.st.nodes, g.st.nodes, a.node);
                assert forall|f: u64| #![trigger p_prefix(toks, cfg, st, f)] pdone(p_prefix(toks, cfg, st, f)) implies p_prefix(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_named(toks, cfg, e.st, (f - 1) as u64)));
                }
            }
            (Ok((Expr::Update(is_inc, true, Box::new(x)), h + 1)), Ghost(g))
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
    fn parse_parenthesized(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
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
    fn parse_builtin(&mut self, which: u8, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
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
        let ghost g = add_node(a.st, n, inc(a.h));
        proof {
            lemma_node(*self, toks, cfg, st, a.st, n, inc(a.h));
            lemma_r_expr_extend(x, a.st.nodes, g.st.nodes, a.node);
            assert forall|f: u64| #![trigger p_builtin(toks, cfg, st, which, f)] pdone(p_builtin(toks, cfg, st, which, f)) implies p_builtin(toks, cfg, st, which, f) == g by {
                assert(f > 0);
                assert(pdone(p_parenthesized(toks, cfg, e.st, (f - 1) as u64)));
            }
        }
        let arg = Box::new(x);
        let call = if which == 0 { Expr::LengthCall(arg) } else if which == 1 { Expr::SqrtCall(arg) } else { Expr::ScaleCall(arg) };
        (Ok((call, h + 1)), Ghost(g))
    }

    /// Parses primary expressions (literals, variables, built-ins, calls).
    #[verifier::rlimit(60)]
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_primary(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
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
            let ghost g = add_node(e.st, Node::Number(t.text), 1u64);
            proof { lemma_node(*self, toks, cfg, st, e.st, Node::Number(t.text), 1u64); }
            return (Ok((Expr::Number(val), 1)), Ghost(g));
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
            let ghost g = add_node(a.st, Node::Paren(a.node), inc(a.h));
            proof {
                lemma_node(*self, toks, cfg, st, a.st, Node::Paren(a.node), inc(a.h));
                lemma_r_expr_extend(x, a.st.nodes, g.st.nodes, a.node);
                assert forall|f: u64| #![trigger p_primary(toks, cfg, st, f)] pdone(p_primary(toks, cfg, st, f)) implies p_primary(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_parenthesized(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (Ok((Expr::Paren(Box::new(x)), h + 1)), Ghost(g));
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
    fn parse_call(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
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
        let ghost g = add_node(e2.st, Node::Call(n.name, a.args), inc(a.h));
        proof {
            lemma_node(*self, toks, cfg, st, e2.st, Node::Call(n.name, a.args), inc(a.h));
            lemma_r_args_extend(args@, a.st.nodes, g.st.nodes, a.args);
            assert forall|f: u64| #![trigger p_call(toks, cfg, st, f)] pdone(p_call(toks, cfg, st, f)) implies p_call(toks, cfg, st, f) == g by {
                assert(f > 0);
                if !empty { assert(pdone(p_arg_list(toks, cfg, e.st, seq![], 0u64, (f - 1) as u64))); }
            }
        }
        (Ok((Expr::Call(name, args), h + 1)), Ghost(g))
    }

    /// Parses a named expression, then a postfix `++`/`--` or an assignment that binds to it.
    #[verifier::rlimit(60)]
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_named_tail(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
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
            let ghost g = add_node(e.st, Node::Update(is_inc, false, a.node), inc(a.h));
            proof {
                lemma_node(*self, toks, cfg, st, e.st, Node::Update(is_inc, false, a.node), inc(a.h));
                lemma_r_expr_extend(target, a.st.nodes, g.st.nodes, a.node);
                assert forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) implies p_named_tail(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_named(toks, cfg, st, (f - 1) as u64)));
                }
            }
            return (Ok((Expr::Update(is_inc, false, Box::new(target)), target_h + 1)), Ghost(g));
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
            let ghost g = add_node(v.st, nd, inc(max_u64(a.h, v.h)));
            proof {
                lemma_node(*self, toks, cfg, st, v.st, nd, inc(max_u64(a.h, v.h)));
                lemma_r_expr_extend(target, a.st.nodes, g.st.nodes, a.node);
                lemma_r_expr_extend(value, v.st.nodes, g.st.nodes, v.node);
                assert forall|f: u64| #![trigger p_named_tail(toks, cfg, st, f)] pdone(p_named_tail(toks, cfg, st, f)) implies p_named_tail(toks, cfg, st, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_named(toks, cfg, st, (f - 1) as u64)));
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 1i8, (f - 1) as u64)));
                }
            }
            let h = 1 + max_height(target_h, value_h);
            return (Ok((Expr::AssignOp(op, Box::new(target), Box::new(value)), h)), Ghost(g));
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
    fn parse_named_expression(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            r.0 matches Ok((x, h)) ==> named(x) && h <= final(self).max_depth + 1,
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
            let ghost g = add_node(e.st, Node::Reg(code), 1u64);
            proof { lemma_node(*self, toks, cfg, st, e.st, Node::Reg(code), 1u64); }
            return (Ok((Expr::RegisterAccess(reg), 1)), Ghost(g));
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
            let ghost g = add_node(n.st, Node::Var(n.name), 1u64);
            proof { lemma_node(*self, toks, cfg, st, n.st, Node::Var(n.name), 1u64); }
            return (Ok((Expr::Variable(name), 1)), Ghost(g));
        }
        (Err(BcError::Syntax { line: self.current_token.line, message: syntax_error_text() }), Ghost(syntax_at(st, t.line)))
    }

    /// Parses `[ expression ]` after the array name `name`.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_subscript(&mut self, name: String, Ghost(sname): Ghost<GBytes>, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Expr, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
            text_view(name) == sname,
        ensures
            r_eres(r.0, *final(self), toks, cfg, st, r.1@),
            r.0 matches Ok((x, h)) ==> x is ArrayAccess && h <= final(self).max_depth + 1,
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
        let ghost g = add_node(e2.st, Node::Array(sname, a.node), inc(a.h));
        proof {
            lemma_node(*self, toks, cfg, st, e2.st, Node::Array(sname, a.node), inc(a.h));
            lemma_r_expr_extend(idx, a.st.nodes, g.st.nodes, a.node);
                assert forall|f: u64| #![trigger p_subscript(toks, cfg, st, sname, f)] pdone(p_subscript(toks, cfg, st, sname, f)) implies p_subscript(toks, cfg, st, sname, f) == g by {
                    assert(f > 0);
                    assert(pdone(p_expr_prec(toks, cfg, e.st, 0i8, (f - 1) as u64)));
                }
        }
        (Ok((Expr::ArrayAccess(name, Box::new(idx)), h + 1)), Ghost(g))
    }

    /// Parses function call argument list; the height is that of the highest argument.
    #[verifier::exec_allows_no_decreases_clause]
    fn parse_argument_list(&mut self, Ghost(toks): Ghost<GToks>, Ghost(cfg): Ghost<GCfg>, Ghost(st): Ghost<GState>) -> (r: (Result<(Vec<ExprOrArray>, usize), BcError>, Ghost<GResult>))
        requires
            r_p(*old(self), toks, cfg, st),
        ensures
            r_ares(r.0, *final(self), toks, cfg, st, r.1@),
            forall|f: u64| #![trigger p_arg_list(toks, cfg, st, seq![], 0u64, f)] pdone(p_arg_list(toks, cfg, st, seq![], 0u64, f)) ==> p_arg_list(toks, cfg, st, seq![], 0u64, f) == r.1@,
    {
        let mut args: Vec<ExprOrArray> = Vec::new();
        let mut height: usize = 0;
        let ghost mut cur = st;
        let ghost mut acc = Seq::<Arg>::empty();
        let ghost mut sh = 0u64;
        proof {
            assert(args@ =~= Seq::<ExprOrArray>::empty());
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
                r_args(args@, cur.nodes, acc),
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
                    lemma_r_args_extend(old_args, c.nodes, a.st.nodes, a0);
                }
                args.push(ExprOrArray::ArrayArg(name));
                proof { assert(r_arg(args@.last(), a.st.nodes, Arg { is_array: is_arr, name: a.name, expr: a.node })); }
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
                    lemma_r_args_extend(old_args, c.nodes, a.st.nodes, a0);
                }
                args.push(ExprOrArray::Expr(x));
                proof { assert(r_arg(args@.last(), a.st.nodes, Arg { is_array: is_arr, name: a.name, expr: a.node })); }
                arg_h = h;
            }
            let ghost arg_s = Arg { is_array: is_arr, name: a.name, expr: a.node };
            let ghost a1 = a0.push(arg_s);
            let ghost h1 = max_u64(h0, a.h);
            proof {
                assert(args@ =~= old_args.push(args@.last()));
                lemma_r_args_push(old_args, a.st.nodes, a0, args@.last(), arg_s);
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
        })
    }

    /// Sets the nesting limit (see [`DEFAULT_MAX_DEPTH`]).
    pub fn set_max_depth(&mut self, max_depth: usize) {
        self.max_depth = max_depth;
    }

    /// Enters one level of nesting. The caller decrements `depth` when it leaves the level.
    fn enter_nesting(&mut self) -> Result<(), BcError> {
        if !verified_nesting_within_limit(self.depth, 1, self.max_depth) {
            return Err(self.too_deep_());
        }
        self.depth += 1;
        Ok(())
    }

    /// Creates a new Parser from the Lexer.
    #[cfg(test)]
    pub fn new(lexer: Lexer) -> Self {
        Self::try_new(lexer).unwrap_or_else(|e| panic!("{:?}", e))
    }

    /// Triggers a syntax error during parsing.
    fn error<T>(&self) -> Result<T, BcError> {
        Err(BcError::syntax(self.current_token.line))
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

    /// Reports a statement that is not allowed where it appears, with GNU bc's wording, on the
    /// line of the current token.
    fn misplaced<T>(&self, message: &str) -> Result<T, BcError> {
        Err(BcError::Syntax {
            line: self.current_token.line,
            message: String::from(message),
        })
    }

    /// Parses a loop body, tracking the loop nesting for `break`.
    fn parse_loop_body(&mut self) -> Result<Stmt, BcError> {
        self.loop_depth += 1;
        let body = self.parse_statement();
        self.loop_depth -= 1;
        body
    }

    /// Parses the program fully, returning Err on lexical/syntax error or `"quit"`.
    pub fn try_parse_program(&mut self) -> Result<Vec<Stmt>, BcError> {
        let mut items = Vec::new();
        while self.current_token.token_type != TokenType::Eof {
            if let Some(item) = self.parse_input_item()? {
                items.push(item);
            }
        }
        Ok(items)
    }

    /// Parses the program fully (entry point).
    #[cfg(test)]
    pub fn parse_program(&mut self) -> Vec<Stmt> {
        self.try_parse_program().unwrap_or_else(|e| {
            if e == BcError::Quit {
                panic!("quit");
            }
            panic!("{:?}", e);
        })
    }

    /// Parses a single top-level item (statement block or function definition).
    fn parse_input_item(&mut self) -> Result<Option<Stmt>, BcError> {
        if self.current_token.token_type == TokenType::Define {
            return Ok(Some(self.parse_function()?));
        }

        let lst = self.parse_semicolon_list()?;
        if self.current_token.token_type == TokenType::Newline {
            self.eat_(TokenType::Newline)?;
        } else {
            self.eat_(TokenType::Eof)?;
        }

        if lst.is_empty() {
            Ok(None)
        } else {
            Ok(Some(Stmt::Block(lst)))
        }
    }

    /// Parses a list of statements separated by semicolons.
    fn parse_semicolon_list(&mut self) -> Result<Vec<Stmt>, BcError> {
        let mut stmts = Vec::new();
        loop {
            let t = self.current_token.token_type;
            if t == TokenType::Newline || t == TokenType::Eof || t == TokenType::Rbrace {
                break;
            }
            if t == TokenType::Semicolon {
                self.eat_(TokenType::Semicolon)?;
                continue;
            }

            let stmt = self.parse_statement()?;
            stmts.push(stmt);

            if self.current_token.token_type == TokenType::Semicolon {
                self.eat_(TokenType::Semicolon)?;
            } else {
                break;
            }
        }
        Ok(stmts)
    }

    /// Parses a list of statements within a block (with newline and semicolon separations).
    fn parse_statement_list(&mut self) -> Result<Vec<Stmt>, BcError> {
        let mut stmts = Vec::new();
        loop {
            self.skip_newlines_()?;
            let t = self.current_token.token_type;
            if t == TokenType::Eof || t == TokenType::Rbrace {
                break;
            }

            let stmt = self.parse_statement()?;
            stmts.push(stmt);

            let nt = self.current_token.token_type;
            match nt {
                TokenType::Semicolon => {
                    self.eat_(TokenType::Semicolon)?;
                }
                TokenType::Newline => {
                    self.eat_(TokenType::Newline)?;
                }
                TokenType::Rbrace | TokenType::Eof => {}
                _ => return self.error(),
            }
        }
        Ok(stmts)
    }

    /// Parses a statement.
    /// Parses one statement as one level of nesting (see [`Height`]).
    fn parse_statement(&mut self) -> Result<Stmt, BcError> {
        self.enter_nesting()?;
        let result = self.parse_statement_inner();
        self.depth -= 1;
        result
    }

    fn parse_statement_inner(&mut self) -> Result<Stmt, BcError> {
        let t = self.current_token.token_type;
        match t {
            TokenType::String => self.parse_string_stmt(),
            TokenType::Break => self.parse_break_stmt(),
            TokenType::Quit => Err(BcError::Quit),
            TokenType::Return => self.parse_return_stmt(),
            TokenType::For => self.parse_for(),
            TokenType::If => self.parse_if(),
            TokenType::While => self.parse_while(),
            TokenType::Lbrace => self.parse_block(),
            _ => self.parse_expr_stmt(),
        }
    }

    /// Parses a string statement.
    fn parse_string_stmt(&mut self) -> Result<Stmt, BcError> {
        let val = self.current_token.value.clone();
        self.eat_(TokenType::String)?;
        Ok(Stmt::StringLiteral(val))
    }

    /// Parses `break`, which must be inside a loop. GNU bc reports a stray `break` on its own
    /// line, and a stray `return` on the line of the token after it.
    fn parse_break_stmt(&mut self) -> Result<Stmt, BcError> {
        if self.loop_depth == 0 {
            return self.misplaced("Break outside a for/while");
        }
        self.eat_(TokenType::Break)?;
        Ok(Stmt::Break)
    }

    /// Parses `return`, which must be inside a function.
    fn parse_return_stmt(&mut self) -> Result<Stmt, BcError> {
        let stmt = self.parse_return()?;
        if !self.in_function {
            return self.misplaced("Return outside of a function.");
        }
        Ok(stmt)
    }

    /// Parses `{ statement_list }`.
    fn parse_block(&mut self) -> Result<Stmt, BcError> {
        self.eat_(TokenType::Lbrace)?;
        let stmts = self.parse_statement_list()?;
        self.eat_(TokenType::Rbrace)?;
        Ok(Stmt::Block(stmts))
    }

    /// Parses an expression statement; a relational one is a GNU extension.
    fn parse_expr_stmt(&mut self) -> Result<Stmt, BcError> {
        let expr = self.parse_relational_expression_()?;
        if matches!(expr, Expr::RelationalOp(..)) {
            self.extension_(String::from("comparison in expression"));
        }
        Ok(Stmt::Expr(expr))
    }

    /// Parses the `for` statement.
    fn parse_for(&mut self) -> Result<Stmt, BcError> {
        self.eat_(TokenType::For)?;
        self.eat_(TokenType::Lparen)?;
        let init = self.parse_expression_()?;
        self.eat_(TokenType::Semicolon)?;
        let cond = self.parse_relational_expression_()?;
        self.eat_(TokenType::Semicolon)?;
        let post = self.parse_expression_()?;
        self.eat_(TokenType::Rparen)?;
        let body = self.parse_loop_body()?;
        Ok(Stmt::For(init, cond, post, Box::new(body)))
    }

    /// Parses the keyword `if` or `while` and the `( relational_expression )` after it.
    fn parse_cond(&mut self) -> Result<Expr, BcError> {
        self.eat_(self.current_token.token_type)?;
        self.eat_(TokenType::Lparen)?;
        let cond = self.parse_relational_expression_()?;
        self.eat_(TokenType::Rparen)?;
        Ok(cond)
    }

    /// Parses the `if` statement.
    fn parse_if(&mut self) -> Result<Stmt, BcError> {
        let cond = self.parse_cond()?;
        let body = self.parse_statement()?;
        Ok(Stmt::If(cond, Box::new(body)))
    }

    /// Parses the `while` statement.
    fn parse_while(&mut self) -> Result<Stmt, BcError> {
        let cond = self.parse_cond()?;
        let body = self.parse_loop_body()?;
        Ok(Stmt::While(cond, Box::new(body)))
    }

    /// Parses `return`, `return (e)`, or the GNU extension `return e`.
    fn parse_return(&mut self) -> Result<Stmt, BcError> {
        self.eat_(TokenType::Return)?;
        if self.current_token.token_type == TokenType::Lparen {
            self.eat_(TokenType::Lparen)?;
            // POSIX: `return ()` is `return (0)`.
            if self.current_token.token_type == TokenType::Rparen {
                self.eat_(TokenType::Rparen)?;
                return Ok(Stmt::Return(None));
            }
            let expr = self.parse_expression_()?;
            self.eat_(TokenType::Rparen)?;
            return Ok(Stmt::Return(Some(expr)));
        }
        // GNU extension: return without parentheses
        let nt = self.current_token.token_type;
        if nt != TokenType::Newline
            && nt != TokenType::Semicolon
            && nt != TokenType::Rbrace
            && nt != TokenType::Eof
        {
            let expr = self.parse_expression_()?;
            self.extension_(String::from("return expression requires parenthesis"));
            Ok(Stmt::Return(Some(expr)))
        } else {
            Ok(Stmt::Return(None))
        }
    }

    /// Parses a function definition `define f(x) { ... }`.
    fn parse_function(&mut self) -> Result<Stmt, BcError> {
        self.eat_(TokenType::Define)?;
        if self.current_token.token_type != TokenType::Letter {
            return self.error();
        }
        let name = self.current_token.text();
        self.eat_(TokenType::Letter)?;

        self.eat_(TokenType::Lparen)?;
        let params = self.parse_opt_define_list_()?;
        self.parse_function_body(name, params)
    }

    /// Parses the rest of a function definition after its parameter list.
    fn parse_function_body(&mut self, name: String, params: Vec<Param>) -> Result<Stmt, BcError> {
        self.eat_(TokenType::Rparen)?;

        self.eat_(TokenType::Lbrace)?;
        // POSIX requires a newline after `{`; GNU bc checks the name at this point too.
        if self.current_token.token_type != TokenType::Newline {
            self.extension_(String::from("End of line required"));
        }
        self.note_name_(&name);
        self.skip_newlines_()?;

        let autos = self.parse_opt_auto_define_list_()?;
        self.parse_function_stmts(name, params, autos)
    }

    /// Parses the statements of a function body, with `in_function` set and no enclosing loop.
    fn parse_function_stmts(
        &mut self,
        name: String,
        params: Vec<Param>,
        autos: Vec<Param>,
    ) -> Result<Stmt, BcError> {
        let outer = (self.loop_depth, self.in_function);
        (self.loop_depth, self.in_function) = (0, true);
        let body = self.parse_statement_list();
        (self.loop_depth, self.in_function) = outer;
        let body = body?;
        self.eat_(TokenType::Rbrace)?;

        Ok(Stmt::FunctionDef(FunctionDef {
            name,
            params,
            autos,
            body,
        }))
    }
}
