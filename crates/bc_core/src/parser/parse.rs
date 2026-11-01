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
use crate::refine::{r_param, r_params, text_view};
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
    ExtUse, PCfg, PR, PState, cur_tok, eat as s_eat, eat_name as s_eat_name,
    extension as s_extension, multi_letter_prefix, note_name as s_note_name, p_define_list,
    p_opt_auto, p_skip_newlines, pr_ok, pr_params, syntax_at, token_at,
};
#[cfg(not(verus_keep_ghost))]
use verus_builtin::Ghost;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// The height of an expression tree: 1 for a leaf. Statements and expressions are nested at
/// most `max_depth` levels deep, which bounds the recursion of everything that walks the tree
/// (parsing, evaluation, `Clone`, and `Drop`).
type Height = usize;

/// Diagnostic for input nested deeper than the limit (`docs/COMPATIBILITY.md` §3.2).
pub const NESTING_TOO_DEEP: &str = "nesting too deep";

/// Default nesting limit for parsing and evaluation (`docs/COMPATIBILITY.md` §2). One level
/// takes at most about 1.9 KB of stack in an x86-64 release build and 800 bytes on RV32, so the
/// default suits a stack of 256 KiB or more. Front ends set `Evaluator::max_depth` for their own
/// stack.
pub const DEFAULT_MAX_DEPTH: usize = 128;

/// Precedence info for binary and assignment operators: `(precedence, is_assignment,
/// next_min_precedence)`.
fn infix_info(token_type: TokenType) -> (i8, bool, i8) {
    let tok_kind = match token_type {
        TokenType::AssignOp => TOK_ASSIGN_OP,
        TokenType::Plus | TokenType::Minus => TOK_PLUS_MINUS,
        TokenType::MulOp => TOK_MUL_OP,
        TokenType::Exp => TOK_EXP_OP,
        _ => 0,
    };
    let (op_prec, _right_assoc, next_min_prec) = verified_pratt_infix_info(tok_kind);
    (op_prec, token_type == TokenType::AssignOp, next_min_prec)
}

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
    &&& forall|i: int| 0 <= i < toks.len() && (#[trigger] toks[i].kind is Letter) ==> all_ascii(toks[i].text)
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
    fn eat_name_(&mut self) -> Result<String, BcError> {
        self.eat_name(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
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

    /// Reports input nested deeper than `max_depth`, on the line of the last consumed token
    /// (the limit is often detected when the current token is already the next line's).
    fn too_deep<T>(&self) -> Result<T, BcError> {
        Err(BcError::Syntax {
            line: self.last_line,
            message: String::from(NESTING_TOO_DEEP),
        })
    }

    /// Enters one level of nesting. The caller decrements `depth` when it leaves the level.
    fn enter_nesting(&mut self) -> Result<(), BcError> {
        if !verified_nesting_within_limit(self.depth, 1, self.max_depth) {
            return self.too_deep();
        }
        self.depth += 1;
        Ok(())
    }

    /// Checks that a subtree of height `height` below the current level is within the limit.
    fn check_height(&self, height: Height) -> Result<Height, BcError> {
        if verified_nesting_within_limit(self.depth, height, self.max_depth) {
            Ok(height)
        } else {
            self.too_deep()
        }
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

    /// Peeks the token type of the token at `offset`.
    fn peek_token_type(&mut self, offset: usize) -> Result<TokenType, BcError> {
        self.lexer.try_peek_token(offset)
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
        let expr = self.parse_relational_expression()?;
        if matches!(expr, Expr::RelationalOp(..)) {
            self.extension_(String::from("comparison in expression"));
        }
        Ok(Stmt::Expr(expr))
    }

    /// Parses the `for` statement.
    fn parse_for(&mut self) -> Result<Stmt, BcError> {
        self.eat_(TokenType::For)?;
        self.eat_(TokenType::Lparen)?;
        let init = self.parse_expression()?;
        self.eat_(TokenType::Semicolon)?;
        let cond = self.parse_relational_expression()?;
        self.eat_(TokenType::Semicolon)?;
        let post = self.parse_expression()?;
        self.eat_(TokenType::Rparen)?;
        let body = self.parse_loop_body()?;
        Ok(Stmt::For(init, cond, post, Box::new(body)))
    }

    /// Parses the keyword `if` or `while` and the `( relational_expression )` after it.
    fn parse_cond(&mut self) -> Result<Expr, BcError> {
        self.eat_(self.current_token.token_type)?;
        self.eat_(TokenType::Lparen)?;
        let cond = self.parse_relational_expression()?;
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
            let expr = self.parse_expression()?;
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
            let expr = self.parse_expression()?;
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

    /// Parses expressions, including relational ones.
    fn parse_relational_expression(&mut self) -> Result<Expr, BcError> {
        let (left, left_h) = self.parse_expression_h()?;
        if self.current_token.token_type == TokenType::RelOp {
            let op = self.current_token.text();
            self.eat_(TokenType::RelOp)?;
            let (right, right_h) = self.parse_expression_h()?;
            self.check_height(1 + left_h.max(right_h))?;
            Ok(Expr::RelationalOp(
                RelOp::from_symbol(&op),
                Box::new(left),
                Box::new(right),
            ))
        } else {
            Ok(left)
        }
    }

    /// Parses arithmetic expressions.
    fn parse_expression(&mut self) -> Result<Expr, BcError> {
        Ok(self.parse_expression_h()?.0)
    }

    /// Parses an arithmetic expression and returns it with its height (see [`Height`]).
    fn parse_expression_h(&mut self) -> Result<(Expr, Height), BcError> {
        self.parse_expr_precedence(0)
    }

    /// Implements Precedence Climbing algorithm. Each call is one level of nesting: it is
    /// counted on entry, so deeply nested input is rejected before its tree is built, and the
    /// height of the result is checked against `max_depth` (`docs/COMPATIBILITY.md` §2).
    fn parse_expr_precedence(&mut self, min_prec: i8) -> Result<(Expr, Height), BcError> {
        self.enter_nesting()?;
        let result = self.parse_expr_precedence_inner(min_prec);
        self.depth -= 1;
        result
    }

    fn parse_expr_precedence_inner(&mut self, min_prec: i8) -> Result<(Expr, Height), BcError> {
        let (mut left, mut height) = self.parse_prefix()?;
        loop {
            let (op_prec, is_assign, next_min_prec) = infix_info(self.current_token.token_type);
            if op_prec < min_prec {
                break;
            }

            if is_assign {
                // Assignments to named expressions are parsed in `parse_primary`; anything
                // else on the left (`1 = 2`, `(a) = 2`, `a = 1 = 2`) is not assignable.
                return self.error();
            }

            let op_val = self.current_token.text();
            self.eat_(self.current_token.token_type)?;

            let (right, right_height) = self.parse_expr_precedence(next_min_prec)?;
            // A left-associative chain grows without recursion, so its height is checked here.
            height = self.check_height(1 + height.max(right_height))?;
            left = Expr::BinaryOp(BinOp::from_symbol(&op_val), Box::new(left), Box::new(right));
        }
        Ok((left, self.check_height(height)?))
    }

    /// Parses prefixes (unary operators).
    fn parse_prefix(&mut self) -> Result<(Expr, Height), BcError> {
        let t = self.current_token.token_type;
        if t == TokenType::Minus {
            self.eat_(TokenType::Minus)?;
            let (expr, h) = self.parse_expr_precedence(5)?;
            Ok((Expr::Negate(Box::new(expr)), h + 1))
        } else if t == TokenType::IncrDecr {
            let op = self.current_token.text();
            self.eat_(TokenType::IncrDecr)?;
            let (target, h) = self.parse_named_expression()?;
            Ok((
                Expr::Update(op.starts_with('+'), true, Box::new(target)),
                h + 1,
            ))
        } else {
            self.parse_primary()
        }
    }

    /// Parses `( expression )` after the keyword or name that precedes it.
    fn parse_parenthesized(&mut self) -> Result<(Expr, Height), BcError> {
        self.eat_(TokenType::Lparen)?;
        let inner = self.parse_expression_h()?;
        self.eat_(TokenType::Rparen)?;
        Ok(inner)
    }

    /// Parses a keyword followed by a parenthesized expression: `length`, `sqrt` or `scale`
    /// (`which` is 0, 1 or 2).
    fn parse_builtin(&mut self, which: u8) -> Result<(Expr, Height), BcError> {
        self.eat_(self.current_token.token_type)?;
        let (expr, h) = self.parse_parenthesized()?;
        let arg = Box::new(expr);
        let call = match which {
            0 => Expr::LengthCall(arg),
            1 => Expr::SqrtCall(arg),
            _ => Expr::ScaleCall(arg),
        };
        Ok((call, h + 1))
    }

    /// Parses primary expressions (literals, variables, built-ins, calls).
    fn parse_primary(&mut self) -> Result<(Expr, Height), BcError> {
        let t = self.current_token.token_type;
        match t {
            TokenType::Number => {
                let val = self.current_token.text();
                self.eat_(TokenType::Number)?;
                Ok((Expr::Number(val), 1))
            }
            TokenType::Lparen => {
                let (expr, h) = self.parse_parenthesized()?;
                Ok((Expr::Paren(Box::new(expr)), h + 1))
            }
            TokenType::Length => self.parse_builtin(0),
            TokenType::Sqrt => self.parse_builtin(1),
            TokenType::Scale if self.peek_token_type(0)? == TokenType::Lparen => {
                self.parse_builtin(2)
            }
            TokenType::Letter if self.peek_token_type(0)? == TokenType::Lparen => self.parse_call(),
            _ => self.parse_named_tail(),
        }
    }

    /// Parses a function call `name(args)`.
    fn parse_call(&mut self) -> Result<(Expr, Height), BcError> {
        let name = self.eat_name_()?;
        self.eat_(TokenType::Lparen)?;
        let (args, h) = self.parse_opt_argument_list()?;
        self.eat_(TokenType::Rparen)?;
        Ok((Expr::Call(name, args), h + 1))
    }

    /// Parses a named expression, then a postfix `++`/`--` or an assignment that binds to it.
    fn parse_named_tail(&mut self) -> Result<(Expr, Height), BcError> {
        let (target, target_h) = self.parse_named_expression()?;
        match self.current_token.token_type {
            TokenType::IncrDecr => {
                let op = self.current_token.text();
                self.eat_(TokenType::IncrDecr)?;
                Ok((
                    Expr::Update(op.starts_with('+'), false, Box::new(target)),
                    target_h + 1,
                ))
            }
            // As in GNU bc's grammar, an assignment operator binds to the named
            // expression right before it: `a + b = 3` is `a + (b = 3)` and `-a = 5`
            // is `-(a = 5)`. The right-hand side extends as far as possible.
            TokenType::AssignOp => {
                let op = self.current_token.text();
                self.eat_(TokenType::AssignOp)?;
                let (_, _, rhs_min_prec) = verified_pratt_infix_info(TOK_ASSIGN_OP);
                let (value, value_h) = self.parse_expr_precedence(rhs_min_prec)?;
                Ok((
                    Expr::AssignOp(
                        AssignOp::from_symbol(&op),
                        Box::new(target),
                        Box::new(value),
                    ),
                    1 + target_h.max(value_h),
                ))
            }
            _ => Ok((target, target_h)),
        }
    }

    /// Parses variables, arrays, or register accesses.
    fn parse_named_expression(&mut self) -> Result<(Expr, Height), BcError> {
        let t = self.current_token.token_type;
        match t {
            TokenType::Scale => {
                self.eat_(TokenType::Scale)?;
                Ok((Expr::RegisterAccess(Register::Scale), 1))
            }
            TokenType::Ibase => {
                self.eat_(TokenType::Ibase)?;
                Ok((Expr::RegisterAccess(Register::Ibase), 1))
            }
            TokenType::Obase => {
                self.eat_(TokenType::Obase)?;
                Ok((Expr::RegisterAccess(Register::Obase), 1))
            }
            TokenType::Letter => {
                let name = self.eat_name_()?;
                if self.current_token.token_type == TokenType::Lbracket {
                    self.parse_subscript(name)
                } else {
                    Ok((Expr::Variable(name), 1))
                }
            }
            _ => self.error(),
        }
    }

    /// Parses `[ expression ]` after the array name `name`.
    fn parse_subscript(&mut self, name: String) -> Result<(Expr, Height), BcError> {
        self.eat_(TokenType::Lbracket)?;
        let (idx, h) = self.parse_expression_h()?;
        self.eat_(TokenType::Rbracket)?;
        Ok((Expr::ArrayAccess(name, Box::new(idx)), h + 1))
    }

    /// Parses optional function call argument list.
    fn parse_opt_argument_list(&mut self) -> Result<(Vec<ExprOrArray>, Height), BcError> {
        if self.current_token.token_type == TokenType::Rparen {
            Ok((Vec::new(), 0))
        } else {
            self.parse_argument_list()
        }
    }

    /// Parses function call argument list; the height is that of the highest argument.
    fn parse_argument_list(&mut self) -> Result<(Vec<ExprOrArray>, Height), BcError> {
        let mut args = Vec::new();
        let mut height = 0;
        loop {
            if self.current_token.token_type == TokenType::Letter
                && self.peek_token_type(0)? == TokenType::Lbracket
                && self.peek_token_type(1)? == TokenType::Rbracket
            {
                let name = self.eat_name_()?;
                self.eat_(TokenType::Lbracket)?;
                self.eat_(TokenType::Rbracket)?;
                args.push(ExprOrArray::ArrayArg(name));
                height = height.max(1);
            } else {
                let (arg, h) = self.parse_expression_h()?;
                args.push(ExprOrArray::Expr(arg));
                height = height.max(h);
            }

            if self.current_token.token_type == TokenType::Comma {
                self.eat_(TokenType::Comma)?;
            } else {
                break;
            }
        }
        Ok((args, height))
    }
}
