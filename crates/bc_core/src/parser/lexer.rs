// SPDX-License-Identifier: MIT

//! The lexer: an incremental scanner over the bytes of an input unit.
//!
//! The tokens not yet returned are `Lexer::rest`: the buffer, then the specification's `lex` of
//! the text from the current position. Each function below is proved to take one token off it,
//! so the tokens returned are the specification's `tokenize` of the unit.

#[cfg(verus_keep_ghost)]
use super::all_ascii;
use super::{Token, TokenType, ascii_string};
use crate::driver::UNIT_TOO_LONG;
use crate::error::BcError;
#[cfg(verus_keep_ghost)]
use crate::refine::text_view;
use crate::verified_kernels::{
    verified_is_bc_digit, verified_is_ident_continue, verified_lexer_advance_step,
    verified_lexer_peek_char_index, verified_lexer_peek_token_index, verified_unit_within_limit,
    verified_utf8_char_len,
};
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use bc_spec::lexer::{
    LexState, Mode, Tok, Token as SToken, display_illegal as s_display_illegal, illegal_msg,
    keyword as s_keyword, lex, next_line, normal, octal, octal_bytes, operator as s_operator,
    syntax_error_msg, tok, utf8_len,
};
#[cfg(verus_keep_ghost)]
use bc_spec::lexer_lemmas::{lemma_lex_cons, lemma_octal_bytes_step};
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

broadcast use vstd::std_specs::vec::group_vec_axioms;

/// The specification's kind of a token kind.
pub open spec fn tok_of(t: TokenType) -> Tok {
    match t {
        TokenType::Eof => Tok::Eof, TokenType::Newline => Tok::Newline, TokenType::Semicolon => Tok::Semicolon,
        TokenType::Comma => Tok::Comma, TokenType::Lparen => Tok::Lparen, TokenType::Rparen => Tok::Rparen,
        TokenType::Lbracket => Tok::Lbracket, TokenType::Rbracket => Tok::Rbracket, TokenType::Lbrace => Tok::Lbrace,
        TokenType::Rbrace => Tok::Rbrace, TokenType::Plus => Tok::Plus, TokenType::Minus => Tok::Minus,
        TokenType::Exp => Tok::Exp, TokenType::MulOp => Tok::MulOp, TokenType::RelOp => Tok::RelOp,
        TokenType::IncrDecr => Tok::IncrDecr, TokenType::AssignOp => Tok::AssignOp, TokenType::Letter => Tok::Letter,
        TokenType::Number => Tok::Number, TokenType::String => Tok::Str, TokenType::Auto => Tok::Auto,
        TokenType::Break => Tok::Break, TokenType::Define => Tok::Define, TokenType::Ibase => Tok::Ibase,
        TokenType::If => Tok::If, TokenType::For => Tok::For, TokenType::Length => Tok::Length,
        TokenType::Obase => Tok::Obase, TokenType::Quit => Tok::Quit, TokenType::Return => Tok::Return,
        TokenType::Scale => Tok::Scale, TokenType::Sqrt => Tok::Sqrt, TokenType::While => Tok::While,
    }
}

/// The specification's token of a token.
pub open spec fn tok_view(t: Token) -> SToken {
    SToken { kind: tok_of(t.token_type), text: t.value@, line: t.line as u64 }
}

/// A lexical error reports the line and message of the specification's `LexError` token `x`.
pub open spec fn r_lex_err(e: BcError, x: SToken) -> bool {
    &&& x.kind is LexError
    &&& match e {
        BcError::Syntax { line, message } => line as u64 == x.line && text_view(message) == x.text,
        _ => false,
    }
}

/// `Ok(t)` is the first of the tokens `old`, and `new` is what follows it. `Eof` stays.
pub open spec fn r_next(t: Token, old: Seq<SToken>, new: Seq<SToken>) -> bool {
    &&& old.len() > 0
    &&& tok_view(t) == old[0]
    &&& !(old[0].kind is LexError)
    &&& if old[0].kind is Eof { old == seq![old[0]] && new == old } else { new == old.drop_first() }
}

/// The bytes of `syntax error`.
pub(super) fn syntax_error_text() -> (r: String)
    ensures
        text_view(r) == syntax_error_msg(),
{
    let bytes = [115u8, 121, 110, 116, 97, 120, 32, 101, 114, 114, 111, 114];
    proof { assert(bytes@ =~= syntax_error_msg()); }
    ascii_string(bytes.as_slice())
}

/// The error of a unit over the limit. Not related to the specification's tokens: `run_unit`
/// rejects such a unit before it reaches the lexer, and this keeps the public API total.
#[verifier::external_body]
fn unit_too_long() -> BcError {
    BcError::Syntax { line: 1, message: String::from(UNIT_TOO_LONG) }
}

/// Appends the octal escape of a byte.
fn push_octal(out: &mut Vec<u8>, b: u8)
    ensures
        final(out)@ == old(out)@ + octal(b),
{
    out.push(b'\\');
    out.push(48 + b / 64);
    out.push(48 + (b / 8) % 8);
    out.push(48 + b % 8);
    proof { assert(final(out)@ =~= old(out)@ + octal(b)); }
}

/// `illegal character: <c>` for the character at `text[pos]`, shown the way GNU bc does: control
/// characters as `^X`, DEL and other bytes outside ASCII as octal escapes.
fn illegal_message(text: &[u8], pos: usize) -> (r: String)
    requires
        pos < text@.len(),
        text@.len() <= 1_000_000_000,
    ensures
        text_view(r) == illegal_msg(text@.skip(pos as int)),
{
    let ghost t = text@.skip(pos as int);
    let prefix = [105u8, 108, 108, 101, 103, 97, 108, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 58, 32];
    let mut out = Vec::new();
    let mut i = 0;
    while i < 19
        invariant
            0 <= i <= 19,
            prefix@.len() == 19,
            out@ =~= prefix@.subrange(0, i as int),
        decreases 19 - i
    {
        out.push(prefix[i]);
        i += 1;
    }
    let ghost head = out@;
    proof {
        assert(head =~= seq![105u8, 108, 108, 101, 103, 97, 108, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 58, 32]);
    }
    let c = text[pos];
    proof { assert(t[0] == c); }
    if c < 0x20 {
        out.push(b'^');
        out.push(c + 0x40);
        proof { assert(out@ =~= head + s_display_illegal(t)); }
    } else if c == 0x7f || c >= 0x80 {
        let n = verified_utf8_char_len(text, pos);
        proof { assert(text@.subrange(pos as int, text@.len() as int) =~= t); }
        let mut k = 0;
        while k < n
            invariant
                k <= n,
                n == utf8_len(t),
                pos + n <= text@.len(),
                text@.len() <= 1_000_000_000,
                t == text@.skip(pos as int),
                out@ == head + octal_bytes(t, k as usize),
                head.len() == 19,
            decreases n - k
        {
            proof {
                assert(t[k as int] == text@[pos + k]);
                lemma_octal_bytes_step(t, k as usize);
                assert(head + octal_bytes(t, k as usize) + octal(t[k as int])
                    =~= head + (octal_bytes(t, k as usize) + octal(t[k as int])));
            }
            push_octal(&mut out, text[pos + k]);
            k += 1;
        }
    } else {
        out.push(c);
        proof { assert(out@ =~= head + s_display_illegal(t)); }
    }
    proof {
        lemma_ascii_message(out@, head, t);
    }
    ascii_string(out.as_slice())
}

/// Octal escapes are ASCII.
proof fn lemma_octal_bytes_ascii(t: Seq<u8>, n: usize)
    ensures
        all_ascii(octal_bytes(t, n)),
    decreases n
{
    if n > 0 && t.len() > 0 {
        lemma_octal_bytes_ascii(t.drop_first(), (n - 1) as usize);
        let a = octal(t[0]);
        let b = octal_bytes(t.drop_first(), (n - 1) as usize);
        assert forall|i: int| 0 <= i < (a + b).len() implies (a + b)[i] < 0x80 by {
            if i >= a.len() {
                assert((a + b)[i] == b[i - a.len()]);
            }
        }
    }
}

/// The message built by [`illegal_message`] is ASCII.
proof fn lemma_ascii_message(m: Seq<u8>, head: Seq<u8>, t: Seq<u8>)
    requires
        head == seq![105u8, 108, 108, 101, 103, 97, 108, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 58, 32],
        t.len() > 0,
        m == head + s_display_illegal(t),
    ensures
        all_ascii(m),
        m == illegal_msg(t),
{
    let shown = s_display_illegal(t);
    lemma_octal_bytes_ascii(t, utf8_len(t));
    assert forall|i: int| 0 <= i < m.len() implies m[i] < 0x80 by {
        if i >= 19 {
            assert(m[i] == shown[i - 19]);
        }
    }
}

/// Trusted: `to_vec` copies the slice.
#[verifier::external_body]
fn copy_bytes(text: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == text@,
{
    text.to_vec()
}

/// The operator at a byte `c` followed by `next` (0 at the end of the input), as `(kind, length)`;
/// length 0 if there is none (the specification's `operator`).
fn operator(c: u8, next: u8) -> (r: (TokenType, u8))
    ensures
        forall|t: Seq<u8>| t.len() > 0 && t[0] == c && next == (if t.len() >= 2 { t[1] } else { 0u8 })
            ==> #[trigger] s_operator(t).1 == r.1 && s_operator(t).0 == tok_of(r.0),
        r.1 <= 2,
        r.1 != 0 ==> !(r.0 is Eof),
        r.1 == 2 ==> next != 10u8 && next != 0u8,
{
    let eq = next == b'=';
    if c == b';' { (TokenType::Semicolon, 1) }
    else if c == b',' { (TokenType::Comma, 1) }
    else if c == b'(' { (TokenType::Lparen, 1) }
    else if c == b')' { (TokenType::Rparen, 1) }
    else if c == b'[' { (TokenType::Lbracket, 1) }
    else if c == b']' { (TokenType::Rbracket, 1) }
    else if c == b'{' { (TokenType::Lbrace, 1) }
    else if c == b'}' { (TokenType::Rbrace, 1) }
    else if c == b'^' { if eq { (TokenType::AssignOp, 2) } else { (TokenType::Exp, 1) } }
    else if c == b'+' {
        if next == b'+' { (TokenType::IncrDecr, 2) } else if eq { (TokenType::AssignOp, 2) } else { (TokenType::Plus, 1) }
    }
    else if c == b'-' {
        if next == b'-' { (TokenType::IncrDecr, 2) } else if eq { (TokenType::AssignOp, 2) } else { (TokenType::Minus, 1) }
    }
    else if c == b'*' || c == b'/' || c == b'%' { if eq { (TokenType::AssignOp, 2) } else { (TokenType::MulOp, 1) } }
    else if c == b'=' { if eq { (TokenType::RelOp, 2) } else { (TokenType::AssignOp, 1) } }
    else if c == b'<' || c == b'>' { if eq { (TokenType::RelOp, 2) } else { (TokenType::RelOp, 1) } }
    else if c == b'!' && eq { (TokenType::RelOp, 2) }
    else { (TokenType::Eof, 0) }
}

/// Whether `name` is the word `word`.
fn is_word(name: &[u8], word: &[u8]) -> (r: bool)
    ensures
        r == (name@ == word@),
{
    if name.len() != word.len() {
        return false;
    }
    let mut i = 0;
    while i < name.len()
        invariant
            0 <= i <= name@.len(),
            name@.len() == word@.len(),
            forall|j: int| 0 <= j < i ==> name@[j] == word@[j],
        decreases name@.len() - i
    {
        if name[i] != word[i] {
            return false;
        }
        i += 1;
    }
    proof { assert(name@ =~= word@); }
    true
}

/// The keyword kind of a name, or `Letter`.
fn keyword(name: &[u8]) -> (r: TokenType)
    ensures
        tok_of(r) == s_keyword(name@),
        !(r is Eof),
{
    if is_word(name, [97u8, 117, 116, 111].as_slice()) { TokenType::Auto }
    else if is_word(name, [98u8, 114, 101, 97, 107].as_slice()) { TokenType::Break }
    else if is_word(name, [100u8, 101, 102, 105, 110, 101].as_slice()) { TokenType::Define }
    else if is_word(name, [105u8, 98, 97, 115, 101].as_slice()) { TokenType::Ibase }
    else if is_word(name, [105u8, 102].as_slice()) { TokenType::If }
    else if is_word(name, [102u8, 111, 114].as_slice()) { TokenType::For }
    else if is_word(name, [108u8, 101, 110, 103, 116, 104].as_slice()) { TokenType::Length }
    else if is_word(name, [111u8, 98, 97, 115, 101].as_slice()) { TokenType::Obase }
    else if is_word(name, [113u8, 117, 105, 116].as_slice()) { TokenType::Quit }
    else if is_word(name, [114u8, 101, 116, 117, 114, 110].as_slice()) { TokenType::Return }
    else if is_word(name, [115u8, 99, 97, 108, 101].as_slice()) { TokenType::Scale }
    else if is_word(name, [115u8, 113, 114, 116].as_slice()) { TokenType::Sqrt }
    else if is_word(name, [119u8, 104, 105, 108, 101].as_slice()) { TokenType::While }
    else { TokenType::Letter }
}

/// An incremental lexical analyzer for the bc language.
pub struct Lexer {
    text: Vec<u8>,
    pos: usize,
    line: usize,
    buffer: Vec<Token>,
}

/// The first bytes of `t` are not whitespace, a continuation or a comment.
pub open spec fn settled(t: Seq<u8>) -> bool {
    !(t.len() > 0 && (t[0] == 32u8 || t[0] == 9u8 || t[0] == 13u8
        || (t[0] == 92u8 && t.len() >= 2 && t[1] == 10u8)
        || (t[0] == 92u8 && t.len() >= 3 && t[1] == 13u8 && t[2] == 10u8)
        || (t[0] == 47u8 && t.len() >= 2 && t[1] == 42u8)))
}

pub open spec fn comment_state(line: u64) -> LexState {
    LexState { mode: Mode::Comment, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }
}

pub open spec fn str_state(line: u64, buf: Seq<u8>, start: u64) -> LexState {
    LexState { mode: Mode::Str, line: line, skip: 0u8, to_comment: false, buf: buf, has_dot: false, start_line: start }
}

pub open spec fn num_state(line: u64, buf: Seq<u8>, has_dot: bool) -> LexState {
    LexState { mode: Mode::Num, line: line, skip: 0u8, to_comment: false, buf: buf, has_dot: has_dot, start_line: 0u64 }
}

pub open spec fn ident_state(line: u64, buf: Seq<u8>) -> LexState {
    LexState { mode: Mode::Ident, line: line, skip: 0u8, to_comment: false, buf: buf, has_dot: false, start_line: 0u64 }
}

proof fn lemma_skip_next(t: Seq<u8>, pos: int)
    requires
        0 <= pos < t.len(),
    ensures
        t.skip(pos).len() > 0,
        t.skip(pos)[0] == t[pos],
        t.skip(pos).drop_first() == t.skip(pos + 1),
{
    assert(t.skip(pos).drop_first() =~= t.skip(pos + 1));
}

/// The first token of `g`, followed by `s`.
proof fn lemma_first_token(g: Seq<SToken>, x: SToken, s: Seq<SToken>)
    requires
        g == seq![x] + s,
    ensures
        g.len() > 0,
        g[0] == x,
        g.drop_first() == s,
{
    assert(g[0] == x);
    assert(g.drop_first() =~= s);
}

impl Lexer {
    /// The bounds that the cursor kernels require.
    closed spec fn core(&self) -> bool {
        &&& self.text@.len() <= 1_000_000_000
        &&& self.pos <= self.text@.len()
        &&& self.line <= self.pos + 1
    }

    /// The text from the current position.
    closed spec fn left(&self) -> Seq<u8> {
        self.text@.skip(self.pos as int)
    }

    /// The tokens of the text from the current position.
    closed spec fn scan_rest(&self) -> Seq<SToken> {
        lex(self.left(), normal(self.line as u64), seq![])
    }

    closed spec fn buffered(&self) -> Seq<SToken> {
        self.buffer@.map_values(|t: Token| tok_view(t))
    }

    /// Whether the buffer holds the last token.
    closed spec fn at_end(&self) -> bool {
        self.buffered().len() > 0 && self.buffered().last().kind is Eof
    }

    /// The tokens not yet returned.
    pub closed spec fn rest(&self) -> Seq<SToken> {
        if self.at_end() { self.buffered() } else { self.buffered() + self.scan_rest() }
    }

    /// The length of the text, to tell whether it is within `BC_UNIT_MAX`.
    pub closed spec fn text_len(&self) -> int {
        self.text@.len() as int
    }

    pub closed spec fn inv(&self) -> bool {
        &&& self.text@.len() <= 1_000_000_000 ==> self.core()
        &&& self.buffer@.len() > 0 ==> self.text@.len() <= 1_000_000_000
        &&& forall|i: int| 0 <= i < self.buffered().len() ==> !(#[trigger] self.buffered()[i].kind is LexError)
        &&& forall|i: int| 0 <= i < self.buffered().len() - 1 ==> !(#[trigger] self.buffered()[i].kind is Eof)
        &&& self.at_end() ==> self.scan_rest() == seq![self.buffered().last()]
    }

    /// Creates a new Lexer from the source bytes. They need not be UTF-8: a string's bytes are
    /// kept unchanged, and elsewhere a byte that is not part of a token is an illegal character.
    pub fn new(text: &[u8]) -> (r: Self)
        ensures
            r.inv(),
            r.text_len() == text@.len(),
            r.rest() == bc_spec::lexer::tokenize(text@),
    {
        let r = Self { text: copy_bytes(text), pos: 0, line: 1, buffer: Vec::new() };
        proof {
            bc_spec::lexer_lemmas::lemma_tokenize(text@);
            assert(r.left() =~= text@);
            assert(r.buffered() =~= Seq::<SToken>::empty());
            assert(r.buffered() + r.scan_rest() =~= r.scan_rest());
        }
        r
    }

    /// Peeks a character ahead of the current position by the given offset; `None` past the end.
    fn peek(&self, offset: usize) -> (r: Option<u8>)
        requires
            self.core(),
            offset <= 3,
        ensures
            r == (if self.pos + offset < self.text@.len() { Some(self.text@[self.pos + offset]) } else { None }),
    {
        let (in_bounds, idx) = verified_lexer_peek_char_index(self.text.len(), self.pos, offset);
        if in_bounds {
            Some(self.text[idx])
        } else {
            None
        }
    }

    /// Like [`Self::peek`], but returns 0 past the end. Only for comparisons against non-NUL
    /// bytes: a NUL in the input is an ordinary (illegal) character, so end of input must be
    /// tested with `peek(..).is_none()`.
    fn peek_char(&self, offset: usize) -> (r: u8)
        requires
            self.core(),
            offset <= 3,
        ensures
            r == (if self.pos + offset < self.text@.len() { self.text@[self.pos + offset] } else { 0u8 }),
    {
        self.peek(offset).unwrap_or_default()
    }

    /// Advances the position by one byte, if there is one.
    fn advance(&mut self)
        requires
            old(self).core(),
        ensures
            final(self).core(),
            final(self).text == old(self).text,
            final(self).buffer == old(self).buffer,
            old(self).pos < old(self).text@.len() ==> final(self).pos == old(self).pos + 1
                && final(self).line as u64 == next_line(old(self).line as u64, old(self).text@[old(self).pos as int]),
            old(self).pos >= old(self).text@.len() ==> *final(self) == *old(self),
    {
        if self.pos < self.text.len() {
            let (next_pos, next_line) =
                verified_lexer_advance_step(self.pos, self.line, self.text[self.pos] == b'\n');
            self.pos = next_pos;
            self.line = next_line;
        }
    }

    /// Skips the rest of a comment, up to and including `*/`.
    fn skip_comment(&mut self) -> (r: Result<(), BcError>)
        requires
            old(self).core(),
        ensures
            final(self).core(),
            final(self).text == old(self).text,
            final(self).buffer == old(self).buffer,
            final(self).pos >= old(self).pos,
            ({
                let g = lex(old(self).left(), comment_state(old(self).line as u64), seq![]);
                match r {
                    Ok(_) => final(self).scan_rest() == g,
                    Err(e) => g.len() == 1 && r_lex_err(e, g[0]),
                }
            }),
    {
        let ghost goal = lex(self.left(), comment_state(self.line as u64), seq![]);
        loop
            invariant
                self.core(),
                self.text == old(self).text,
                self.buffer == old(self).buffer,
                lex(self.left(), comment_state(self.line as u64), seq![]) == goal,
                goal == lex(old(self).left(), comment_state(old(self).line as u64), seq![]),
                self.pos >= old(self).pos,
            decreases self.text@.len() - self.pos
        {
            let ghost t = self.left();
            match self.peek(0) {
                None => {
                    proof {
                        assert(t.len() == 0);
                        reveal_with_fuel(lex, 2);
                        assert(goal == seq![tok(Tok::LexError, syntax_error_msg(), self.line as u64)]);
                    }
                    return Err(BcError::Syntax { line: self.line, message: syntax_error_text() });
                },
                Some(cc) => {
                    proof { lemma_skip_next(self.text@, self.pos as int); }
                    if cc == b'*' && self.peek_char(1) == b'/' {
                        proof {
                            lemma_skip_next(self.text@, self.pos + 1);
                            reveal_with_fuel(lex, 3);
                            assert(t[1] == 47u8);
                            assert(goal == lex(t.drop_first().drop_first(), normal(self.line as u64), seq![]));
                        }
                        self.advance();
                        self.advance();
                        return Ok(());
                    }
                    proof {
                        reveal_with_fuel(lex, 2);
                        assert(!(t[0] == 42u8 && t.len() >= 2 && t[1] == 47u8));
                    }
                    self.advance();
                },
            }
        }
    }

    /// Skips whitespace, comments (`/* ... */`), and backslash-newlines.
    fn skip_whitespace_and_comments(&mut self) -> (r: Result<(), BcError>)
        requires
            old(self).core(),
        ensures
            final(self).core(),
            final(self).text == old(self).text,
            final(self).buffer == old(self).buffer,
            match r {
                Ok(_) => final(self).scan_rest() == old(self).scan_rest() && settled(final(self).left()),
                Err(e) => old(self).scan_rest().len() == 1 && r_lex_err(e, old(self).scan_rest()[0]),
            },
    {
        let ghost goal = self.scan_rest();
        loop
            invariant
                self.core(),
                self.text == old(self).text,
                self.buffer == old(self).buffer,
                self.scan_rest() == goal,
                goal == old(self).scan_rest(),
            decreases self.text@.len() - self.pos
        {
            let c = self.peek_char(0);
            let c1 = self.peek_char(1);
            let c2 = self.peek_char(2);
            let ghost t = self.left();
            let ghost (p, line) = (self.pos as int, self.line as u64);
            if self.pos >= self.text.len() {
                proof { assert(t.len() == 0); }
                return Ok(());
            }
            proof {
                lemma_skip_next(self.text@, p);
                assert(t[0] == c);
                if t.len() >= 2 { assert(t[1] == c1); }
                if t.len() >= 3 { assert(t[2] == c2); }
            }
            if c == b' ' || c == b'\t' || c == b'\r' {
                proof { reveal_with_fuel(lex, 2); }
                self.advance();
            } else if c == b'\\' && c1 == b'\n' {
                proof {
                    lemma_skip_next(self.text@, p + 1);
                    reveal_with_fuel(lex, 3);
                }
                self.advance();
                self.advance();
                proof { assert(self.scan_rest() == goal); }
            } else if c == b'\\' && c1 == b'\r' && c2 == b'\n' {
                proof {
                    lemma_skip_next(self.text@, p + 1);
                    lemma_skip_next(self.text@, p + 2);
                    reveal_with_fuel(lex, 4);
                }
                self.advance();
                self.advance();
                self.advance();
                proof { assert(self.scan_rest() == goal); }
            } else if c == b'/' && c1 == b'*' {
                proof {
                    lemma_skip_next(self.text@, p + 1);
                    reveal_with_fuel(lex, 3);
                }
                self.advance();
                self.advance();
                proof { assert(goal == lex(self.left(), comment_state(self.line as u64), seq![])); }
                match self.skip_comment() {
                    Ok(()) => {},
                    Err(e) => return Err(e),
                }
            } else {
                return Ok(());
            }
        }
    }

    /// Scans a string, whose opening quote is the current byte. An unterminated string is
    /// reported at the line where it starts, as in GNU bc.
    fn scan_string(&mut self) -> (r: Result<Token, BcError>)
        requires
            old(self).core(),
            old(self).pos < old(self).text@.len(),
            old(self).text@[old(self).pos as int] == 34u8,
        ensures
            final(self).core(),
            final(self).text == old(self).text,
            final(self).buffer == old(self).buffer,
            match r {
                Ok(t) => t.token_type is String && old(self).scan_rest() == seq![tok_view(t)] + final(self).scan_rest(),
                Err(e) => old(self).scan_rest().len() == 1 && r_lex_err(e, old(self).scan_rest()[0]),
            },
    {
        let ghost goal = self.scan_rest();
        let start_line = self.line;
        proof {
            lemma_skip_next(self.text@, self.pos as int);
            reveal_with_fuel(lex, 2);
        }
        self.advance();
        let mut bytes = Vec::new();
        proof { assert(goal == lex(self.left(), str_state(self.line as u64, bytes@, start_line as u64), seq![])); }
        loop
            invariant
                self.core(),
                self.text == old(self).text,
                self.buffer == old(self).buffer,
                start_line <= self.pos + 1,
                goal == old(self).scan_rest(),
                goal == lex(self.left(), str_state(self.line as u64, bytes@, start_line as u64), seq![]),
            decreases self.text@.len() - self.pos
        {
            let ghost t = self.left();
            match self.peek(0) {
                None => {
                    proof {
                        assert(t.len() == 0);
                        reveal_with_fuel(lex, 2);
                    }
                    self.line = start_line;
                    let quote = [34u8];
                    proof { assert(quote@.skip(0) =~= seq![34u8]); }
                    let message = illegal_message(quote.as_slice(), 0);
                    return Err(BcError::Syntax { line: start_line, message });
                },
                Some(c) => {
                    proof {
                        lemma_skip_next(self.text@, self.pos as int);
                        reveal_with_fuel(lex, 2);
                    }
                    self.advance();
                    if c == b'"' {
                        let tok = Token { token_type: TokenType::String, value: bytes, line: self.line };
                        proof {
                            assert(goal == lex(self.left(), normal(self.line as u64), seq![].push(tok_view(tok))));
                            lemma_lex_cons(self.left(), normal(self.line as u64), tok_view(tok));
                        }
                        return Ok(tok);
                    }
                    bytes.push(c);
                },
            }
        }
    }

    /// Scans a number: digits with at most one point, and backslash-newlines that join its parts.
    fn scan_number(&mut self) -> (r: Token)
        requires
            old(self).core(),
        ensures
            final(self).core(),
            final(self).text == old(self).text,
            final(self).buffer == old(self).buffer,
            r.token_type is Number,
            lex(old(self).left(), num_state(old(self).line as u64, seq![], false), seq![])
                == seq![tok_view(r)] + final(self).scan_rest(),
    {
        let ghost goal = lex(self.left(), num_state(self.line as u64, seq![], false), seq![]);
        let mut digits = Vec::new();
        let mut has_dot = false;
        proof { assert(digits@ =~= Seq::<u8>::empty()); }
        loop
            invariant
                self.core(),
                self.text == old(self).text,
                self.buffer == old(self).buffer,
                goal == lex(self.left(), num_state(self.line as u64, digits@, has_dot), seq![]),
                goal == lex(old(self).left(), num_state(old(self).line as u64, seq![], false), seq![]),
            decreases self.text@.len() - self.pos
        {
            let c = self.peek_char(0);
            let c1 = self.peek_char(1);
            let c2 = self.peek_char(2);
            let ghost t = self.left();
            let ghost p = self.pos as int;
            proof {
                if self.pos < self.text@.len() {
                    lemma_skip_next(self.text@, p);
                    assert(t[0] == c);
                    if t.len() >= 2 { assert(t[1] == c1); }
                    if t.len() >= 3 { assert(t[2] == c2); }
                } else {
                    assert(t.len() == 0);
                }
                reveal_with_fuel(lex, 2);
            }
            if verified_is_bc_digit(c as u32) {
                digits.push(c);
                self.advance();
            } else if c == b'.' && !has_dot {
                has_dot = true;
                digits.push(c);
                self.advance();
            } else if c == b'\\' && c1 == b'\n' {
                proof {
                    lemma_skip_next(self.text@, p + 1);
                    assert(t.drop_first().drop_first() == self.text@.skip(p + 2));
                }
                self.advance();
                self.advance();
            } else if c == b'\\' && c1 == b'\r' && c2 == b'\n' {
                proof {
                    lemma_skip_next(self.text@, p + 1);
                    lemma_skip_next(self.text@, p + 2);
                }
                self.advance();
                self.advance();
                self.advance();
            } else {
                let x = Token { token_type: TokenType::Number, value: digits, line: self.line };
                proof {
                    assert(tok_view(x) == tok(Tok::Number, digits@, self.line as u64));
                    assert(goal == lex(t, normal(self.line as u64), seq![].push(tok_view(x))));
                    lemma_lex_cons(t, normal(self.line as u64), tok_view(x));
                }
                return x;
            }
        }
    }

    /// Scans a name or keyword, whose first letter `first` is the current byte.
    fn scan_name(&mut self, first: u8) -> (r: Token)
        requires
            old(self).core(),
            old(self).pos < old(self).text@.len(),
            old(self).text@[old(self).pos as int] == first,
            97 <= first <= 122,
        ensures
            final(self).core(),
            final(self).text == old(self).text,
            final(self).buffer == old(self).buffer,
            !(r.token_type is Eof),
            lex(old(self).left().drop_first(), ident_state(old(self).line as u64, seq![first]), seq![])
                == seq![tok_view(r)] + final(self).scan_rest(),
    {
        let ghost goal = lex(self.left().drop_first(), ident_state(self.line as u64, seq![first]), seq![]);
        proof { lemma_skip_next(self.text@, self.pos as int); }
        let mut letters = Vec::new();
        letters.push(first);
        self.advance();
        proof { assert(letters@ =~= seq![first]); }
        loop
            invariant
                self.core(),
                self.text == old(self).text,
                self.buffer == old(self).buffer,
                goal == lex(self.left(), ident_state(self.line as u64, letters@), seq![]),
                goal == lex(old(self).left().drop_first(), ident_state(old(self).line as u64, seq![first]), seq![]),
            decreases self.text@.len() - self.pos
        {
            let c = self.peek_char(0);
            let ghost t = self.left();
            proof {
                if self.pos < self.text@.len() {
                    lemma_skip_next(self.text@, self.pos as int);
                    assert(t[0] == c);
                } else {
                    assert(t.len() == 0);
                }
                reveal_with_fuel(lex, 2);
            }
            if !verified_is_ident_continue(c as u32) {
                let token_type = keyword(letters.as_slice());
                let ghost name = letters@;
                let x = Token { token_type, value: letters, line: self.line };
                proof {
                    assert(tok_view(x) == tok(s_keyword(name), name, self.line as u64));
                    assert(goal == lex(t, normal(self.line as u64), seq![].push(tok_view(x))));
                    lemma_lex_cons(t, normal(self.line as u64), tok_view(x));
                }
                return x;
            }
            letters.push(c);
            self.advance();
        }
    }

    /// Scans an operator, the only token that can start with the current byte `c`, followed by
    /// `next`; any other byte is an illegal character.
    fn scan_operator(&mut self, c: u8, next: u8) -> (r: Result<Token, BcError>)
        requires
            old(self).core(),
            old(self).pos < old(self).text@.len(),
            settled(old(self).left()),
            old(self).left()[0] == c,
            next == (if old(self).left().len() >= 2 { old(self).left()[1] } else { 0u8 }),
            c != 10u8,
            c != 34u8,
            !bc_spec::lexer::is_bc_digit(c),
            !(c == 46u8 && bc_spec::lexer::is_bc_digit(next)),
            !(97 <= c && c <= 122),
        ensures
            final(self).core(),
            final(self).text == old(self).text,
            final(self).buffer == old(self).buffer,
            match r {
                Ok(t) => r_next(t, old(self).scan_rest(), final(self).scan_rest()),
                Err(e) => old(self).scan_rest().len() == 1 && r_lex_err(e, old(self).scan_rest()[0]),
            },
    {
        let ghost goal = self.scan_rest();
        let ghost t = self.left();
        let ghost line = self.line as u64;
        proof { lemma_skip_next(self.text@, self.pos as int); }
        let (token_type, len) = operator(c, next);
        proof { assert(s_operator(t).1 == len && s_operator(t).0 == tok_of(token_type)); }
        if len == 0 {
            let message = illegal_message(self.text.as_slice(), self.pos);
            let e = BcError::Syntax { line: self.line, message };
            proof { assert(goal == seq![tok(Tok::LexError, illegal_msg(t), line)]); }
            return Err(e);
        }
        let mut value = Vec::new();
        value.push(c);
        if len == 2 {
            value.push(next);
            proof { lemma_skip_next(self.text@, self.pos + 1); }
            self.advance();
        }
        self.advance();
        let x = Token { token_type, value, line: self.line };
        proof {
            assert(self.line as u64 == line);
            let v = tok_view(x);
            if len == 1 {
                assert(value@ =~= seq![c]);
                assert(goal == lex(self.left(), normal(line), seq![].push(v)));
            } else {
                assert(value@ =~= seq![c, t[1]]);
                reveal_with_fuel(lex, 2);
                assert(goal == lex(t.drop_first(), bc_spec::lexer::skipping(line, 1u8, false), seq![].push(v)));
                assert(goal == lex(self.left(), normal(line), seq![].push(v)));
            }
            lemma_lex_cons(self.left(), normal(line), v);
        }
        Ok(x)
    }

    /// Scans the next token from input.
    #[allow(clippy::manual_range_contains, reason = "the proof reasons about the two comparisons directly")]
    fn scan_token(&mut self) -> (r: Result<Token, BcError>)
        requires
            old(self).text@.len() <= 1_000_000_000 ==> old(self).core(),
        ensures
            final(self).text == old(self).text,
            final(self).buffer == old(self).buffer,
            old(self).text@.len() > 1_000_000_000 ==> r is Err,
            old(self).text@.len() <= 1_000_000_000 ==> final(self).core() && match r {
                Ok(t) => r_next(t, old(self).scan_rest(), final(self).scan_rest()),
                Err(e) => old(self).scan_rest().len() == 1 && r_lex_err(e, old(self).scan_rest()[0]),
            },
    {
        if !verified_unit_within_limit(self.text.len()) {
            return Err(unit_too_long());
        }
        match self.skip_whitespace_and_comments() {
            Ok(()) => {},
            Err(e) => return Err(e),
        }
        let ghost goal = self.scan_rest();
        let ghost t = self.left();
        let ghost line = self.line as u64;
        let c = match self.peek(0) {
            Some(c) => c,
            None => {
                let tok = Token { token_type: TokenType::Eof, value: Vec::new(), line: self.line };
                proof {
                    assert(t.len() == 0);
                    reveal_with_fuel(lex, 2);
                    assert(tok_view(tok) == goal[0]);
                    assert(goal == seq![goal[0]]);
                }
                return Ok(tok);
            },
        };
        let next = self.peek_char(1);
        proof {
            lemma_skip_next(self.text@, self.pos as int);
            assert(t[0] == c);
            if t.len() >= 2 { assert(t[1] == next); }
        }
        if c == b'\n' {
            let value = alloc::vec![c];
            self.advance();
            let tok = Token { token_type: TokenType::Newline, value, line: self.line };
            proof {
                assert(value@ =~= seq![10u8]);
                assert(goal == lex(self.left(), normal(self.line as u64), seq![].push(tok_view(tok))));
                lemma_lex_cons(self.left(), normal(self.line as u64), tok_view(tok));
            }
            return Ok(tok);
        }
        if c == b'"' {
            let r = self.scan_string();
            proof {
                if r is Ok {
                    lemma_first_token(goal, tok_view(r->Ok_0), self.scan_rest());
                }
            }
            return r;
        }
        if verified_is_bc_digit(c as u32) || (c == b'.' && verified_is_bc_digit(next as u32)) {
            proof {
                reveal_with_fuel(lex, 2);
                assert(goal == lex(t, num_state(line, seq![], false), seq![]));
            }
            let x = self.scan_number();
            proof { lemma_first_token(goal, tok_view(x), self.scan_rest()); }
            return Ok(x);
        }
        if 97 <= c && c <= 122 {
            proof { assert(goal == lex(t.drop_first(), ident_state(line, seq![c]), seq![])); }
            let x = self.scan_name(c);
            proof { lemma_first_token(goal, tok_view(x), self.scan_rest()); }
            return Ok(x);
        }
        self.scan_operator(c, next)
    }

    /// Appending the token scanned next to the buffer leaves `rest` as it was.
    proof fn lemma_push_token(a: Self, s: Self, b: Self, x: Token)
        requires
            a.inv(),
            !a.at_end(),
            a.text@.len() <= 1_000_000_000,
            s.text == a.text,
            s.buffer == a.buffer,
            s.core(),
            r_next(x, a.scan_rest(), s.scan_rest()),
            b.text == s.text,
            b.pos == s.pos,
            b.line == s.line,
            b.buffer@ == s.buffer@.push(x),
        ensures
            b.inv(),
            b.rest() == a.rest(),
            b.text_len() == a.text_len(),
            b.at_end() == (x.token_type is Eof),
            b.buffer@.len() == b.buffered().len(),
    {
        let av = a.buffered();
        let sr = a.scan_rest();
        let v = tok_view(x);
        assert(b.buffered() =~= av.push(v));
        assert(b.buffered().last() == v);
        assert(b.scan_rest() == s.scan_rest());
        if x.token_type is Eof {
            assert(av + sr =~= av.push(v));
        } else {
            assert(av.push(v) + b.scan_rest() =~= av + sr);
        }
        assert forall|i: int| 0 <= i < b.buffered().len() - 1 implies !(#[trigger] b.buffered()[i].kind is Eof) by {
            if i < av.len() - 1 { assert(b.buffered()[i] == av[i]); }
            else { assert(b.buffered()[i] == av.last()); }
        }
        assert forall|i: int| 0 <= i < b.buffered().len() implies !(#[trigger] b.buffered()[i].kind is LexError) by {
            if i < av.len() { assert(b.buffered()[i] == av[i]); }
        }
    }

    /// Obtains the next token, returning Err on lexical error.
    pub fn try_get_next_token(&mut self) -> (r: Result<Token, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).text_len() == old(self).text_len(),
            old(self).text_len() > 1_000_000_000 ==> r is Err,
            old(self).text_len() <= 1_000_000_000 ==> match r {
                Ok(t) => final(self).inv() && r_next(t, old(self).rest(), final(self).rest()),
                Err(e) => old(self).rest().len() == 1 && r_lex_err(e, old(self).rest()[0]),
            },
    {
        if !self.buffer.is_empty() {
            let ghost b = self.buffered();
            let ghost sr = self.scan_rest();
            let tok = self.buffer.remove(0);
            proof {
                assert(self.buffered() =~= b.drop_first());
                assert(b[0] == tok_view(tok));
                if !(b.last().kind is Eof) {
                    assert((b + sr).drop_first() =~= b.drop_first() + sr);
                    if self.buffered().len() > 0 {
                        assert(self.buffered().last() == b.last());
                    }
                    assert(self.rest() =~= (b + sr).drop_first());
                    assert((b + sr)[0] == b[0]);
                } else {
                    if b.len() > 1 {
                        assert(b[0] != b.last() || true);
                        assert(self.buffered().last() == b.last());
                    } else {
                        assert(self.buffered() =~= Seq::<SToken>::empty());
                        assert(self.buffered() + sr =~= sr);
                        assert(b =~= seq![b[0]]);
                    }
                }
            }
            Ok(tok)
        } else {
            proof {
                assert(self.buffered() =~= Seq::<SToken>::empty());
                assert(self.buffered() + self.scan_rest() =~= self.scan_rest());
            }
            let r = self.scan_token();
            proof {
                assert(self.buffered() =~= Seq::<SToken>::empty());
                assert(self.buffered() + self.scan_rest() =~= self.scan_rest());
            }
            r
        }
    }

    /// The kind of the token at a given offset forward, or Err on lexical error.
    pub fn try_peek_token(&mut self, offset: usize) -> (r: Result<TokenType, BcError>)
        requires
            old(self).inv(),
            offset < 8,
        ensures
            final(self).text_len() == old(self).text_len(),
            old(self).text_len() > 1_000_000_000 ==> r is Err,
            old(self).text_len() <= 1_000_000_000 ==> old(self).rest().len() > 0 && match r {
                Ok(k) => final(self).inv() && final(self).rest() == old(self).rest()
                    && tok_of(k) == bc_spec::parser::token_at(old(self).rest(), offset).kind,
                Err(e) => old(self).rest().len() - 1 <= offset
                    && r_lex_err(e, old(self).rest().last()),
            },
    {
        let ghost whole = self.rest();
        let mut at_end = false;
        if !self.buffer.is_empty() {
            at_end = matches!(self.buffer[self.buffer.len() - 1].token_type, TokenType::Eof);
            proof {
                let b = self.buffered();
                assert(b.last() == tok_view(self.buffer@[self.buffer@.len() - 1]));
            }
        }
        proof {
            if self.buffer@.len() == 0 {
                assert(self.buffered() =~= Seq::<SToken>::empty());
            }
        }
        while !at_end && self.buffer.len() <= offset
            invariant
                self.inv(),
                self.text_len() == old(self).text_len(),
                self.rest() == whole,
                whole == old(self).rest(),
                at_end == self.at_end(),
                offset < 8,
                self.buffer@.len() == self.buffered().len(),
            decreases offset + 1 - self.buffer@.len()
        {
            let ghost before = *self;
            let x = self.scan_token()?;
            let ghost scanned = *self;
            let is_eof = matches!(x.token_type, TokenType::Eof);
            self.buffer.push(x);
            proof { Self::lemma_push_token(before, scanned, *self, x); }
            at_end = is_eof;
        }
        let idx = verified_lexer_peek_token_index(self.buffer.len(), offset);
        let k = self.buffer[idx].token_type;
        proof {
            let b = self.buffered();
            assert(b[idx as int] == tok_view(self.buffer@[idx as int]));
            if !at_end { assert((b + self.scan_rest())[offset as int] == b[offset as int]); }
        }
        Ok(k)
    }
}

} // verus!

impl Lexer {
    /// Advances the position by `steps` bytes.
    #[cfg(test)]
    pub(super) fn advance_char(&mut self, steps: usize) {
        for _ in 0..steps {
            self.advance();
        }
    }

    /// Obtains the next token, consuming it from the buffer or stream.
    #[cfg(test)]
    pub fn get_next_token(&mut self) -> Token {
        self.try_get_next_token()
            .unwrap_or_else(|e| panic!("{:?}", e))
    }
}
