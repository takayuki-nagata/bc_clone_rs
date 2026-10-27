// SPDX-License-Identifier: MIT

//! Input decoding, unit splitting and tokens.
//!
//! - `utf8_lossy` is `String::from_utf8_lossy` (`bc_cli::decode_input`): each maximal invalid
//!   subsequence becomes U+FFFD (the `Utf8Chunks` algorithm of `core`).
//! - `split_units` is `UnitAccumulator` (`bc_core::driver`) over `split_inclusive('\n')`.
//! - `tokenize` is `parser::Lexer`, run to the end of a unit. The production lexer is
//!   incremental, but it is context-free, so scanning ahead changes nothing: the parser meets
//!   a lexical error exactly when it asks for the token at that position, here a `LexError`
//!   token that ends the sequence.
//!
//! The lexer is a state machine that consumes one byte per step, so that every recursion goes
//! through `drop_first` (see the crate documentation).

use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

exec_spec_verified! {

// ---------------------------------------------------------------------------------------------
// UTF-8 decoding
// ---------------------------------------------------------------------------------------------

/// Whether `b` is a UTF-8 continuation byte.
pub open spec fn is_cont(b: u8) -> bool {
    0x80 <= b && b <= 0xbf
}

/// Whether `b` may follow the lead byte `lead` of a 3- or 4-byte sequence (no overlong forms,
/// surrogates or code points above U+10FFFF).
pub open spec fn second_ok(lead: u8, b: u8) -> bool {
    if lead == 0xe0 {
        0xa0 <= b && b <= 0xbf
    } else if lead == 0xed {
        0x80 <= b && b <= 0x9f
    } else if lead == 0xf0 {
        0x90 <= b && b <= 0xbf
    } else if lead == 0xf4 {
        0x80 <= b && b <= 0x8f
    } else {
        is_cont(b)
    }
}

/// `String::from_utf8_lossy(s)` as bytes.
pub open spec fn utf8_lossy(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let c = s[0];
        let r1 = s.drop_first();
        if c < 0x80 {
            seq![c].add(utf8_lossy(r1))
        } else if 0xc2 <= c && c <= 0xdf {
            if s.len() >= 2 && is_cont(s[1]) {
                let r2 = r1.drop_first();
                seq![c, s[1]].add(utf8_lossy(r2))
            } else {
                seq![0xefu8, 0xbfu8, 0xbdu8].add(utf8_lossy(r1))
            }
        } else if 0xe0 <= c && c <= 0xef {
            if s.len() >= 2 && second_ok(c, s[1]) {
                let r2 = r1.drop_first();
                if s.len() >= 3 && is_cont(s[2]) {
                    let r3 = r2.drop_first();
                    seq![c, s[1], s[2]].add(utf8_lossy(r3))
                } else {
                    seq![0xefu8, 0xbfu8, 0xbdu8].add(utf8_lossy(r2))
                }
            } else {
                seq![0xefu8, 0xbfu8, 0xbdu8].add(utf8_lossy(r1))
            }
        } else if 0xf0 <= c && c <= 0xf4 {
            if s.len() >= 2 && second_ok(c, s[1]) {
                let r2 = r1.drop_first();
                if s.len() >= 3 && is_cont(s[2]) {
                    let r3 = r2.drop_first();
                    if s.len() >= 4 && is_cont(s[3]) {
                        let r4 = r3.drop_first();
                        seq![c, s[1], s[2], s[3]].add(utf8_lossy(r4))
                    } else {
                        seq![0xefu8, 0xbfu8, 0xbdu8].add(utf8_lossy(r3))
                    }
                } else {
                    seq![0xefu8, 0xbfu8, 0xbdu8].add(utf8_lossy(r2))
                }
            } else {
                seq![0xefu8, 0xbfu8, 0xbdu8].add(utf8_lossy(r1))
            }
        } else {
            seq![0xefu8, 0xbfu8, 0xbdu8].add(utf8_lossy(r1))
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Units (`UnitAccumulator`)
// ---------------------------------------------------------------------------------------------

/// A complete input unit and the line number of its first line.
pub struct Unit {
    pub text: Seq<u8>,
    pub line: u64,
}

/// State of `verified_repl_block_completeness` while it scans.
pub struct BlockScan {
    pub count: i64,
    pub in_comment: bool,
    pub in_string: bool,
}

/// `verified_repl_block_completeness`: brace depth outside comments and strings.
pub open spec fn block_scan(t: Seq<u8>, st: BlockScan) -> BlockScan
    decreases t.len()
{
    if t.len() == 0 {
        st
    } else {
        let c = t[0];
        let r1 = t.drop_first();
        if st.in_comment {
            if c == 42u8 && t.len() >= 2 && t[1] == 47u8 {
                block_scan(r1.drop_first(), BlockScan { count: st.count, in_comment: false, in_string: false })
            } else {
                block_scan(r1, st)
            }
        } else if st.in_string {
            if c == 34u8 {
                block_scan(r1, BlockScan { count: st.count, in_comment: false, in_string: false })
            } else if c == 92u8 && t.len() >= 2 && t[1] == 10u8 {
                block_scan(r1.drop_first(), st)
            } else if c == 92u8 && t.len() >= 3 && t[1] == 13u8 && t[2] == 10u8 {
                block_scan(r1.drop_first().drop_first(), st)
            } else {
                block_scan(r1, st)
            }
        } else if c == 47u8 && t.len() >= 2 && t[1] == 42u8 {
            block_scan(r1.drop_first(), BlockScan { count: st.count, in_comment: true, in_string: false })
        } else if c == 34u8 {
            block_scan(r1, BlockScan { count: st.count, in_comment: false, in_string: true })
        } else if c == 123u8 {
            let n = if st.count < 0x7fff_ffff_ffff_ffffi64 { (st.count + 1) as i64 } else { st.count };
            block_scan(r1, BlockScan { count: n, in_comment: false, in_string: false })
        } else if c == 125u8 {
            let n = if st.count > -0x7fff_ffff_ffff_ffffi64 { (st.count - 1) as i64 } else { st.count };
            block_scan(r1, BlockScan { count: n, in_comment: false, in_string: false })
        } else {
            block_scan(r1, st)
        }
    }
}

/// Whether accumulated text must wait for more lines: a trailing backslash-newline, or an open
/// brace, comment or string.
pub open spec fn unit_pending(buf: Seq<u8>) -> bool {
    let n = buf.len();
    let cont = (n >= 2 && buf[n - 1] == 10u8 && buf[n - 2] == 92u8)
        || (n >= 3 && buf[n - 1] == 10u8 && buf[n - 2] == 13u8 && buf[n - 3] == 92u8);
    let st = block_scan(buf, BlockScan { count: 0i64, in_comment: false, in_string: false });
    cont || st.count > 0 || st.in_comment || st.in_string
}

/// The next line of `t` including its newline, and the rest.
pub open spec fn take_line(t: Seq<u8>) -> (Seq<u8>, Seq<u8>)
    decreases t.len()
{
    if t.len() == 0 {
        (seq![], seq![])
    } else if t[0] == 10u8 {
        (seq![10u8], t.drop_first())
    } else {
        let r = take_line(t.drop_first());
        (seq![t[0]].add(r.0), r.1)
    }
}

/// Splits decoded input into units after the units `out`, continuing the accumulator state
/// `buf` (first line `start`) at line `next`.
pub open spec fn split_units_from(t: Seq<u8>, buf: Seq<u8>, start: u64, next: u64, out: Seq<Unit>) -> Seq<Unit>
    decreases t.len()
{
    if t.len() == 0 {
        if buf.len() == 0 { out } else { out.push(Unit { text: buf, line: start }) }
    } else {
        let lr = take_line(t);
        if lr.1.len() < t.len() {
            let start2 = if buf.len() == 0 { next } else { start };
            let b2 = buf.add(lr.0);
            let ends_nl = lr.0.len() > 0 && lr.0[lr.0.len() - 1] == 10u8;
            let next2 = if ends_nl && next < 0xffff_ffff_ffff_ffffu64 { (next + 1) as u64 } else { next };
            if unit_pending(b2) {
                split_units_from(lr.1, b2, start2, next2, out)
            } else {
                split_units_from(lr.1, seq![], start2, next2, out.push(Unit { text: b2, line: start2 }))
            }
        } else {
            out
        }
    }
}

/// The units of a decoded input, in order.
pub open spec fn split_units(t: Seq<u8>) -> Seq<Unit> {
    split_units_from(t, seq![], 1u64, 1u64, seq![])
}

// ---------------------------------------------------------------------------------------------
// Tokens (`parser::Lexer`)
// ---------------------------------------------------------------------------------------------

/// Token kinds (`parser::TokenType`), plus the lexical error that ends a token sequence.
pub enum Tok {
    Eof,
    Newline,
    Semicolon,
    Comma,
    Lparen,
    Rparen,
    Lbracket,
    Rbracket,
    Lbrace,
    Rbrace,
    Plus,
    Minus,
    Exp,
    MulOp,
    RelOp,
    IncrDecr,
    AssignOp,
    Letter,
    Number,
    Str,
    Auto,
    Break,
    Define,
    Ibase,
    If,
    For,
    Length,
    Obase,
    Quit,
    Return,
    Scale,
    Sqrt,
    While,
    /// A lexical error; `text` is the diagnostic message.
    LexError,
}

/// A token: kind, text (operator, name, digits, string contents or error message) and the
/// line where the token ends.
pub struct Token {
    pub kind: Tok,
    pub text: Seq<u8>,
    pub line: u64,
}

/// Lexer modes.
pub enum Mode {
    Normal,
    /// Skipping `skip` more bytes, then continuing in `Normal` (or `Comment` if `to_comment`).
    Skip,
    Comment,
    Str,
    Num,
    Ident,
}

pub struct LexState {
    pub mode: Mode,
    pub line: u64,
    pub skip: u8,
    pub to_comment: bool,
    pub buf: Seq<u8>,
    pub has_dot: bool,
    pub start_line: u64,
}

/// `0-9` and `A-F` (`verified_is_bc_digit`).
pub open spec fn is_bc_digit(c: u8) -> bool {
    (48 <= c && c <= 57) || (65 <= c && c <= 70)
}

/// `a-z`, `0-9` and `_` (`verified_is_ident_continue`).
pub open spec fn is_ident_continue(c: u8) -> bool {
    (97 <= c && c <= 122) || (48 <= c && c <= 57) || c == 95
}

/// The keyword kind of a name, or `Letter`.
pub open spec fn keyword(w: Seq<u8>) -> Tok {
    if w == seq![97u8, 117, 116, 111] { Tok::Auto }
    else if w == seq![98u8, 114, 101, 97, 107] { Tok::Break }
    else if w == seq![100u8, 101, 102, 105, 110, 101] { Tok::Define }
    else if w == seq![105u8, 98, 97, 115, 101] { Tok::Ibase }
    else if w == seq![105u8, 102] { Tok::If }
    else if w == seq![102u8, 111, 114] { Tok::For }
    else if w == seq![108u8, 101, 110, 103, 116, 104] { Tok::Length }
    else if w == seq![111u8, 98, 97, 115, 101] { Tok::Obase }
    else if w == seq![113u8, 117, 105, 116] { Tok::Quit }
    else if w == seq![114u8, 101, 116, 117, 114, 110] { Tok::Return }
    else if w == seq![115u8, 99, 97, 108, 101] { Tok::Scale }
    else if w == seq![115u8, 113, 114, 116] { Tok::Sqrt }
    else if w == seq![119u8, 104, 105, 108, 101] { Tok::While }
    else { Tok::Letter }
}

/// The octal escape `\ooo` of a byte.
pub open spec fn octal(b: u8) -> Seq<u8> {
    seq![92u8, (48 + b / 64) as u8, (48 + (b / 8) % 8) as u8, (48 + b % 8) as u8]
}

/// The UTF-8 length of the character whose first byte is `c` (input is valid UTF-8).
pub open spec fn char_len(c: u8) -> usize {
    if c < 0x80 { 1usize } else if c < 0xe0 { 2usize } else if c < 0xf0 { 3usize } else { 4usize }
}

/// Octal escapes of the first `n` bytes of `t`.
pub open spec fn octal_bytes(t: Seq<u8>, n: usize) -> Seq<u8>
    decreases n
{
    if n == 0 || t.len() == 0 { seq![] } else { octal(t[0]).add(octal_bytes(t.drop_first(), (n - 1) as usize)) }
}

/// `display_illegal_char` of the character at the start of `t`.
pub open spec fn display_illegal(t: Seq<u8>) -> Seq<u8> {
    let c = if t.len() > 0 { t[0] } else { 0u8 };
    if c < 0x20 {
        seq![94u8, (c + 0x40) as u8]
    } else if c == 0x7f || c >= 0x80 {
        octal_bytes(t, char_len(c))
    } else {
        seq![c]
    }
}

/// `illegal character: <c>` for the character at the start of `t`.
pub open spec fn illegal_msg(t: Seq<u8>) -> Seq<u8> {
    let prefix = seq![105u8, 108, 108, 101, 103, 97, 108, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 58, 32];
    let shown = display_illegal(t);
    prefix.add(shown)
}

/// `syntax error`.
pub open spec fn syntax_error_msg() -> Seq<u8> {
    seq![115u8, 121, 110, 116, 97, 120, 32, 101, 114, 114, 111, 114]
}

pub open spec fn tok(kind: Tok, text: Seq<u8>, line: u64) -> Token {
    Token { kind: kind, text: text, line: line }
}

pub open spec fn next_line(line: u64, c: u8) -> u64 {
    if c == 10u8 && line < 0xffff_ffff_ffff_ffffu64 { (line + 1) as u64 } else { line }
}

pub open spec fn normal(line: u64) -> LexState {
    LexState { mode: Mode::Normal, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }
}

pub open spec fn skipping(line: u64, n: u8, to_comment: bool) -> LexState {
    LexState { mode: Mode::Skip, line: line, skip: n, to_comment: to_comment, buf: seq![], has_dot: false, start_line: 0u64 }
}

pub open spec fn mode_rank(m: Mode) -> u8 {
    match m {
        Mode::Normal => 0u8,
        _ => 1u8,
    }
}

/// A one- or two-byte operator at the start of `t`, as `(kind, length)`; length 0 if none.
pub open spec fn operator(t: Seq<u8>) -> (Tok, u8) {
    let c = if t.len() > 0 { t[0] } else { 0u8 };
    let eq = t.len() >= 2 && t[1] == 61u8;
    if c == 59u8 { (Tok::Semicolon, 1u8) }
    else if c == 44u8 { (Tok::Comma, 1u8) }
    else if c == 40u8 { (Tok::Lparen, 1u8) }
    else if c == 41u8 { (Tok::Rparen, 1u8) }
    else if c == 91u8 { (Tok::Lbracket, 1u8) }
    else if c == 93u8 { (Tok::Rbracket, 1u8) }
    else if c == 123u8 { (Tok::Lbrace, 1u8) }
    else if c == 125u8 { (Tok::Rbrace, 1u8) }
    else if c == 94u8 { if eq { (Tok::AssignOp, 2u8) } else { (Tok::Exp, 1u8) } }
    else if c == 43u8 {
        if t.len() >= 2 && t[1] == 43u8 { (Tok::IncrDecr, 2u8) }
        else if eq { (Tok::AssignOp, 2u8) } else { (Tok::Plus, 1u8) }
    }
    else if c == 45u8 {
        if t.len() >= 2 && t[1] == 45u8 { (Tok::IncrDecr, 2u8) }
        else if eq { (Tok::AssignOp, 2u8) } else { (Tok::Minus, 1u8) }
    }
    else if c == 42u8 || c == 47u8 || c == 37u8 { if eq { (Tok::AssignOp, 2u8) } else { (Tok::MulOp, 1u8) } }
    else if c == 61u8 { if eq { (Tok::RelOp, 2u8) } else { (Tok::AssignOp, 1u8) } }
    else if c == 60u8 || c == 62u8 { if eq { (Tok::RelOp, 2u8) } else { (Tok::RelOp, 1u8) } }
    else if c == 33u8 { if eq { (Tok::RelOp, 2u8) } else { (Tok::Eof, 0u8) } }
    else { (Tok::Eof, 0u8) }
}

/// The token sequence of `t`, after the tokens `out` and in state `st`; it ends with `Eof` or
/// `LexError`.
pub open spec fn lex(t: Seq<u8>, st: LexState, out: Seq<Token>) -> Seq<Token>
    decreases t.len(), mode_rank(st.mode)
{
    match st.mode {
        Mode::Skip => {
            if t.len() == 0 {
                out.push(tok(Tok::Eof, seq![], st.line))
            } else {
                let line = next_line(st.line, t[0]);
                if st.skip > 1 {
                    lex(t.drop_first(), skipping(line, (st.skip - 1) as u8, st.to_comment), out)
                } else if st.to_comment {
                    lex(t.drop_first(), LexState { mode: Mode::Comment, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }, out)
                } else {
                    lex(t.drop_first(), normal(line), out)
                }
            }
        },
        Mode::Comment => {
            if t.len() == 0 {
                out.push(tok(Tok::LexError, syntax_error_msg(), st.line))
            } else if t[0] == 42u8 && t.len() >= 2 && t[1] == 47u8 {
                lex(t.drop_first(), skipping(st.line, 1u8, false), out)
            } else {
                lex(t.drop_first(), LexState { mode: Mode::Comment, line: next_line(st.line, t[0]), skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }, out)
            }
        },
        Mode::Str => {
            if t.len() == 0 {
                out.push(tok(Tok::LexError, illegal_msg(seq![34u8]), st.start_line))
            } else if t[0] == 34u8 {
                lex(t.drop_first(), normal(st.line), out.push(tok(Tok::Str, st.buf, st.line)))
            } else {
                lex(t.drop_first(), LexState { mode: Mode::Str, line: next_line(st.line, t[0]), skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: false, start_line: st.start_line }, out)
            }
        },
        Mode::Num => {
            if t.len() > 0 && is_bc_digit(t[0]) {
                lex(t.drop_first(), LexState { mode: Mode::Num, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: st.has_dot, start_line: 0u64 }, out)
            } else if t.len() > 0 && t[0] == 46u8 && !st.has_dot {
                lex(t.drop_first(), LexState { mode: Mode::Num, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: true, start_line: 0u64 }, out)
            } else if t.len() >= 2 && t[0] == 92u8 && t[1] == 10u8 {
                lex(t.drop_first().drop_first(), LexState { mode: Mode::Num, line: next_line(st.line, 10u8), skip: 0u8, to_comment: false, buf: st.buf, has_dot: st.has_dot, start_line: 0u64 }, out)
            } else if t.len() >= 3 && t[0] == 92u8 && t[1] == 13u8 && t[2] == 10u8 {
                lex(t.drop_first().drop_first().drop_first(), LexState { mode: Mode::Num, line: next_line(st.line, 10u8), skip: 0u8, to_comment: false, buf: st.buf, has_dot: st.has_dot, start_line: 0u64 }, out)
            } else {
                lex(t, normal(st.line), out.push(tok(Tok::Number, st.buf, st.line)))
            }
        },
        Mode::Ident => {
            if t.len() > 0 && is_ident_continue(t[0]) {
                lex(t.drop_first(), LexState { mode: Mode::Ident, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: false, start_line: 0u64 }, out)
            } else {
                lex(t, normal(st.line), out.push(tok(keyword(st.buf), st.buf, st.line)))
            }
        },
        Mode::Normal => {
            if t.len() == 0 {
                out.push(tok(Tok::Eof, seq![], st.line))
            } else {
                let c = t[0];
                let line = st.line;
                if c == 32u8 || c == 9u8 || c == 13u8 {
                    lex(t.drop_first(), normal(line), out)
                } else if c == 92u8 && t.len() >= 2 && t[1] == 10u8 {
                    lex(t.drop_first(), skipping(line, 1u8, false), out)
                } else if c == 92u8 && t.len() >= 3 && t[1] == 13u8 && t[2] == 10u8 {
                    lex(t.drop_first(), skipping(line, 2u8, false), out)
                } else if c == 47u8 && t.len() >= 2 && t[1] == 42u8 {
                    lex(t.drop_first(), skipping(line, 1u8, true), out)
                } else if c == 10u8 {
                    let l2 = next_line(line, c);
                    lex(t.drop_first(), normal(l2), out.push(tok(Tok::Newline, seq![10u8], l2)))
                } else if c == 34u8 {
                    lex(t.drop_first(), LexState { mode: Mode::Str, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: line }, out)
                } else if is_bc_digit(c) || (c == 46u8 && t.len() >= 2 && is_bc_digit(t[1])) {
                    lex(t.drop_first(), LexState { mode: Mode::Num, line: line, skip: 0u8, to_comment: false, buf: seq![c], has_dot: c == 46u8, start_line: 0u64 }, out)
                } else if 97 <= c && c <= 122 {
                    lex(t.drop_first(), LexState { mode: Mode::Ident, line: line, skip: 0u8, to_comment: false, buf: seq![c], has_dot: false, start_line: 0u64 }, out)
                } else {
                    let op = operator(t);
                    if op.1 == 0 {
                        out.push(tok(Tok::LexError, illegal_msg(t), line))
                    } else if op.1 == 1 {
                        lex(t.drop_first(), normal(line), out.push(tok(op.0, seq![c], line)))
                    } else {
                        lex(t.drop_first(), skipping(line, 1u8, false), out.push(tok(op.0, seq![c, t[1]], line)))
                    }
                }
            }
        },
    }
}

/// The tokens of a unit.
pub open spec fn tokenize(t: Seq<u8>) -> Seq<Token> {
    lex(t, normal(1u64), seq![])
}

} // exec_spec_verified!

} // verus!
