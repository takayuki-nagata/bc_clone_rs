// SPDX-License-Identifier: MIT

//! Facts about the specification's `lex` that the proof of the production lexer uses.

use crate::lexer::*;
use vstd::prelude::*;

verus! {

/// The tokens found so far are a prefix: `lex` only appends to `out`.
pub proof fn lemma_lex_out(t: Seq<u8>, st: LexState, out: Seq<Token>)
    ensures
        lex(t, st, out) == out + lex(t, st, seq![]),
    decreases t.len(), mode_rank(st.mode), 0int
{
    let e = Seq::<Token>::empty();
    assert(seq![] == e);
    // Every step of `lex` continues with the same `t2` and `st2` from `out` and from the empty
    // sequence, after appending the same token, if any.
    assert(forall|x: Token| #![auto] (out.push(x) + lex(t, st, e)) == out + (e.push(x) + lex(t, st, e))) by {
        assert forall|x: Token| #![auto] (out.push(x) + lex(t, st, e)) =~= out + (e.push(x) + lex(t, st, e)) by {}
    }
    match st.mode {
        Mode::Skip => {
            if t.len() == 0 {
                assert(out.push(tok(Tok::Eof, seq![], st.line)) =~= out + e.push(tok(Tok::Eof, seq![], st.line)));
            } else {
                let line = next_line(st.line, t[0]);
                let st2 = if st.skip > 1 {
                    skipping(line, (st.skip - 1) as u8, st.to_comment)
                } else if st.to_comment {
                    LexState { mode: Mode::Comment, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }
                } else {
                    normal(line)
                };
                lemma_lex_out(t.drop_first(), st2, out);
            }
        },
        Mode::Comment => {
            if t.len() == 0 {
                assert(out.push(tok(Tok::LexError, syntax_error_msg(), st.line)) =~= out + e.push(tok(Tok::LexError, syntax_error_msg(), st.line)));
            } else if t[0] == 42u8 && t.len() >= 2 && t[1] == 47u8 {
                lemma_lex_out(t.drop_first(), skipping(st.line, 1u8, false), out);
            } else {
                lemma_lex_out(t.drop_first(), LexState { mode: Mode::Comment, line: next_line(st.line, t[0]), skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }, out);
            }
        },
        Mode::Str => {
            if t.len() == 0 {
                let x = tok(Tok::LexError, illegal_msg(seq![34u8]), st.start_line);
                assert(out.push(x) =~= out + e.push(x));
            } else if t[0] == 34u8 {
                lemma_lex_push(t.drop_first(), normal(st.line), out, tok(Tok::Str, st.buf, st.line));
            } else {
                lemma_lex_out(t.drop_first(), LexState { mode: Mode::Str, line: next_line(st.line, t[0]), skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: false, start_line: st.start_line }, out);
            }
        },
        Mode::Num => {
            if t.len() > 0 && is_bc_digit(t[0]) {
                lemma_lex_out(t.drop_first(), LexState { mode: Mode::Num, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: st.has_dot, start_line: 0u64 }, out);
            } else if t.len() > 0 && t[0] == 46u8 && !st.has_dot {
                lemma_lex_out(t.drop_first(), LexState { mode: Mode::Num, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: true, start_line: 0u64 }, out);
            } else if t.len() >= 2 && t[0] == 92u8 && t[1] == 10u8 {
                lemma_lex_out(t.drop_first().drop_first(), LexState { mode: Mode::Num, line: next_line(st.line, 10u8), skip: 0u8, to_comment: false, buf: st.buf, has_dot: st.has_dot, start_line: 0u64 }, out);
            } else if t.len() >= 3 && t[0] == 92u8 && t[1] == 13u8 && t[2] == 10u8 {
                lemma_lex_out(t.drop_first().drop_first().drop_first(), LexState { mode: Mode::Num, line: next_line(st.line, 10u8), skip: 0u8, to_comment: false, buf: st.buf, has_dot: st.has_dot, start_line: 0u64 }, out);
            } else {
                lemma_lex_push(t, normal(st.line), out, tok(Tok::Number, st.buf, st.line));
            }
        },
        Mode::Ident => {
            if t.len() > 0 && is_ident_continue(t[0]) {
                lemma_lex_out(t.drop_first(), LexState { mode: Mode::Ident, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: false, start_line: 0u64 }, out);
            } else {
                lemma_lex_push(t, normal(st.line), out, tok(keyword(st.buf), st.buf, st.line));
            }
        },
        Mode::Normal => {
            if t.len() == 0 {
                assert(out.push(tok(Tok::Eof, seq![], st.line)) =~= out + e.push(tok(Tok::Eof, seq![], st.line)));
            } else {
                let c = t[0];
                let line = st.line;
                let r = t.drop_first();
                if c == 32u8 || c == 9u8 || c == 13u8 {
                    lemma_lex_out(r, normal(line), out);
                } else if c == 92u8 && t.len() >= 2 && t[1] == 10u8 {
                    lemma_lex_out(r, skipping(line, 1u8, false), out);
                } else if c == 92u8 && t.len() >= 3 && t[1] == 13u8 && t[2] == 10u8 {
                    lemma_lex_out(r, skipping(line, 2u8, false), out);
                } else if c == 47u8 && t.len() >= 2 && t[1] == 42u8 {
                    lemma_lex_out(r, skipping(line, 1u8, true), out);
                } else if c == 10u8 {
                    let l2 = next_line(line, c);
                    lemma_lex_push(r, normal(l2), out, tok(Tok::Newline, seq![10u8], l2));
                } else if c == 34u8 {
                    lemma_lex_out(r, LexState { mode: Mode::Str, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: line }, out);
                } else if is_bc_digit(c) || (c == 46u8 && t.len() >= 2 && is_bc_digit(t[1])) {
                    lemma_lex_out(r, LexState { mode: Mode::Num, line: line, skip: 0u8, to_comment: false, buf: seq![c], has_dot: c == 46u8, start_line: 0u64 }, out);
                } else if 97 <= c && c <= 122 {
                    lemma_lex_out(r, LexState { mode: Mode::Ident, line: line, skip: 0u8, to_comment: false, buf: seq![c], has_dot: false, start_line: 0u64 }, out);
                } else {
                    let op = operator(t);
                    if op.1 == 0 {
                        let x = tok(Tok::LexError, illegal_msg(t), line);
                        assert(out.push(x) =~= out + e.push(x));
                    } else if op.1 == 1 {
                        lemma_lex_push(r, normal(line), out, tok(op.0, seq![c], line));
                    } else {
                        lemma_lex_push(r, skipping(line, 1u8, false), out, tok(op.0, seq![c, t[1]], line));
                    }
                }
            }
        },
    }
}

/// The step of [`lemma_lex_out`] that appends the token `x`. `Num` and `Ident` append without
/// consuming, which the second measure of `lex` allows.
proof fn lemma_lex_push(t: Seq<u8>, st: LexState, out: Seq<Token>, x: Token)
    requires
        st.mode is Normal || st.mode is Skip,
    ensures
        lex(t, st, out.push(x)) == out + lex(t, st, seq![x]),
    decreases t.len(), mode_rank(st.mode), 1int
{
    lemma_lex_out(t, st, out.push(x));
    lemma_lex_out(t, st, seq![x]);
    assert(out.push(x) + lex(t, st, seq![]) =~= out + (seq![x] + lex(t, st, seq![])));
}

/// `lex` after the single token `x`.
pub proof fn lemma_lex_cons(t: Seq<u8>, st: LexState, x: Token)
    ensures
        lex(t, st, seq![].push(x)) == seq![x] + lex(t, st, seq![]),
        lex(t, st, seq![].push(x)).len() > 0,
        lex(t, st, seq![].push(x))[0] == x,
        lex(t, st, seq![].push(x)).drop_first() == lex(t, st, seq![]),
{
    lemma_lex_out(t, st, seq![x]);
    assert(seq![].push(x) =~= seq![x]);
    let r = lex(t, st, seq![]);
    assert((seq![x] + r).drop_first() =~= r);
}

/// The octal escapes of one more byte.
pub proof fn lemma_octal_bytes_step(t: Seq<u8>, k: usize)
    requires
        k < t.len(),
        k < usize::MAX,
    ensures
        octal_bytes(t, (k + 1) as usize) == octal_bytes(t, k) + octal(t[k as int]),
    decreases k
{
    if k == 0 {
        assert(octal_bytes(t.drop_first(), 0usize) == Seq::<u8>::empty());
        assert(octal(t[0]) + Seq::<u8>::empty() =~= octal(t[0]));
        assert(Seq::<u8>::empty() + octal(t[0]) =~= octal(t[0]));
    } else {
        let r = t.drop_first();
        lemma_octal_bytes_step(r, (k - 1) as usize);
        assert(r[k - 1] == t[k as int]);
        assert(octal(t[0]) + (octal_bytes(r, (k - 1) as usize) + octal(t[k as int]))
            =~= (octal(t[0]) + octal_bytes(r, (k - 1) as usize)) + octal(t[k as int]));
    }
}

/// How much a pending `Num` or `Ident` token adds to the count of tokens.
pub open spec fn lex_pending(st: LexState) -> int {
    if st.mode is Num || st.mode is Ident { 1 } else { 0 }
}

/// At most one token per byte, plus the last one and a pending one.
pub proof fn lemma_lex_len(t: Seq<u8>, st: LexState, out: Seq<Token>)
    ensures
        lex(t, st, out).len() <= out.len() + t.len() + 1 + lex_pending(st),
    decreases t.len(), mode_rank(st.mode)
{
    match st.mode {
        Mode::Skip => {
            if t.len() > 0 {
                let line = next_line(st.line, t[0]);
                if st.skip > 1 {
                    lemma_lex_len(t.drop_first(), skipping(line, (st.skip - 1) as u8, st.to_comment), out);
                } else if st.to_comment {
                    lemma_lex_len(t.drop_first(), LexState { mode: Mode::Comment, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }, out);
                } else {
                    lemma_lex_len(t.drop_first(), normal(line), out);
                }
            }
        },
        Mode::Comment => {
            if t.len() > 0 {
                if t[0] == 42u8 && t.len() >= 2 && t[1] == 47u8 {
                    lemma_lex_len(t.drop_first(), skipping(st.line, 1u8, false), out);
                } else {
                    lemma_lex_len(t.drop_first(), LexState { mode: Mode::Comment, line: next_line(st.line, t[0]), skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }, out);
                }
            }
        },
        Mode::Str => {
            if t.len() > 0 {
                if t[0] == 34u8 {
                    lemma_lex_len(t.drop_first(), normal(st.line), out.push(tok(Tok::Str, st.buf, st.line)));
                } else {
                    lemma_lex_len(t.drop_first(), LexState { mode: Mode::Str, line: next_line(st.line, t[0]), skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: false, start_line: st.start_line }, out);
                }
            }
        },
        Mode::Num => {
            if t.len() > 0 && is_bc_digit(t[0]) {
                lemma_lex_len(t.drop_first(), LexState { mode: Mode::Num, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: st.has_dot, start_line: 0u64 }, out);
            } else if t.len() > 0 && t[0] == 46u8 && !st.has_dot {
                lemma_lex_len(t.drop_first(), LexState { mode: Mode::Num, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: true, start_line: 0u64 }, out);
            } else if t.len() >= 2 && t[0] == 92u8 && t[1] == 10u8 {
                lemma_lex_len(t.drop_first().drop_first(), LexState { mode: Mode::Num, line: next_line(st.line, 10u8), skip: 0u8, to_comment: false, buf: st.buf, has_dot: st.has_dot, start_line: 0u64 }, out);
            } else if t.len() >= 3 && t[0] == 92u8 && t[1] == 13u8 && t[2] == 10u8 {
                lemma_lex_len(t.drop_first().drop_first().drop_first(), LexState { mode: Mode::Num, line: next_line(st.line, 10u8), skip: 0u8, to_comment: false, buf: st.buf, has_dot: st.has_dot, start_line: 0u64 }, out);
            } else {
                lemma_lex_len(t, normal(st.line), out.push(tok(Tok::Number, st.buf, st.line)));
            }
        },
        Mode::Ident => {
            if t.len() > 0 && is_ident_continue(t[0]) {
                lemma_lex_len(t.drop_first(), LexState { mode: Mode::Ident, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: false, start_line: 0u64 }, out);
            } else {
                lemma_lex_len(t, normal(st.line), out.push(tok(keyword(st.buf), st.buf, st.line)));
            }
        },
        Mode::Normal => {
            if t.len() > 0 {
                let c = t[0];
                let line = st.line;
                let r = t.drop_first();
                if c == 32u8 || c == 9u8 || c == 13u8 {
                    lemma_lex_len(r, normal(line), out);
                } else if c == 92u8 && t.len() >= 2 && t[1] == 10u8 {
                    lemma_lex_len(r, skipping(line, 1u8, false), out);
                } else if c == 92u8 && t.len() >= 3 && t[1] == 13u8 && t[2] == 10u8 {
                    lemma_lex_len(r, skipping(line, 2u8, false), out);
                } else if c == 47u8 && t.len() >= 2 && t[1] == 42u8 {
                    lemma_lex_len(r, skipping(line, 1u8, true), out);
                } else if c == 10u8 {
                    let l2 = next_line(line, c);
                    lemma_lex_len(r, normal(l2), out.push(tok(Tok::Newline, seq![10u8], l2)));
                } else if c == 34u8 {
                    lemma_lex_len(r, LexState { mode: Mode::Str, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: line }, out);
                } else if is_bc_digit(c) || (c == 46u8 && t.len() >= 2 && is_bc_digit(t[1])) {
                    lemma_lex_len(r, LexState { mode: Mode::Num, line: line, skip: 0u8, to_comment: false, buf: seq![c], has_dot: c == 46u8, start_line: 0u64 }, out);
                } else if 97 <= c && c <= 122 {
                    lemma_lex_len(r, LexState { mode: Mode::Ident, line: line, skip: 0u8, to_comment: false, buf: seq![c], has_dot: false, start_line: 0u64 }, out);
                } else {
                    let op = operator(t);
                    if op.1 == 1 {
                        lemma_lex_len(r, normal(line), out.push(tok(op.0, seq![c], line)));
                    } else if op.1 != 0 {
                        lemma_lex_len(r, skipping(line, 1u8, false), out.push(tok(op.0, seq![c, t[1]], line)));
                    }
                }
            }
        },
    }
}

/// Whether all the bytes are ASCII.
pub open spec fn ascii_bytes(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> b[i] < 0x80
}

/// A token that may come before the last one.
pub open spec fn tok_good(x: Token) -> bool {
    &&& !(x.kind is Eof)
    &&& !(x.kind is LexError)
    &&& (x.kind is Letter || x.kind is Number) ==> ascii_bytes(x.text)
}

/// The shape of a token sequence.
pub open spec fn toks_shape(r: Seq<Token>) -> bool {
    &&& r.len() > 0
    &&& r.last().kind is Eof || r.last().kind is LexError
    &&& forall|i: int| 0 <= i < r.len() - 1 ==> #[trigger] tok_good(r[i])
}

proof fn lemma_push_end(out: Seq<Token>, x: Token)
    requires
        forall|i: int| 0 <= i < out.len() ==> #[trigger] tok_good(out[i]),
        x.kind is Eof || x.kind is LexError,
    ensures
        toks_shape(out.push(x)),
{
    assert forall|i: int| 0 <= i < out.push(x).len() - 1 implies #[trigger] tok_good(out.push(x)[i]) by {
        assert(out.push(x)[i] == out[i]);
    }
}

proof fn lemma_push_good(out: Seq<Token>, x: Token)
    requires
        forall|i: int| 0 <= i < out.len() ==> #[trigger] tok_good(out[i]),
        tok_good(x),
    ensures
        forall|i: int| 0 <= i < out.push(x).len() ==> #[trigger] tok_good(out.push(x)[i]),
{
    assert forall|i: int| 0 <= i < out.push(x).len() implies #[trigger] tok_good(out.push(x)[i]) by {
        if i < out.len() { assert(out.push(x)[i] == out[i]); }
    }
}

proof fn lemma_ascii_push(b: Seq<u8>, c: u8)
    requires
        ascii_bytes(b),
        c < 0x80,
    ensures
        ascii_bytes(b.push(c)),
{
    assert forall|i: int| 0 <= i < b.push(c).len() implies b.push(c)[i] < 0x80 by {
        if i < b.len() { assert(b.push(c)[i] == b[i]); }
    }
}

/// `lex` ends with its one `Eof` or `LexError`, and names and numbers are ASCII.
pub proof fn lemma_lex_shape(t: Seq<u8>, st: LexState, out: Seq<Token>)
    requires
        forall|i: int| 0 <= i < out.len() ==> #[trigger] tok_good(out[i]),
        (st.mode is Num || st.mode is Ident) ==> ascii_bytes(st.buf),
    ensures
        toks_shape(lex(t, st, out)),
    decreases t.len(), mode_rank(st.mode)
{
    let e = Seq::<u8>::empty();
    assert(ascii_bytes(e));
    match st.mode {
        Mode::Skip => {
            if t.len() == 0 {
                lemma_push_end(out, tok(Tok::Eof, seq![], st.line));
            } else {
                let line = next_line(st.line, t[0]);
                if st.skip > 1 {
                    lemma_lex_shape(t.drop_first(), skipping(line, (st.skip - 1) as u8, st.to_comment), out);
                } else if st.to_comment {
                    lemma_lex_shape(t.drop_first(), LexState { mode: Mode::Comment, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }, out);
                } else {
                    lemma_lex_shape(t.drop_first(), normal(line), out);
                }
            }
        },
        Mode::Comment => {
            if t.len() == 0 {
                lemma_push_end(out, tok(Tok::LexError, syntax_error_msg(), st.line));
            } else if t[0] == 42u8 && t.len() >= 2 && t[1] == 47u8 {
                lemma_lex_shape(t.drop_first(), skipping(st.line, 1u8, false), out);
            } else {
                lemma_lex_shape(t.drop_first(), LexState { mode: Mode::Comment, line: next_line(st.line, t[0]), skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: 0u64 }, out);
            }
        },
        Mode::Str => {
            if t.len() == 0 {
                lemma_push_end(out, tok(Tok::LexError, illegal_msg(seq![34u8]), st.start_line));
            } else if t[0] == 34u8 {
                let x = tok(Tok::Str, st.buf, st.line);
                lemma_push_good(out, x);
                lemma_lex_shape(t.drop_first(), normal(st.line), out.push(x));
            } else {
                lemma_lex_shape(t.drop_first(), LexState { mode: Mode::Str, line: next_line(st.line, t[0]), skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: false, start_line: st.start_line }, out);
            }
        },
        Mode::Num => {
            if t.len() > 0 && is_bc_digit(t[0]) {
                lemma_ascii_push(st.buf, t[0]);
                lemma_lex_shape(t.drop_first(), LexState { mode: Mode::Num, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: st.has_dot, start_line: 0u64 }, out);
            } else if t.len() > 0 && t[0] == 46u8 && !st.has_dot {
                lemma_ascii_push(st.buf, t[0]);
                lemma_lex_shape(t.drop_first(), LexState { mode: Mode::Num, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: true, start_line: 0u64 }, out);
            } else if t.len() >= 2 && t[0] == 92u8 && t[1] == 10u8 {
                lemma_lex_shape(t.drop_first().drop_first(), LexState { mode: Mode::Num, line: next_line(st.line, 10u8), skip: 0u8, to_comment: false, buf: st.buf, has_dot: st.has_dot, start_line: 0u64 }, out);
            } else if t.len() >= 3 && t[0] == 92u8 && t[1] == 13u8 && t[2] == 10u8 {
                lemma_lex_shape(t.drop_first().drop_first().drop_first(), LexState { mode: Mode::Num, line: next_line(st.line, 10u8), skip: 0u8, to_comment: false, buf: st.buf, has_dot: st.has_dot, start_line: 0u64 }, out);
            } else {
                let x = tok(Tok::Number, st.buf, st.line);
                lemma_push_good(out, x);
                lemma_lex_shape(t, normal(st.line), out.push(x));
            }
        },
        Mode::Ident => {
            if t.len() > 0 && is_ident_continue(t[0]) {
                lemma_ascii_push(st.buf, t[0]);
                lemma_lex_shape(t.drop_first(), LexState { mode: Mode::Ident, line: st.line, skip: 0u8, to_comment: false, buf: st.buf.push(t[0]), has_dot: false, start_line: 0u64 }, out);
            } else {
                let x = tok(keyword(st.buf), st.buf, st.line);
                lemma_push_good(out, x);
                lemma_lex_shape(t, normal(st.line), out.push(x));
            }
        },
        Mode::Normal => {
            if t.len() == 0 {
                lemma_push_end(out, tok(Tok::Eof, seq![], st.line));
            } else {
                let c = t[0];
                let line = st.line;
                let r = t.drop_first();
                if c == 32u8 || c == 9u8 || c == 13u8 {
                    lemma_lex_shape(r, normal(line), out);
                } else if c == 92u8 && t.len() >= 2 && t[1] == 10u8 {
                    lemma_lex_shape(r, skipping(line, 1u8, false), out);
                } else if c == 92u8 && t.len() >= 3 && t[1] == 13u8 && t[2] == 10u8 {
                    lemma_lex_shape(r, skipping(line, 2u8, false), out);
                } else if c == 47u8 && t.len() >= 2 && t[1] == 42u8 {
                    lemma_lex_shape(r, skipping(line, 1u8, true), out);
                } else if c == 10u8 {
                    let l2 = next_line(line, c);
                    let x = tok(Tok::Newline, seq![10u8], l2);
                    lemma_push_good(out, x);
                    lemma_lex_shape(r, normal(l2), out.push(x));
                } else if c == 34u8 {
                    lemma_lex_shape(r, LexState { mode: Mode::Str, line: line, skip: 0u8, to_comment: false, buf: seq![], has_dot: false, start_line: line }, out);
                } else if is_bc_digit(c) || (c == 46u8 && t.len() >= 2 && is_bc_digit(t[1])) {
                    lemma_ascii_push(e, c);
                    assert(e.push(c) =~= seq![c]);
                    lemma_lex_shape(r, LexState { mode: Mode::Num, line: line, skip: 0u8, to_comment: false, buf: seq![c], has_dot: c == 46u8, start_line: 0u64 }, out);
                } else if 97 <= c && c <= 122 {
                    lemma_ascii_push(e, c);
                    assert(e.push(c) =~= seq![c]);
                    lemma_lex_shape(r, LexState { mode: Mode::Ident, line: line, skip: 0u8, to_comment: false, buf: seq![c], has_dot: false, start_line: 0u64 }, out);
                } else {
                    let op = operator(t);
                    if op.1 == 0 {
                        lemma_push_end(out, tok(Tok::LexError, illegal_msg(t), line));
                    } else if op.1 == 1 {
                        let x = tok(op.0, seq![c], line);
                        lemma_push_good(out, x);
                        lemma_lex_shape(r, normal(line), out.push(x));
                    } else {
                        let x = tok(op.0, seq![c, t[1]], line);
                        lemma_push_good(out, x);
                        lemma_lex_shape(r, skipping(line, 1u8, false), out.push(x));
                    }
                }
            }
        },
    }
}

/// A block scan can stop at the end of a line and resume there: a step looks ahead only within
/// a line, so what follows the newline does not change it.
pub proof fn lemma_block_scan_split(a: Seq<u8>, b: Seq<u8>, st: BlockScan)
    requires
        a.len() == 0 || a[a.len() - 1] == 10u8,
    ensures
        block_scan(a + b, st) == block_scan(b, block_scan(a, st)),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        let t = a + b;
        let c = a[0];
        assert(t[0] == c);
        let r1 = a.drop_first();
        assert(t.drop_first() =~= r1 + b);
        // The bytes that a step looks at, when they are in `a`.
        if a.len() >= 2 { assert(t[1] == a[1]); }
        if a.len() >= 3 { assert(t[2] == a[2]); }
        if a.len() >= 2 {
            let r2 = r1.drop_first();
            assert((r1 + b).drop_first() =~= r2 + b);
            if a.len() >= 3 {
                assert((r2 + b).drop_first() =~= r2.drop_first() + b);
                if a.len() > 3 { assert(r2.drop_first()[r2.drop_first().len() - 1] == 10u8); }
                assert(r2[r2.len() - 1] == 10u8);
            }
            assert(r1[r1.len() - 1] == 10u8);
        }
        let n = if st.count < 0x7fff_ffff_ffff_ffffi64 { (st.count + 1) as i64 } else { st.count };
        let d = if st.count > -0x7fff_ffff_ffff_ffffi64 { (st.count - 1) as i64 } else { st.count };
        if st.in_comment {
            if c == 42u8 && t.len() >= 2 && t[1] == 47u8 {
                lemma_block_scan_split(r1.drop_first(), b, BlockScan { count: st.count, in_comment: false, in_string: false });
            } else {
                lemma_block_scan_split(r1, b, st);
            }
        } else if st.in_string {
            if c == 34u8 {
                lemma_block_scan_split(r1, b, BlockScan { count: st.count, in_comment: false, in_string: false });
            } else if c == 92u8 && t.len() >= 2 && t[1] == 10u8 {
                lemma_block_scan_split(r1.drop_first(), b, st);
            } else if c == 92u8 && t.len() >= 3 && t[1] == 13u8 && t[2] == 10u8 {
                lemma_block_scan_split(r1.drop_first().drop_first(), b, st);
            } else {
                lemma_block_scan_split(r1, b, st);
            }
        } else if c == 47u8 && t.len() >= 2 && t[1] == 42u8 {
            lemma_block_scan_split(r1.drop_first(), b, BlockScan { count: st.count, in_comment: true, in_string: false });
        } else if c == 34u8 {
            lemma_block_scan_split(r1, b, BlockScan { count: st.count, in_comment: false, in_string: true });
        } else if c == 123u8 {
            lemma_block_scan_split(r1, b, BlockScan { count: n, in_comment: false, in_string: false });
        } else if c == 125u8 {
            lemma_block_scan_split(r1, b, BlockScan { count: d, in_comment: false, in_string: false });
        } else {
            lemma_block_scan_split(r1, b, st);
        }
    }
}

} // verus!
