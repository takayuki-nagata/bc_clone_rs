// SPDX-License-Identifier: MIT

//! The lexer: an incremental scanner over the bytes of an input unit.

use super::{Token, TokenType};
use crate::driver::UNIT_TOO_LONG;
use crate::error::BcError;
use crate::verified_kernels::{
    verified_is_bc_digit, verified_is_ident_continue, verified_lexer_advance_step,
    verified_lexer_peek_char_index, verified_lexer_peek_token_index, verified_unit_within_limit,
    verified_utf8_char_len,
};
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

/// Formats a character (its bytes `c`) for an `illegal character` diagnostic the way GNU bc
/// does: control characters as `^X`, DEL and other bytes outside ASCII as octal escapes.
fn display_illegal(c: &[u8]) -> String {
    match c {
        // `b + 0x40` is in 0x40..0x60, an ASCII character.
        [b] if *b < 0x20 => format!("^{}", char::from(*b + 0x40)),
        [b] if *b < 0x7f => char::from(*b).to_string(),
        _ => c.iter().map(|b| format!("\\{:03o}", b)).collect(),
    }
}

/// The operator at a byte `c` followed by `next` (0 at the end of the input), as `(kind, length)`;
/// length 0 if there is none (the specification's `operator`).
fn operator(c: u8, next: u8) -> (TokenType, u8) {
    let eq = next == b'=';
    match c {
        b';' => (TokenType::Semicolon, 1),
        b',' => (TokenType::Comma, 1),
        b'(' => (TokenType::Lparen, 1),
        b')' => (TokenType::Rparen, 1),
        b'[' => (TokenType::Lbracket, 1),
        b']' => (TokenType::Rbracket, 1),
        b'{' => (TokenType::Lbrace, 1),
        b'}' => (TokenType::Rbrace, 1),
        b'^' if eq => (TokenType::AssignOp, 2),
        b'^' => (TokenType::Exp, 1),
        b'+' if next == b'+' => (TokenType::IncrDecr, 2),
        b'+' if eq => (TokenType::AssignOp, 2),
        b'+' => (TokenType::Plus, 1),
        b'-' if next == b'-' => (TokenType::IncrDecr, 2),
        b'-' if eq => (TokenType::AssignOp, 2),
        b'-' => (TokenType::Minus, 1),
        b'*' | b'/' | b'%' if eq => (TokenType::AssignOp, 2),
        b'*' | b'/' | b'%' => (TokenType::MulOp, 1),
        b'=' if eq => (TokenType::RelOp, 2),
        b'=' => (TokenType::AssignOp, 1),
        b'<' | b'>' if eq => (TokenType::RelOp, 2),
        b'<' | b'>' => (TokenType::RelOp, 1),
        b'!' if eq => (TokenType::RelOp, 2),
        _ => (TokenType::Eof, 0),
    }
}

/// The keyword kind of a name, or `Letter`.
fn keyword(name: &[u8]) -> TokenType {
    match name {
        b"auto" => TokenType::Auto,
        b"break" => TokenType::Break,
        b"define" => TokenType::Define,
        b"ibase" => TokenType::Ibase,
        b"if" => TokenType::If,
        b"for" => TokenType::For,
        b"length" => TokenType::Length,
        b"obase" => TokenType::Obase,
        b"quit" => TokenType::Quit,
        b"return" => TokenType::Return,
        b"scale" => TokenType::Scale,
        b"sqrt" => TokenType::Sqrt,
        b"while" => TokenType::While,
        _ => TokenType::Letter,
    }
}

/// An incremental lexical analyzer for the bc language.
pub struct Lexer {
    text: Vec<u8>,
    pos: usize,
    line: usize,
    buffer: Vec<Token>,
}

impl Lexer {
    /// Creates a new Lexer from the source bytes. They need not be UTF-8: a string's bytes are
    /// kept unchanged, and elsewhere a byte that is not part of a token is an illegal character.
    pub fn new(text: &[u8]) -> Self {
        Self {
            text: text.to_vec(),
            pos: 0,
            line: 1,
            buffer: Vec::new(),
        }
    }

    /// Triggers a syntax error during lexical analysis.
    fn error<T>(&self) -> Result<T, BcError> {
        Err(BcError::syntax(self.line))
    }

    /// Reports a character (its bytes `c`) that cannot start any token, as GNU bc does.
    fn illegal_character<T>(&self, c: &[u8]) -> Result<T, BcError> {
        Err(BcError::Syntax {
            line: self.line,
            message: format!("illegal character: {}", display_illegal(c)),
        })
    }

    /// Peeks a character ahead of the current position by the given offset; `None` past the end.
    fn peek(&self, offset: usize) -> Option<u8> {
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
    fn peek_char(&self, offset: usize) -> u8 {
        self.peek(offset).unwrap_or(0)
    }

    /// Advances the position pointer by `steps`.
    pub(super) fn advance_char(&mut self, steps: usize) {
        for _ in 0..steps {
            if self.pos < self.text.len() {
                let (next_pos, next_line) =
                    verified_lexer_advance_step(self.pos, self.line, self.text[self.pos] == b'\n');
                self.pos = next_pos;
                self.line = next_line;
            }
        }
    }

    /// Skips whitespace, comments (`/* ... */`), and backslash-newlines.
    fn skip_whitespace_and_comments(&mut self) -> Result<(), BcError> {
        loop {
            let c = self.peek_char(0);
            if c == b' ' || c == b'\t' || c == b'\r' {
                self.advance_char(1);
            } else if c == b'\\' && self.peek_char(1) == b'\n' {
                self.advance_char(2);
            } else if c == b'\\' && self.peek_char(1) == b'\r' && self.peek_char(2) == b'\n' {
                self.advance_char(3);
            } else if c == b'/' && self.peek_char(1) == b'*' {
                self.advance_char(2);
                loop {
                    let Some(cc) = self.peek(0) else {
                        return self.error();
                    };
                    if cc == b'*' && self.peek_char(1) == b'/' {
                        self.advance_char(2);
                        break;
                    }
                    self.advance_char(1);
                }
            } else {
                break;
            }
        }
        Ok(())
    }

    /// A token made of the bytes just consumed, or of the bytes given.
    fn token(&self, token_type: TokenType, value: Vec<u8>) -> Token {
        Token {
            token_type,
            value,
            line: self.line,
        }
    }

    /// Scans the next token from input.
    fn scan_token(&mut self) -> Result<Token, BcError> {
        if !verified_unit_within_limit(self.text.len()) {
            return Err(BcError::Syntax {
                line: 1,
                message: String::from(UNIT_TOO_LONG),
            });
        }
        self.skip_whitespace_and_comments()?;
        let Some(c) = self.peek(0) else {
            return Ok(self.token(TokenType::Eof, Vec::new()));
        };

        if c == b'\n' {
            self.advance_char(1);
            return Ok(self.token(TokenType::Newline, vec![c]));
        }
        if c == b'"' {
            return self.scan_string();
        }
        if verified_is_bc_digit(u32::from(c))
            || (c == b'.' && verified_is_bc_digit(u32::from(self.peek_char(1))))
        {
            return Ok(self.scan_number());
        }
        if c.is_ascii_lowercase() {
            return Ok(self.scan_name(c));
        }

        let next = self.peek_char(1);
        let (token_type, len) = operator(c, next);
        if len == 0 {
            let len = verified_utf8_char_len(&self.text, self.pos);
            return self.illegal_character(&self.text[self.pos..self.pos + len]);
        }
        self.advance_char(usize::from(len));
        let value = if len == 1 { vec![c] } else { vec![c, next] };
        Ok(self.token(token_type, value))
    }

    /// Scans a string, whose opening quote is the current byte. An unterminated string is
    /// reported at the line where it starts, as in GNU bc.
    fn scan_string(&mut self) -> Result<Token, BcError> {
        let start_line = self.line;
        self.advance_char(1);
        let mut bytes = Vec::new();
        loop {
            let Some(c) = self.peek(0) else {
                self.line = start_line;
                return self.illegal_character(b"\"");
            };
            self.advance_char(1);
            if c == b'"' {
                return Ok(self.token(TokenType::String, bytes));
            }
            bytes.push(c);
        }
    }

    /// Scans a number: digits with at most one point, and backslash-newlines that join its parts.
    fn scan_number(&mut self) -> Token {
        let mut digits = Vec::new();
        let mut has_dot = false;
        loop {
            let c = self.peek_char(0);
            if verified_is_bc_digit(u32::from(c)) {
                digits.push(c);
                self.advance_char(1);
            } else if c == b'.' && !has_dot {
                has_dot = true;
                digits.push(c);
                self.advance_char(1);
            } else if c == b'\\' && self.peek_char(1) == b'\n' {
                self.advance_char(2);
            } else if c == b'\\' && self.peek_char(1) == b'\r' && self.peek_char(2) == b'\n' {
                self.advance_char(3);
            } else {
                return self.token(TokenType::Number, digits);
            }
        }
    }

    /// Scans a name or keyword, whose first letter `first` is the current byte.
    fn scan_name(&mut self, first: u8) -> Token {
        let mut letters = vec![first];
        self.advance_char(1);
        loop {
            let c = self.peek_char(0);
            if !verified_is_ident_continue(u32::from(c)) {
                let token_type = keyword(&letters);
                return self.token(token_type, letters);
            }
            letters.push(c);
            self.advance_char(1);
        }
    }

    /// Obtains the next token, returning Err on lexical error.
    pub fn try_get_next_token(&mut self) -> Result<Token, BcError> {
        if !self.buffer.is_empty() {
            Ok(self.buffer.remove(0))
        } else {
            self.scan_token()
        }
    }

    /// Obtains the next token, consuming it from the buffer or stream.
    #[cfg(test)]
    pub fn get_next_token(&mut self) -> Token {
        self.try_get_next_token()
            .unwrap_or_else(|e| panic!("{:?}", e))
    }

    /// The kind of the token at a given offset forward, or Err on lexical error.
    pub fn try_peek_token(&mut self, offset: usize) -> Result<TokenType, BcError> {
        while self.buffer.len() <= offset {
            let tok = self.scan_token()?;
            let is_eof = tok.token_type == TokenType::Eof;
            self.buffer.push(tok);
            if is_eof {
                break;
            }
        }
        let idx = verified_lexer_peek_token_index(self.buffer.len(), offset);
        Ok(self.buffer[idx].token_type)
    }
}
