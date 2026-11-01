// SPDX-License-Identifier: MIT

//! The lexer: an incremental scanner over the bytes of an input unit.

use super::{Token, TokenType};
use crate::error::BcError;
use crate::verified_kernels::{
    verified_is_bc_digit, verified_is_ident_continue, verified_lexer_advance_step,
    verified_lexer_peek_char_index, verified_lexer_peek_token_index, verified_utf8_char_len,
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

/// An incremental lexical analyzer for the bc language.
pub struct Lexer {
    text: Vec<u8>,
    pos: usize,
    pub line: usize,
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
    fn error<T>(&self, msg: &str) -> Result<T, BcError> {
        Err(BcError::syntax(self.line, String::from(msg)))
    }

    /// Reports a character (its bytes `c`) that cannot start any token, as GNU bc does.
    fn illegal_character<T>(&self, c: &[u8]) -> Result<T, BcError> {
        Err(BcError::Syntax {
            line: self.line,
            message: format!("illegal character: {}", display_illegal(c)),
            detail: format!("unexpected bytes {:?}", c),
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
                        return self.error("unterminated comment");
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

    /// Scans the next token from input.
    fn scan_token(&mut self) -> Result<Token, BcError> {
        self.skip_whitespace_and_comments()?;
        let Some(c) = self.peek(0) else {
            return Ok(Token {
                token_type: TokenType::Eof,
                value: Vec::new(),
                line: self.line,
            });
        };

        if c == b'\n' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Newline,
                value: b"\n".to_vec(),
                line: self.line,
            });
        }

        if c == b';' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Semicolon,
                value: b";".to_vec(),
                line: self.line,
            });
        }
        if c == b',' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Comma,
                value: b",".to_vec(),
                line: self.line,
            });
        }
        if c == b'(' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Lparen,
                value: b"(".to_vec(),
                line: self.line,
            });
        }
        if c == b')' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Rparen,
                value: b")".to_vec(),
                line: self.line,
            });
        }
        if c == b'[' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Lbracket,
                value: b"[".to_vec(),
                line: self.line,
            });
        }
        if c == b']' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Rbracket,
                value: b"]".to_vec(),
                line: self.line,
            });
        }
        if c == b'{' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Lbrace,
                value: b"{".to_vec(),
                line: self.line,
            });
        }
        if c == b'}' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Rbrace,
                value: b"}".to_vec(),
                line: self.line,
            });
        }

        if c == b'^' {
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: b"^=".to_vec(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Exp,
                value: b"^".to_vec(),
                line: self.line,
            });
        }

        if c == b'+' {
            if self.peek_char(1) == b'+' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::IncrDecr,
                    value: b"++".to_vec(),
                    line: self.line,
                });
            }
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: b"+=".to_vec(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Plus,
                value: b"+".to_vec(),
                line: self.line,
            });
        }

        if c == b'-' {
            if self.peek_char(1) == b'-' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::IncrDecr,
                    value: b"--".to_vec(),
                    line: self.line,
                });
            }
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: b"-=".to_vec(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Minus,
                value: b"-".to_vec(),
                line: self.line,
            });
        }

        if c == b'*' {
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: b"*=".to_vec(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::MulOp,
                value: b"*".to_vec(),
                line: self.line,
            });
        }

        if c == b'/' {
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: b"/=".to_vec(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::MulOp,
                value: b"/".to_vec(),
                line: self.line,
            });
        }

        if c == b'%' {
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: b"%=".to_vec(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::MulOp,
                value: b"%".to_vec(),
                line: self.line,
            });
        }

        if c == b'=' {
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::RelOp,
                    value: b"==".to_vec(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::AssignOp,
                value: b"=".to_vec(),
                line: self.line,
            });
        }

        if c == b'<' {
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::RelOp,
                    value: b"<=".to_vec(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::RelOp,
                value: b"<".to_vec(),
                line: self.line,
            });
        }

        if c == b'>' {
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::RelOp,
                    value: b">=".to_vec(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::RelOp,
                value: b">".to_vec(),
                line: self.line,
            });
        }

        if c == b'!' {
            if self.peek_char(1) == b'=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::RelOp,
                    value: b"!=".to_vec(),
                    line: self.line,
                });
            }
            return self.illegal_character(b"!");
        }

        if c == b'"' {
            // An unterminated string is reported at the line where it starts, as in GNU bc.
            let start_line = self.line;
            self.advance_char(1);
            let mut val_chars = Vec::new();
            loop {
                let Some(cc) = self.peek(0) else {
                    self.line = start_line;
                    return self.illegal_character(b"\"");
                };
                if cc == b'"' {
                    self.advance_char(1);
                    break;
                }
                if cc == b'\\' && self.peek_char(1) == b'\n' {
                    val_chars.push(b'\\');
                    val_chars.push(b'\n');
                    self.advance_char(2);
                } else if cc == b'\\' && self.peek_char(1) == b'\r' && self.peek_char(2) == b'\n' {
                    val_chars.push(b'\\');
                    val_chars.push(b'\r');
                    val_chars.push(b'\n');
                    self.advance_char(3);
                } else {
                    val_chars.push(cc);
                    self.advance_char(1);
                }
            }
            return Ok(Token {
                token_type: TokenType::String,
                value: val_chars,
                line: self.line,
            });
        }

        let is_digit = |ch: u8| -> bool { verified_is_bc_digit(u32::from(ch)) };

        if is_digit(c) || (c == b'.' && is_digit(self.peek_char(1))) {
            let mut val_chars = Vec::new();
            let mut has_dot = false;
            loop {
                let cc = self.peek_char(0);
                if is_digit(cc) {
                    val_chars.push(cc);
                    self.advance_char(1);
                } else if cc == b'.' && !has_dot {
                    has_dot = true;
                    val_chars.push(cc);
                    self.advance_char(1);
                } else if cc == b'\\' && self.peek_char(1) == b'\n' {
                    self.advance_char(2);
                } else if cc == b'\\' && self.peek_char(1) == b'\r' && self.peek_char(2) == b'\n' {
                    self.advance_char(3);
                } else {
                    break;
                }
            }
            return Ok(Token {
                token_type: TokenType::Number,
                value: val_chars,
                line: self.line,
            });
        }

        if c.is_ascii_lowercase() {
            let mut letters = vec![c];
            self.advance_char(1);
            loop {
                let peek = self.peek_char(0);
                if verified_is_ident_continue(u32::from(peek)) {
                    letters.push(peek);
                    self.advance_char(1);
                } else {
                    break;
                }
            }
            let token_type = match letters.as_slice() {
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
            };

            return Ok(Token {
                token_type,
                value: letters,
                line: self.line,
            });
        }

        let len = verified_utf8_char_len(&self.text, self.pos);
        self.illegal_character(&self.text[self.pos..self.pos + len])
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

    /// Peeks a token at a given offset forward, returning Err on lexical error.
    pub fn try_peek_token(&mut self, offset: usize) -> Result<&Token, BcError> {
        while self.buffer.len() <= offset {
            let tok = self.scan_token()?;
            let is_eof = tok.token_type == TokenType::Eof;
            self.buffer.push(tok);
            if is_eof {
                break;
            }
        }
        let idx = verified_lexer_peek_token_index(self.buffer.len(), offset);
        Ok(&self.buffer[idx])
    }

    /// Peeks a token at a given offset forward.
    #[cfg(test)]
    pub fn peek_token(&mut self, offset: usize) -> &Token {
        self.try_peek_token(offset)
            .unwrap_or_else(|e| panic!("{:?}", e))
    }
}
