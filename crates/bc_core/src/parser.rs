// SPDX-License-Identifier: MIT

//! Lexer, Parser, and Abstract Syntax Tree (AST) definitions for the bc clone.
//!
//! Conforms to standard POSIX bc lexical and syntax grammar rules, supporting
//! operator precedence climbing and backslash-newline continuation.

use crate::error::BcError;
use crate::verified_kernels::{
    TOK_ASSIGN_OP, TOK_EXP_OP, TOK_MUL_OP, TOK_PLUS_MINUS, verified_is_bc_digit,
    verified_is_ident_continue, verified_lexer_advance_step, verified_lexer_peek_char_index,
    verified_lexer_peek_token_index, verified_nesting_within_limit, verified_pratt_infix_info,
    verified_utf8_char_len,
};
use alloc::boxed::Box;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// The types of tokens supported by the bc lexer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
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

    // Operators
    Plus,
    Minus,
    Exp,
    MulOp,    // *, /, %
    RelOp,    // ==, <=, >=, !=, <, >
    IncrDecr, // ++, --
    AssignOp, // =, +=, -=, *=, /=, %=, ^=

    // Literals & Identifiers
    Letter, // lowercase identifier starting with a-z
    Number, // numeric constant
    String, // string constant

    // Keywords
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
}

/// A token scanned from the source input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub token_type: TokenType,
    /// The token's bytes (for a string, its text between the quotes).
    pub value: Vec<u8>,
    pub line: usize,
}

impl Token {
    /// The token's bytes as a `String`. Names, numbers and operators are ASCII, so each byte is
    /// one character.
    fn text(&self) -> String {
        self.value.iter().map(|&b| char::from(b)).collect()
    }
}

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
    fn advance_char(&mut self, steps: usize) {
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

// --- AST Node Definitions ---

/// Struct representing a formal parameter or local auto variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub is_array: bool,
}

/// One of the special registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Register {
    Scale,
    Ibase,
    Obase,
}

/// A binary arithmetic operator. The order is that of the specification's operator codes
/// (`crates/bc_spec`, `binop_code`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
}

/// A relational operator, in the order of the specification's `rel_code`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// An assignment operator: `=`, or `op=` for a binary operator (as `assign_code`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Assign,
    Compound(BinOp),
}

/// Enum representing an expression in bc AST.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Number(String),
    Variable(String),
    ArrayAccess(String, Box<Expr>),
    RegisterAccess(Register),
    /// Unary minus.
    Negate(Box<Expr>),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
    RelationalOp(RelOp, Box<Expr>, Box<Expr>),
    /// `++`/`--` as `(increment, prefix, target)`.
    Update(bool, bool, Box<Expr>),
    /// `(operator, target, value)`.
    AssignOp(AssignOp, Box<Expr>, Box<Expr>),
    Call(String, Vec<ExprOrArray>),
    LengthCall(Box<Expr>),
    SqrtCall(Box<Expr>),
    ScaleCall(Box<Expr>),
    /// A parenthesized expression; kept so that `(a = 5)` is printed while `a = 5` is not.
    Paren(Box<Expr>),
}

/// Enum wrapper for function call arguments which can be standard expressions
/// or whole arrays (e.g. `a[]`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprOrArray {
    Expr(Expr),
    ArrayArg(String),
}

/// Struct representing a function definition in bc AST.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDef {
    pub name: String,
    pub params: Vec<Param>,
    pub autos: Vec<Param>,
    pub body: Vec<Stmt>,
}

/// Enum representing a statement in bc AST.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Block(Vec<Stmt>),
    Expr(Expr),
    StringLiteral(Vec<u8>),
    Break,
    Quit,
    Return(Option<Expr>),
    If(Expr, Box<Stmt>),
    While(Expr, Box<Stmt>),
    For(Expr, Expr, Expr, Box<Stmt>),
    FunctionDef(FunctionDef),
}

/// How the parser treats the non-POSIX syntax listed in `docs/COMPATIBILITY.md` §4.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExtensionPolicy {
    /// Accept extensions silently (default).
    #[default]
    Allow,
    /// Accept extensions and record each use as a warning (`-w`).
    Warn,
    /// Record each use as an error; the input unit must not be executed (`-s`).
    Reject,
}

verus! {

// The syntax tree as Verus sees it (for the refinement proofs). The types are
// declared outside `verus!` because Verus rejects derived trait impls on recursive types.
#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExParam(Param);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExRegister(Register);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExBinOp(BinOp);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExRelOp(RelOp);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExAssignOp(AssignOp);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExExpr(Expr);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExExprOrArray(ExprOrArray);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExFunctionDef(FunctionDef);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExStmt(Stmt);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExExtensionPolicy(ExtensionPolicy);

} // verus!

impl BinOp {
    /// The operator of a `+`, `-`, `*`, `/`, `%` or `^` token (as `binop_code`: `^` for any
    /// other text, which the lexer does not produce).
    pub fn from_symbol(text: &str) -> Self {
        match text.as_bytes().first() {
            Some(b'+') => Self::Add,
            Some(b'-') => Self::Sub,
            Some(b'*') => Self::Mul,
            Some(b'/') => Self::Div,
            Some(b'%') => Self::Mod,
            _ => Self::Pow,
        }
    }
}

impl RelOp {
    /// The operator of a relational token (as `rel_code`).
    pub fn from_symbol(text: &str) -> Self {
        let two = text.len() == 2;
        match text.as_bytes().first() {
            Some(b'=') => Self::Eq,
            Some(b'!') => Self::Ne,
            Some(b'<') => {
                if two {
                    Self::Le
                } else {
                    Self::Lt
                }
            }
            _ => {
                if two {
                    Self::Ge
                } else {
                    Self::Gt
                }
            }
        }
    }
}

impl AssignOp {
    /// The operator of an assignment token.
    pub fn from_symbol(text: &str) -> Self {
        if text.len() == 1 {
            Self::Assign
        } else {
            Self::Compound(BinOp::from_symbol(text))
        }
    }
}

/// Recursive descent parser with operator precedence support for bc.
pub struct Parser {
    pub lexer: Lexer,
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
            detail: String::from(NESTING_TOO_DEEP),
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
    fn error<T>(&self, msg: &str) -> Result<T, BcError> {
        Err(BcError::syntax(self.current_token.line, String::from(msg)))
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

    /// Records a use of non-POSIX syntax on the line of the current token, as GNU bc does.
    fn extension(&mut self, description: String) {
        if self.extension_policy != ExtensionPolicy::Allow {
            self.extension_uses
                .push((self.current_token.line, description));
        }
    }

    /// Consumes an identifier, recording it if it is longer than one letter (an extension).
    fn eat_name(&mut self) -> Result<String, BcError> {
        let name = self.current_token.text();
        self.eat(TokenType::Letter)?;
        self.note_name(&name);
        Ok(name)
    }

    fn note_name(&mut self, name: &str) {
        if name.len() > 1 {
            self.extension(format!("multiple letter name - {}", name));
        }
    }

    /// Reports a statement that is not allowed where it appears, with GNU bc's wording, on the
    /// line of the current token.
    fn misplaced<T>(&self, message: &str) -> Result<T, BcError> {
        Err(BcError::Syntax {
            line: self.current_token.line,
            message: String::from(message),
            detail: String::from(message),
        })
    }

    /// Parses a loop body, tracking the loop nesting for `break`.
    fn parse_loop_body(&mut self) -> Result<Stmt, BcError> {
        self.loop_depth += 1;
        let body = self.parse_statement();
        self.loop_depth -= 1;
        body
    }

    /// Consumes a token of the expected type, otherwise raises error.
    fn eat(&mut self, token_type: TokenType) -> Result<(), BcError> {
        if self.current_token.token_type == token_type {
            self.last_line = self.current_token.line;
            self.current_token = self.lexer.try_get_next_token()?;
            Ok(())
        } else {
            self.error(&format!(
                "expected {:?}, got {:?}",
                token_type, self.current_token.token_type
            ))
        }
    }

    /// Peeks the token type of the token at `offset`.
    fn peek_token_type(&mut self, offset: usize) -> Result<TokenType, BcError> {
        Ok(self.lexer.try_peek_token(offset)?.token_type)
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
            self.eat(TokenType::Newline)?;
        } else {
            self.eat(TokenType::Eof)?;
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
                self.eat(TokenType::Semicolon)?;
                continue;
            }

            let stmt = self.parse_statement()?;
            stmts.push(stmt);

            if self.current_token.token_type == TokenType::Semicolon {
                self.eat(TokenType::Semicolon)?;
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
            self.skip_newlines()?;
            let t = self.current_token.token_type;
            if t == TokenType::Eof || t == TokenType::Rbrace {
                break;
            }

            let stmt = self.parse_statement()?;
            stmts.push(stmt);

            let nt = self.current_token.token_type;
            match nt {
                TokenType::Semicolon => {
                    self.eat(TokenType::Semicolon)?;
                }
                TokenType::Newline => {
                    self.eat(TokenType::Newline)?;
                }
                TokenType::Rbrace | TokenType::Eof => {}
                _ => return self.error(&format!("expected separator, got {:?}", nt)),
            }
        }
        Ok(stmts)
    }

    /// Skips sequence of newline tokens.
    fn skip_newlines(&mut self) -> Result<(), BcError> {
        while self.current_token.token_type == TokenType::Newline {
            self.eat(TokenType::Newline)?;
        }
        Ok(())
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
            TokenType::String => {
                let val = self.current_token.value.clone();
                self.eat(TokenType::String)?;
                Ok(Stmt::StringLiteral(val))
            }
            TokenType::Break => {
                // GNU bc reports a stray `break` on its own line, and a stray `return` on the
                // line of the token after it.
                if self.loop_depth == 0 {
                    return self.misplaced("Break outside a for/while");
                }
                self.eat(TokenType::Break)?;
                Ok(Stmt::Break)
            }
            TokenType::Quit => Err(BcError::Quit),
            TokenType::Return => {
                let stmt = self.parse_return()?;
                if !self.in_function {
                    return self.misplaced("Return outside of a function.");
                }
                Ok(stmt)
            }
            TokenType::For => {
                self.eat(TokenType::For)?;
                self.eat(TokenType::Lparen)?;
                let init = self.parse_expression()?;
                self.eat(TokenType::Semicolon)?;
                let cond = self.parse_relational_expression()?;
                self.eat(TokenType::Semicolon)?;
                let post = self.parse_expression()?;
                self.eat(TokenType::Rparen)?;
                let body = self.parse_loop_body()?;
                Ok(Stmt::For(init, cond, post, Box::new(body)))
            }
            TokenType::If => {
                self.eat(TokenType::If)?;
                self.eat(TokenType::Lparen)?;
                let cond = self.parse_relational_expression()?;
                self.eat(TokenType::Rparen)?;
                let body = self.parse_statement()?;
                Ok(Stmt::If(cond, Box::new(body)))
            }
            TokenType::While => {
                self.eat(TokenType::While)?;
                self.eat(TokenType::Lparen)?;
                let cond = self.parse_relational_expression()?;
                self.eat(TokenType::Rparen)?;
                let body = self.parse_loop_body()?;
                Ok(Stmt::While(cond, Box::new(body)))
            }
            TokenType::Lbrace => {
                self.eat(TokenType::Lbrace)?;
                let stmts = self.parse_statement_list()?;
                self.eat(TokenType::Rbrace)?;
                Ok(Stmt::Block(stmts))
            }
            _ => {
                let expr = self.parse_relational_expression()?;
                if matches!(expr, Expr::RelationalOp(..)) {
                    self.extension(String::from("comparison in expression"));
                }
                Ok(Stmt::Expr(expr))
            }
        }
    }

    /// Parses `return`, `return (e)`, or the GNU extension `return e`.
    fn parse_return(&mut self) -> Result<Stmt, BcError> {
        self.eat(TokenType::Return)?;
        if self.current_token.token_type == TokenType::Lparen {
            self.eat(TokenType::Lparen)?;
            // POSIX: `return ()` is `return (0)`.
            if self.current_token.token_type == TokenType::Rparen {
                self.eat(TokenType::Rparen)?;
                return Ok(Stmt::Return(None));
            }
            let expr = self.parse_expression()?;
            self.eat(TokenType::Rparen)?;
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
            self.extension(String::from("return expression requires parenthesis"));
            Ok(Stmt::Return(Some(expr)))
        } else {
            Ok(Stmt::Return(None))
        }
    }

    /// Parses a function definition `define f(x) { ... }`.
    fn parse_function(&mut self) -> Result<Stmt, BcError> {
        self.eat(TokenType::Define)?;
        if self.current_token.token_type != TokenType::Letter {
            return self.error("expected function name (letter)");
        }
        let name = self.current_token.text();
        self.eat(TokenType::Letter)?;

        self.eat(TokenType::Lparen)?;
        let params = self.parse_opt_define_list()?;
        self.eat(TokenType::Rparen)?;

        self.eat(TokenType::Lbrace)?;
        // POSIX requires a newline after `{`; GNU bc checks the name at this point too.
        if self.current_token.token_type != TokenType::Newline {
            self.extension(String::from("End of line required"));
        }
        self.note_name(&name);
        self.skip_newlines()?;

        let autos = self.parse_opt_auto_define_list()?;
        let outer = (self.loop_depth, self.in_function);
        (self.loop_depth, self.in_function) = (0, true);
        let body = self.parse_statement_list();
        (self.loop_depth, self.in_function) = outer;
        let body = body?;
        self.eat(TokenType::Rbrace)?;

        Ok(Stmt::FunctionDef(FunctionDef {
            name,
            params,
            autos,
            body,
        }))
    }

    /// Parses optional parameters/autos define list.
    fn parse_opt_define_list(&mut self) -> Result<Vec<Param>, BcError> {
        if self.current_token.token_type == TokenType::Rparen {
            Ok(Vec::new())
        } else {
            self.parse_define_list()
        }
    }

    /// Parses a define list of parameters or auto variables.
    fn parse_define_list(&mut self) -> Result<Vec<Param>, BcError> {
        let mut lst = Vec::new();
        loop {
            if self.current_token.token_type != TokenType::Letter {
                return self.error("expected parameter name (letter)");
            }
            let pname = self.eat_name()?;
            let mut is_arr = false;
            if self.current_token.token_type == TokenType::Lbracket {
                self.eat(TokenType::Lbracket)?;
                self.eat(TokenType::Rbracket)?;
                is_arr = true;
            }
            lst.push(Param {
                name: pname,
                is_array: is_arr,
            });

            if self.current_token.token_type == TokenType::Comma {
                self.eat(TokenType::Comma)?;
            } else {
                break;
            }
        }
        Ok(lst)
    }

    /// Parses auto list declarations `auto a, b[]`.
    fn parse_opt_auto_define_list(&mut self) -> Result<Vec<Param>, BcError> {
        if self.current_token.token_type != TokenType::Auto {
            return Ok(Vec::new());
        }
        self.eat(TokenType::Auto)?;
        let lst = self.parse_define_list()?;
        let t = self.current_token.token_type;
        if t == TokenType::Newline {
            self.eat(TokenType::Newline)?;
        } else if t == TokenType::Semicolon {
            self.eat(TokenType::Semicolon)?;
        } else {
            return self.error("expected newline or semicolon after auto declaration");
        }
        Ok(lst)
    }

    /// Parses expressions, including relational ones.
    fn parse_relational_expression(&mut self) -> Result<Expr, BcError> {
        let (left, left_h) = self.parse_expression_h()?;
        if self.current_token.token_type == TokenType::RelOp {
            let op = self.current_token.text();
            self.eat(TokenType::RelOp)?;
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
            let (op_prec, op_class, next_min_prec) = self.get_infix_info(&self.current_token);
            if op_prec < min_prec {
                break;
            }

            if op_class == "ASSIGN" {
                // Assignments to named expressions are parsed in `parse_primary`; anything
                // else on the left (`1 = 2`, `(a) = 2`, `a = 1 = 2`) is not assignable.
                return self.error("assignment to an expression that is not a named expression");
            }

            let op_val = self.current_token.text();
            self.eat(self.current_token.token_type)?;

            let (right, right_height) = self.parse_expr_precedence(next_min_prec)?;
            // A left-associative chain grows without recursion, so its height is checked here.
            height = self.check_height(1 + height.max(right_height))?;
            left = Expr::BinaryOp(BinOp::from_symbol(&op_val), Box::new(left), Box::new(right));
        }
        Ok((left, self.check_height(height)?))
    }

    /// Retrieves precedence info for binary and assignment operators.
    fn get_infix_info(&self, token: &Token) -> (i8, &'static str, i8) {
        let (tok_kind, op_class) = match token.token_type {
            TokenType::AssignOp => (TOK_ASSIGN_OP, "ASSIGN"),
            TokenType::Plus | TokenType::Minus => (TOK_PLUS_MINUS, "BINARY"),
            TokenType::MulOp => (TOK_MUL_OP, "BINARY"),
            TokenType::Exp => (TOK_EXP_OP, "BINARY"),
            _ => (0, ""),
        };
        let (op_prec, _right_assoc, next_min_prec) = verified_pratt_infix_info(tok_kind);
        (op_prec, op_class, next_min_prec)
    }

    /// Parses prefixes (unary operators).
    fn parse_prefix(&mut self) -> Result<(Expr, Height), BcError> {
        let t = self.current_token.token_type;
        if t == TokenType::Minus {
            self.eat(TokenType::Minus)?;
            let (expr, h) = self.parse_expr_precedence(5)?;
            Ok((Expr::Negate(Box::new(expr)), h + 1))
        } else if t == TokenType::IncrDecr {
            let op = self.current_token.text();
            self.eat(TokenType::IncrDecr)?;
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
        self.eat(TokenType::Lparen)?;
        let inner = self.parse_expression_h()?;
        self.eat(TokenType::Rparen)?;
        Ok(inner)
    }

    /// Parses primary expressions (literals, variables, built-ins, calls).
    fn parse_primary(&mut self) -> Result<(Expr, Height), BcError> {
        let t = self.current_token.token_type;
        match t {
            TokenType::Number => {
                let val = self.current_token.text();
                self.eat(TokenType::Number)?;
                Ok((Expr::Number(val), 1))
            }
            TokenType::Lparen => {
                let (expr, h) = self.parse_parenthesized()?;
                Ok((Expr::Paren(Box::new(expr)), h + 1))
            }
            TokenType::Length => {
                self.eat(TokenType::Length)?;
                let (expr, h) = self.parse_parenthesized()?;
                Ok((Expr::LengthCall(Box::new(expr)), h + 1))
            }
            TokenType::Sqrt => {
                self.eat(TokenType::Sqrt)?;
                let (expr, h) = self.parse_parenthesized()?;
                Ok((Expr::SqrtCall(Box::new(expr)), h + 1))
            }
            TokenType::Scale if self.peek_token_type(0)? == TokenType::Lparen => {
                self.eat(TokenType::Scale)?;
                let (expr, h) = self.parse_parenthesized()?;
                Ok((Expr::ScaleCall(Box::new(expr)), h + 1))
            }
            TokenType::Letter if self.peek_token_type(0)? == TokenType::Lparen => {
                let name = self.eat_name()?;
                self.eat(TokenType::Lparen)?;
                let (args, h) = self.parse_opt_argument_list()?;
                self.eat(TokenType::Rparen)?;
                Ok((Expr::Call(name, args), h + 1))
            }
            _ => {
                let (target, target_h) = self.parse_named_expression()?;
                match self.current_token.token_type {
                    TokenType::IncrDecr => {
                        let op = self.current_token.text();
                        self.eat(TokenType::IncrDecr)?;
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
                        self.eat(TokenType::AssignOp)?;
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
        }
    }

    /// Parses variables, arrays, or register accesses.
    fn parse_named_expression(&mut self) -> Result<(Expr, Height), BcError> {
        let t = self.current_token.token_type;
        match t {
            TokenType::Scale => {
                self.eat(TokenType::Scale)?;
                Ok((Expr::RegisterAccess(Register::Scale), 1))
            }
            TokenType::Ibase => {
                self.eat(TokenType::Ibase)?;
                Ok((Expr::RegisterAccess(Register::Ibase), 1))
            }
            TokenType::Obase => {
                self.eat(TokenType::Obase)?;
                Ok((Expr::RegisterAccess(Register::Obase), 1))
            }
            TokenType::Letter => {
                let name = self.eat_name()?;
                if self.current_token.token_type == TokenType::Lbracket {
                    self.eat(TokenType::Lbracket)?;
                    let (idx, h) = self.parse_expression_h()?;
                    self.eat(TokenType::Rbracket)?;
                    Ok((Expr::ArrayAccess(name, Box::new(idx)), h + 1))
                } else {
                    Ok((Expr::Variable(name), 1))
                }
            }
            _ => self.error(&format!("expected named expression, got {:?}", t)),
        }
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
                let name = self.eat_name()?;
                self.eat(TokenType::Lbracket)?;
                self.eat(TokenType::Rbracket)?;
                args.push(ExprOrArray::ArrayArg(name));
                height = height.max(1);
            } else {
                let (arg, h) = self.parse_expression_h()?;
                args.push(ExprOrArray::Expr(arg));
                height = height.max(h);
            }

            if self.current_token.token_type == TokenType::Comma {
                self.eat(TokenType::Comma)?;
            } else {
                break;
            }
        }
        Ok((args, height))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lexer_basic() {
        let mut lexer = Lexer::new(b"a = 10 + 20; /* comment */ a");
        let tokens = vec![
            (TokenType::Letter, "a"),
            (TokenType::AssignOp, "="),
            (TokenType::Number, "10"),
            (TokenType::Plus, "+"),
            (TokenType::Number, "20"),
            (TokenType::Semicolon, ";"),
            (TokenType::Letter, "a"),
            (TokenType::Eof, ""),
        ];
        for (expected_type, expected_val) in tokens {
            let tok = lexer.get_next_token();
            assert_eq!(tok.token_type, expected_type);
            assert_eq!(tok.value, expected_val.as_bytes());
        }
    }

    #[test]
    fn test_lexer_backslash_newline() {
        let mut lexer = Lexer::new(b"1.2\\\n34 + \\\n  5.0");
        let tok1 = lexer.get_next_token();
        assert_eq!(tok1.token_type, TokenType::Number);
        assert_eq!(tok1.value, b"1.234");

        let tok2 = lexer.get_next_token();
        assert_eq!(tok2.token_type, TokenType::Plus);

        let tok3 = lexer.get_next_token();
        assert_eq!(tok3.token_type, TokenType::Number);
        assert_eq!(tok3.value, b"5.0");
    }

    #[test]
    fn test_lexer_crlf_and_carriage_return() {
        let mut lexer = Lexer::new(b"a = 10\r\n + \r20");
        let tok1 = lexer.get_next_token();
        assert_eq!(tok1.token_type, TokenType::Letter);
        assert_eq!(tok1.value, b"a");

        let tok2 = lexer.get_next_token();
        assert_eq!(tok2.token_type, TokenType::AssignOp);

        let tok3 = lexer.get_next_token();
        assert_eq!(tok3.token_type, TokenType::Number);
        assert_eq!(tok3.value, b"10");

        let tok4 = lexer.get_next_token();
        assert_eq!(tok4.token_type, TokenType::Newline);

        let tok5 = lexer.get_next_token();
        assert_eq!(tok5.token_type, TokenType::Plus);

        let tok6 = lexer.get_next_token();
        assert_eq!(tok6.token_type, TokenType::Number);
        assert_eq!(tok6.value, b"20");

        let mut lexer2 = Lexer::new(b"1.2\\\r\n34");
        let tok_num = lexer2.get_next_token();
        assert_eq!(tok_num.token_type, TokenType::Number);
        assert_eq!(tok_num.value, b"1.234");

        // A number ends before a lone backslash and before an operator followed by CRLF.
        for (input, next_ok) in [(&b"12\\ 3"[..], false), (&b"12+\r\n"[..], true)] {
            let mut lexer = Lexer::new(input);
            let tok = lexer.get_next_token();
            assert_eq!(tok.token_type, TokenType::Number);
            assert_eq!(tok.value, b"12");
            let next = lexer.try_get_next_token();
            assert_eq!(next.is_ok(), next_ok);
            if let Ok(tok) = next {
                assert_eq!(tok.token_type, TokenType::Plus);
            }
        }

        let mut lexer3 = Lexer::new(b"\"hello \\\r\nworld\"");
        let tok_str = lexer3.get_next_token();
        assert_eq!(tok_str.token_type, TokenType::String);
        assert_eq!(tok_str.value, b"hello \\\r\nworld");
    }

    #[test]
    fn test_lexer_string_backslash_newline() {
        let mut lexer = Lexer::new(b"\"hello \\\nworld\"");
        let tok = lexer.get_next_token();
        assert_eq!(tok.token_type, TokenType::String);
        assert_eq!(tok.value, b"hello \\\nworld");
    }

    #[test]
    fn test_parser_arithmetic_precedence() {
        let lexer = Lexer::new(b"2 + 3 * 4");
        let mut parser = Parser::new(lexer);
        let prog = parser.parse_program();
        assert_eq!(prog.len(), 1);
        assert_eq!(
            prog[0],
            Stmt::Block(vec![Stmt::Expr(Expr::BinaryOp(
                BinOp::Add,
                Box::new(Expr::Number("2".to_string())),
                Box::new(Expr::BinaryOp(
                    BinOp::Mul,
                    Box::new(Expr::Number("3".to_string())),
                    Box::new(Expr::Number("4".to_string()))
                ))
            ))])
        );
    }

    #[test]
    #[should_panic(expected = "unterminated comment")]
    fn test_lexer_unterminated_comment() {
        let mut lexer = Lexer::new(b"/* unterminated");
        let _ = lexer.get_next_token();
    }

    fn parse_err(src: &str) -> BcError {
        Parser::try_new(Lexer::new(src.as_bytes()))
            .and_then(|mut p| p.try_parse_program())
            .unwrap_err()
    }

    #[test]
    fn test_misplaced_break_and_return_are_syntax_errors() {
        for (src, line, message) in [
            ("break\n", 1, "Break outside a for/while"),
            ("{ break }\n", 1, "Break outside a for/while"),
            ("define f() { break }\n", 1, "Break outside a for/while"),
            ("while (1) { define f() { break } }\n", 1, "syntax error"),
            ("return\n", 2, "Return outside of a function."),
            ("if (1) return (1)\n", 2, "Return outside of a function."),
        ] {
            match parse_err(src) {
                BcError::Syntax {
                    line: l,
                    message: m,
                    ..
                } => assert_eq!((l, m.as_str()), (line, message), "{src:?}"),
                other => panic!("{src:?}: {other:?}"),
            }
        }
        // POSIX allows `return ()`, which returns 0.
        let empty = Parser::new(Lexer::new(b"define f() {\nreturn ()\n}\n")).parse_program();
        assert!(matches!(&empty[0], Stmt::FunctionDef(f) if f.body == vec![Stmt::Return(None)]));
        // Allowed: break in a loop inside a function, return inside a loop in a function.
        let ok = "define f() { while (1) { break }; for (i = 0; 1; i++) return (1) }\n";
        assert!(
            Parser::try_new(Lexer::new(ok.as_bytes()))
                .and_then(|mut p| p.try_parse_program())
                .is_ok()
        );
    }

    #[test]
    fn test_assignment_binds_to_preceding_named_expression() {
        let parse = |src: &str| {
            let stmts = Parser::new(Lexer::new(src.as_bytes())).parse_program();
            match &stmts[0] {
                Stmt::Block(v) => match &v[0] {
                    Stmt::Expr(e) => e.clone(),
                    other => panic!("{other:?}"),
                },
                other => panic!("{other:?}"),
            }
        };
        let var = |n: &str| Box::new(Expr::Variable(n.to_string()));
        let num = |n: &str| Box::new(Expr::Number(n.to_string()));
        assert_eq!(
            parse("a + b = 3\n"),
            Expr::BinaryOp(
                BinOp::Add,
                var("a"),
                Box::new(Expr::AssignOp(AssignOp::Assign, var("b"), num("3")))
            )
        );
        assert_eq!(
            parse("-a = 5\n"),
            Expr::Negate(Box::new(Expr::AssignOp(
                AssignOp::Assign,
                var("a"),
                num("5")
            )))
        );
        assert_eq!(
            parse("(a = 5)\n"),
            Expr::Paren(Box::new(Expr::AssignOp(
                AssignOp::Assign,
                var("a"),
                num("5")
            )))
        );
        for src in [
            "A = 1\n",
            "1 = 2\n",
            "(a) = 2\n",
            "a = 1 = 2\n",
            "++a = 1\n",
        ] {
            assert!(
                matches!(parse_err(src), BcError::Syntax { .. }),
                "{src:?} must be a syntax error"
            );
        }
    }

    #[test]
    #[should_panic(expected = "quit")]
    fn test_parse_program_panics_with_quit() {
        let _ = Parser::new(Lexer::new(b"quit\n")).parse_program();
    }

    #[test]
    fn test_lexer_nul_and_control_characters_are_illegal_not_eof() {
        let syntax_message = |src: &[u8]| {
            let mut lexer = Lexer::new(src);
            loop {
                match lexer.try_get_next_token() {
                    Ok(tok) if tok.token_type == TokenType::Eof => return None,
                    Ok(_) => {}
                    Err(BcError::Syntax { line, message, .. }) => return Some((line, message)),
                    Err(e) => panic!("{e:?}"),
                }
            }
        };
        assert_eq!(
            syntax_message(b"3\x004\n"),
            Some((1, "illegal character: ^@".to_string()))
        );
        assert_eq!(
            syntax_message(b"\x01"),
            Some((1, "illegal character: ^A".to_string()))
        );
        assert_eq!(
            syntax_message(b"\x7f"),
            Some((1, "illegal character: \\177".to_string()))
        );
        assert_eq!(
            syntax_message("\u{e9}".as_bytes()),
            Some((1, "illegal character: \\303\\251".to_string()))
        );
        // A byte that does not start a well-formed UTF-8 sequence is a character of its own.
        for (src, shown) in [
            (&b"\xff"[..], "\\377"),
            (b"\x80", "\\200"),
            (b"\xc0\x80", "\\300"),
            (b"\xed\xa0\x80", "\\355"),
            (b"\xe2\x82", "\\342"),
            (b"\xf4\x90\x80\x80", "\\364"),
        ] {
            assert_eq!(
                syntax_message(src),
                Some((1, format!("illegal character: {shown}")))
            );
        }
        assert_eq!(
            syntax_message("\u{20ac}\u{1f600}".as_bytes()),
            Some((1, "illegal character: \\342\\202\\254".to_string()))
        );
        assert_eq!(
            syntax_message("\u{1f600}".as_bytes()),
            Some((1, "illegal character: \\360\\237\\230\\200".to_string()))
        );
        // Bytes that are not UTF-8 are kept in a string and skipped in a comment.
        let mut lexer = Lexer::new(b"\"a\xff\xed\xa0\x80\" /* \xff */");
        assert_eq!(lexer.get_next_token().value, b"a\xff\xed\xa0\x80");
        assert_eq!(lexer.get_next_token().token_type, TokenType::Eof);
        // A NUL inside a string or a comment does not end it.
        assert_eq!(syntax_message(b"\"a\0b\" /* \0 */ 1\n"), None);
        // An unterminated string is reported at the line where it starts.
        assert_eq!(
            syntax_message(b"1\n\"abc\nd\n"),
            Some((2, "illegal character: \"".to_string()))
        );
    }

    #[test]
    #[should_panic(expected = "illegal character")]
    fn test_lexer_unterminated_string() {
        let mut lexer = Lexer::new(b"\"unterminated");
        let _ = lexer.get_next_token();
    }

    #[test]
    #[should_panic(expected = "illegal character: @")]
    fn test_lexer_unexpected_char() {
        let mut lexer = Lexer::new(b"@");
        let _ = lexer.get_next_token();
    }

    #[test]
    #[should_panic(expected = "illegal character: !")]
    fn test_lexer_unexpected_bang() {
        let mut lexer = Lexer::new(b"!3");
        let _ = lexer.get_next_token();
    }

    #[test]
    fn test_lexer_advance_past_end() {
        let mut lexer = Lexer::new(b"abc");
        lexer.advance_char(10);
    }

    #[test]
    fn test_lexer_peek_past_eof() {
        let mut lexer = Lexer::new(b"123");
        let tok = lexer.peek_token(5);
        assert_eq!(tok.token_type, TokenType::Eof);
    }

    #[test]
    #[should_panic(expected = "expected")]
    fn test_parser_eat_mismatch() {
        let mut parser = Parser::new(Lexer::new(b"define f 123"));
        let _ = parser.parse_program();
    }

    #[test]
    #[should_panic(expected = "expected separator")]
    fn test_parser_expected_separator() {
        let mut parser = Parser::new(Lexer::new(b"{ a = 5 b = 10 }"));
        let _ = parser.parse_program();
    }

    #[test]
    #[should_panic(expected = "expected function name")]
    fn test_parser_expected_function_name() {
        let mut parser = Parser::new(Lexer::new(b"define 123() {}"));
        let _ = parser.parse_program();
    }

    #[test]
    #[should_panic(expected = "expected parameter name")]
    fn test_parser_expected_parameter_name() {
        let mut parser = Parser::new(Lexer::new(b"define f(123) {}"));
        let _ = parser.parse_program();
    }

    #[test]
    #[should_panic(expected = "expected newline or semicolon")]
    fn test_parser_expected_auto_separator() {
        let mut parser = Parser::new(Lexer::new(b"define f() { auto a 123; }"));
        let _ = parser.parse_program();
    }

    #[test]
    fn test_lexer_and_parser_mutant_edge_cases() {
        // 1. CRLF line tracking across comments and multi-line strings
        let mut lexer = Lexer::new(b"/* line 1\r\n line 2 */\r\n123");
        let tok1 = lexer.get_next_token();
        assert_eq!(tok1.token_type, TokenType::Newline);
        let tok2 = lexer.get_next_token();
        assert_eq!(tok2.token_type, TokenType::Number);
        assert_eq!(tok2.line, 3);

        // 2. Semicolons and empty statement list parsing
        let mut parser = Parser::new(Lexer::new(b"; ; a = 1; ; b = 2; ;"));
        let prog = parser.parse_program();
        assert!(!prog.is_empty());

        // 3. Complex argument list with expressions and array parameters
        let mut parser2 = Parser::new(Lexer::new(b"f(1 + 2, a[])"));
        let prog2 = parser2.parse_program();
        assert_eq!(prog2.len(), 1);

        // 4. Tokenizer operator coverage
        let ops = "+= -= *= /= %= ^= == != <= >= ++ --";
        let mut lexer_ops = Lexer::new(ops.as_bytes());
        let mut tok_count = 0;
        loop {
            let tok = lexer_ops.get_next_token();
            if tok.token_type == TokenType::Eof {
                break;
            }
            tok_count += 1;
        }
        assert_eq!(tok_count, 12);
    }

    #[test]
    fn test_string_backslash_newline_continuation_variations() {
        // String literal with backslash-LF and backslash-CRLF
        let mut lexer_lf = Lexer::new(b"\"hello \\\nworld\"");
        let tok_lf = lexer_lf.get_next_token();
        assert_eq!(tok_lf.token_type, TokenType::String);

        let mut lexer_crlf = Lexer::new(b"\"hello \\\r\nworld\"");
        let tok_crlf = lexer_crlf.get_next_token();
        assert_eq!(tok_crlf.token_type, TokenType::String);

        // Number token with backslash-newline continuation inside digits
        let mut lexer_num = Lexer::new(b"123\\\n456");
        let tok_num = lexer_num.get_next_token();
        assert_eq!(tok_num.token_type, TokenType::Number);
        assert_eq!(tok_num.value, b"123456");

        let mut lexer_num_crlf = Lexer::new(b"123\\\r\n456");
        let tok_num_crlf = lexer_num_crlf.get_next_token();
        assert_eq!(tok_num_crlf.token_type, TokenType::Number);
        assert_eq!(tok_num_crlf.value, b"123456");
    }

    #[test]
    fn test_parser_precedence_associativity_and_bare_return() {
        // 1. Right-associativity of exponentiation operator '^'
        let mut parser_pow = Parser::new(Lexer::new(b"2^3^2"));
        let stmts_pow = parser_pow.parse_program();
        assert_eq!(stmts_pow.len(), 1);
        let target_stmt = match &stmts_pow[0] {
            Stmt::Block(inner) => &inner[0],
            other => other,
        };
        if let Stmt::Expr(Expr::BinaryOp(op1, left1, right1)) = target_stmt {
            assert_eq!(*op1, BinOp::Pow);
            assert_eq!(**left1, Expr::Number("2".to_string()));
            if let Expr::BinaryOp(op2, left2, right2) = &**right1 {
                assert_eq!(*op2, BinOp::Pow);
                assert_eq!(**left2, Expr::Number("3".to_string()));
                assert_eq!(**right2, Expr::Number("2".to_string()));
            } else {
                panic!("Expected right-associative nested exponentiation");
            }
        } else {
            panic!("Expected BinaryOp statement");
        }

        // 2. Bare GNU return statement parsing
        let mut parser_ret = Parser::new(Lexer::new(b"define f() { return }"));
        let stmts_ret = parser_ret.parse_program();
        assert_eq!(stmts_ret.len(), 1);
        if let Stmt::FunctionDef(fdef) = &stmts_ret[0] {
            assert_eq!(fdef.body.len(), 1);
            assert_eq!(fdef.body[0], Stmt::Return(None));
        } else {
            panic!("Expected FunctionDef statement");
        }

        // 3. Multi-argument call with array and expression arguments
        let mut parser_call = Parser::new(Lexer::new(b"f(1, a[], 3)"));
        let stmts_call = parser_call.parse_program();
        assert_eq!(stmts_call.len(), 1);
        let call_stmt = match &stmts_call[0] {
            Stmt::Block(inner) => &inner[0],
            other => other,
        };
        if let Stmt::Expr(Expr::Call(name, args)) = call_stmt {
            assert_eq!(name, "f");
            assert_eq!(args.len(), 3);
        } else {
            panic!("Expected Call statement");
        }
    }

    #[test]
    fn test_lexer_token_boundaries_and_comment_transitions() {
        // 1. Comment-to-token transition scanning
        let mut lexer_comment = Lexer::new(b"/* comment */ x = 5");
        let tok1 = lexer_comment.get_next_token();
        assert_eq!(tok1.token_type, TokenType::Letter);
        assert_eq!(tok1.value, b"x");

        // 2. Minus operator vs negative numbers
        let mut lexer_minus = Lexer::new(b"x - 5");
        let _ = lexer_minus.get_next_token(); // x
        let tok_op = lexer_minus.get_next_token(); // -
        assert_eq!(tok_op.token_type, TokenType::Minus);

        // 3. Argument list parsing with multiple expressions
        let mut parser_args = Parser::new(Lexer::new(b"f(1 + 2, 3 * 4)"));
        let stmts_args = parser_args.parse_program();
        assert_eq!(stmts_args.len(), 1);
    }

    #[test]
    fn test_multi_array_parameter_call_parsing() {
        let mut parser_arrays = Parser::new(Lexer::new(b"f(x[], y[], z[])"));
        let stmts = parser_arrays.parse_program();
        assert_eq!(stmts.len(), 1);
        let call_stmt = match &stmts[0] {
            Stmt::Block(inner) => &inner[0],
            other => other,
        };
        if let Stmt::Expr(Expr::Call(name, args)) = call_stmt {
            assert_eq!(name, "f");
            assert_eq!(args.len(), 3);
            assert_eq!(args[0], ExprOrArray::ArrayArg("x".to_string()));
            assert_eq!(args[1], ExprOrArray::ArrayArg("y".to_string()));
            assert_eq!(args[2], ExprOrArray::ArrayArg("z".to_string()));
        } else {
            panic!("Expected Call statement with array parameters");
        }
    }

    #[test]
    fn test_lexer_crlf_continuation_and_newline_token_line() {
        // 1. A newline token reports the line after it, as GNU bc does for diagnostics
        let mut lexer_nl = Lexer::new(b"a\n");
        let _ = lexer_nl.get_next_token(); // a
        let tok_nl = lexer_nl.get_next_token(); // \n
        assert_eq!(tok_nl.token_type, TokenType::Newline);
        assert_eq!(tok_nl.line, 2);

        // 2. String token with CRLF backslash continuation
        let mut lexer_str = Lexer::new(b"\"hello \\\r\n world\"");
        let tok_str = lexer_str.get_next_token();
        assert_eq!(tok_str.token_type, TokenType::String);
        assert_eq!(tok_str.value, b"hello \\\r\n world");

        // 3. Number token with CRLF backslash continuation
        let mut lexer_num = Lexer::new(b"123\\\r\n456");
        let tok_num = lexer_num.get_next_token();
        assert_eq!(tok_num.token_type, TokenType::Number);
        assert_eq!(tok_num.value, b"123456");
    }

    #[test]
    fn test_argument_list_invalid_syntax_error_message() {
        let panic_res =
            std::panic::catch_unwind(|| Parser::new(Lexer::new(b"f(a + ])")).parse_program());
        assert!(panic_res.is_err());
        let payload = panic_res.unwrap_err();
        let msg = if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else if let Some(s) = payload.downcast_ref::<&str>() {
            s.to_string()
        } else {
            String::new()
        };
        assert!(!msg.contains("Lbracket"));
    }

    #[test]
    fn test_comment_slash_in_body_and_standalone_dot_token() {
        // 1. Comment with slash inside comment body: /* a / b */ 42
        let mut lexer_comment = Lexer::new(b"/* a / b */ 42");
        let tok_comment = lexer_comment.get_next_token();
        assert_eq!(tok_comment.token_type, TokenType::Number);
        assert_eq!(tok_comment.value, b"42");

        // 2. Standalone dot without trailing digit panics with unexpected character
        let panic_dot = std::panic::catch_unwind(|| {
            let mut lexer_dot = Lexer::new(b". + 1");
            let _ = lexer_dot.get_next_token();
        });
        assert!(panic_dot.is_err());
    }

    #[test]
    fn test_number_and_string_scan_token_crlf_short_circuit_precedence() {
        // Number token ending before newline: 123+\n
        let mut lexer_num = Lexer::new(b"123+\n");
        let tok_num = lexer_num.get_next_token();
        assert_eq!(tok_num.token_type, TokenType::Number);
        assert_eq!(tok_num.value, b"123");

        // String token with plus newline: "abc+\n"
        let mut lexer_str = Lexer::new(b"\"abc+\n\"");
        let tok_str = lexer_str.get_next_token();
        assert_eq!(tok_str.token_type, TokenType::String);
        assert_eq!(tok_str.value, b"abc+\n");

        // String token with unescaped CRLF (kills == vs != mutants on line 416)
        let mut lexer_raw_crlf = Lexer::new(b"\"a\r\nb\"");
        let tok_raw_crlf = lexer_raw_crlf.get_next_token();
        assert_eq!(tok_raw_crlf.token_type, TokenType::String);
        assert_eq!(tok_raw_crlf.value, b"a\r\nb");

        // Non-dot identifier followed by digit: x5 (kills == vs != on line 435)
        let mut lexer_x5 = Lexer::new(b"x5");
        let tok_x5 = lexer_x5.get_next_token();
        assert_eq!(tok_x5.token_type, TokenType::Letter);
        assert_eq!(tok_x5.value, b"x5");

        // Number token followed by space plus newline: 123 + \n (kills && vs || on line 449)
        let mut lexer_num_space = Lexer::new(b"123 + \n");
        let tok_num_space = lexer_num_space.get_next_token();
        assert_eq!(tok_num_space.token_type, TokenType::Number);
        assert_eq!(tok_num_space.value, b"123");

        // String token with backslash non-CRLF (kills line 416:59 and line 416:88)
        let mut lexer_str_bs_x = Lexer::new(b"\"a \\x\nb\"");
        let tok_str_bs_x = lexer_str_bs_x.get_next_token();
        assert_eq!(tok_str_bs_x.token_type, TokenType::String);
        assert_eq!(tok_str_bs_x.value, b"a \\x\nb");

        let mut lexer_str_bs_rx = Lexer::new(b"\"a \\\rxb\"");
        let tok_str_bs_rx = lexer_str_bs_rx.get_next_token();
        assert_eq!(tok_str_bs_rx.token_type, TokenType::String);
        assert_eq!(tok_str_bs_rx.value, b"a \\\rxb");

        // Number token followed by backslash x newline: 123 \x\n (kills line 449:38)
        let mut lexer_num_bs_x = Lexer::new(b"123 \\x\n");
        let tok_num_bs_x = lexer_num_bs_x.get_next_token();
        assert_eq!(tok_num_bs_x.token_type, TokenType::Number);
        assert_eq!(tok_num_bs_x.value, b"123");
    }

    #[test]
    fn test_fallible_parser_and_lexer() {
        let mut lexer_err = Lexer::new(b"@");
        assert!(lexer_err.try_get_next_token().is_err());

        let mut lexer_peek_err = Lexer::new(b"1 @");
        assert!(lexer_peek_err.try_peek_token(1).is_err());

        assert!(Parser::try_new(Lexer::new(b"/* unterminated")).is_err());

        let mut parser_syntax = Parser::try_new(Lexer::new(b"1 + * 2\n")).unwrap();
        assert!(parser_syntax.try_parse_program().is_err());

        let mut parser_quit = Parser::try_new(Lexer::new(b"quit\n")).unwrap();
        assert_eq!(parser_quit.try_parse_program(), Err(BcError::Quit));

        // Verify statement & primary expression variants in try_parse_program
        let mut parser_variants = Parser::try_new(Lexer::new(
            b"\"hello\"\nwhile (0) break\nif (1) x = 2\nlength(123)\nscale(1.23)\nobase = 16\nscale = 4\n",
        ))
        .unwrap();
        let stmts = parser_variants.try_parse_program().unwrap();
        assert_eq!(stmts.len(), 7);
        assert_eq!(
            stmts[0],
            Stmt::Block(vec![Stmt::StringLiteral(b"hello".to_vec())])
        );
        assert!(
            matches!(&stmts[1], Stmt::Block(v) if matches!(&v[0], Stmt::While(_, body) if **body == Stmt::Break))
        );
        assert!(matches!(&stmts[2], Stmt::Block(v) if matches!(&v[0], Stmt::If(_, _))));
        assert!(
            matches!(&stmts[3], Stmt::Block(v) if matches!(&v[0], Stmt::Expr(Expr::LengthCall(_))))
        );
        assert!(
            matches!(&stmts[4], Stmt::Block(v) if matches!(&v[0], Stmt::Expr(Expr::ScaleCall(_))))
        );
        assert!(
            matches!(&stmts[5], Stmt::Block(v) if matches!(&v[0], Stmt::Expr(Expr::AssignOp(_, t, _)) if **t == Expr::RegisterAccess(Register::Obase)))
        );
        assert!(
            matches!(&stmts[6], Stmt::Block(v) if matches!(&v[0], Stmt::Expr(Expr::AssignOp(_, t, _)) if **t == Expr::RegisterAccess(Register::Scale)))
        );
    }
}
