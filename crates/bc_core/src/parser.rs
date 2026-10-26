// SPDX-License-Identifier: MIT

//! Lexer, Parser, and Abstract Syntax Tree (AST) definitions for the bc clone.
//!
//! Conforms to standard POSIX bc lexical and syntax grammar rules, supporting
//! operator precedence climbing and backslash-newline continuation.

use crate::error::BcError;
use crate::verified_kernels::{
    TOK_ASSIGN_OP, TOK_EXP_OP, TOK_MUL_OP, TOK_PLUS_MINUS, verified_is_bc_digit,
    verified_is_ident_continue, verified_lexer_advance_step, verified_lexer_peek_char_index,
    verified_lexer_peek_token_index, verified_pratt_infix_info,
};
use alloc::boxed::Box;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

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
    pub value: String,
    pub line: usize,
}

/// An incremental lexical analyzer for the bc language.
pub struct Lexer {
    text: Vec<char>,
    pos: usize,
    pub line: usize,
    buffer: Vec<Token>,
}

impl Lexer {
    /// Creates a new Lexer from the source text.
    pub fn new(text: &str) -> Self {
        Self {
            text: text.chars().collect(),
            pos: 0,
            line: 1,
            buffer: Vec::new(),
        }
    }

    /// Triggers a syntax error during lexical analysis.
    fn error<T>(&self, msg: &str) -> Result<T, BcError> {
        Err(BcError::syntax(self.line, String::from(msg)))
    }

    /// Reports a character that cannot start any token, as GNU bc does.
    fn illegal_character<T>(&self, c: char) -> Result<T, BcError> {
        Err(BcError::Syntax {
            line: self.line,
            message: format!("illegal character: {}", c),
            detail: format!("unexpected character {:?}", c),
        })
    }

    /// Peeks a character ahead of the current position by the given offset.
    fn peek_char(&self, offset: usize) -> char {
        let (in_bounds, idx) = verified_lexer_peek_char_index(self.text.len(), self.pos, offset);
        if in_bounds { self.text[idx] } else { '\0' }
    }

    /// Advances the position pointer by `steps`.
    fn advance_char(&mut self, steps: usize) {
        for _ in 0..steps {
            if self.pos < self.text.len() {
                let (next_pos, next_line) =
                    verified_lexer_advance_step(self.pos, self.line, self.text[self.pos] == '\n');
                self.pos = next_pos;
                self.line = next_line;
            }
        }
    }

    /// Skips whitespace, comments (`/* ... */`), and backslash-newlines.
    fn skip_whitespace_and_comments(&mut self) -> Result<(), BcError> {
        loop {
            let c = self.peek_char(0);
            if c == ' ' || c == '\t' || c == '\r' {
                self.advance_char(1);
            } else if c == '\\' && self.peek_char(1) == '\n' {
                self.advance_char(2);
            } else if c == '\\' && self.peek_char(1) == '\r' && self.peek_char(2) == '\n' {
                self.advance_char(3);
            } else if c == '/' && self.peek_char(1) == '*' {
                self.advance_char(2);
                loop {
                    let cc = self.peek_char(0);
                    if cc == '\0' {
                        return self.error("unterminated comment");
                    }
                    if cc == '*' && self.peek_char(1) == '/' {
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
        let c = self.peek_char(0);
        if c == '\0' {
            return Ok(Token {
                token_type: TokenType::Eof,
                value: String::new(),
                line: self.line,
            });
        }

        if c == '\n' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Newline,
                value: "\n".to_string(),
                line: self.line,
            });
        }

        if c == ';' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Semicolon,
                value: ";".to_string(),
                line: self.line,
            });
        }
        if c == ',' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Comma,
                value: ",".to_string(),
                line: self.line,
            });
        }
        if c == '(' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Lparen,
                value: "(".to_string(),
                line: self.line,
            });
        }
        if c == ')' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Rparen,
                value: ")".to_string(),
                line: self.line,
            });
        }
        if c == '[' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Lbracket,
                value: "[".to_string(),
                line: self.line,
            });
        }
        if c == ']' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Rbracket,
                value: "]".to_string(),
                line: self.line,
            });
        }
        if c == '{' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Lbrace,
                value: "{".to_string(),
                line: self.line,
            });
        }
        if c == '}' {
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Rbrace,
                value: "}".to_string(),
                line: self.line,
            });
        }

        if c == '^' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: "^=".to_string(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Exp,
                value: "^".to_string(),
                line: self.line,
            });
        }

        if c == '+' {
            if self.peek_char(1) == '+' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::IncrDecr,
                    value: "++".to_string(),
                    line: self.line,
                });
            }
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: "+=".to_string(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Plus,
                value: "+".to_string(),
                line: self.line,
            });
        }

        if c == '-' {
            if self.peek_char(1) == '-' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::IncrDecr,
                    value: "--".to_string(),
                    line: self.line,
                });
            }
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: "-=".to_string(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::Minus,
                value: "-".to_string(),
                line: self.line,
            });
        }

        if c == '*' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: "*=".to_string(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::MulOp,
                value: "*".to_string(),
                line: self.line,
            });
        }

        if c == '/' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: "/=".to_string(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::MulOp,
                value: "/".to_string(),
                line: self.line,
            });
        }

        if c == '%' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::AssignOp,
                    value: "%=".to_string(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::MulOp,
                value: "%".to_string(),
                line: self.line,
            });
        }

        if c == '=' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::RelOp,
                    value: "==".to_string(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::AssignOp,
                value: "=".to_string(),
                line: self.line,
            });
        }

        if c == '<' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::RelOp,
                    value: "<=".to_string(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::RelOp,
                value: "<".to_string(),
                line: self.line,
            });
        }

        if c == '>' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::RelOp,
                    value: ">=".to_string(),
                    line: self.line,
                });
            }
            self.advance_char(1);
            return Ok(Token {
                token_type: TokenType::RelOp,
                value: ">".to_string(),
                line: self.line,
            });
        }

        if c == '!' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Ok(Token {
                    token_type: TokenType::RelOp,
                    value: "!=".to_string(),
                    line: self.line,
                });
            }
            return self.illegal_character('!');
        }

        if c == '"' {
            self.advance_char(1);
            let mut val_chars = Vec::new();
            loop {
                let cc = self.peek_char(0);
                if cc == '\0' {
                    return self.illegal_character('"');
                }
                if cc == '"' {
                    self.advance_char(1);
                    break;
                }
                if cc == '\\' && self.peek_char(1) == '\n' {
                    val_chars.push('\\');
                    val_chars.push('\n');
                    self.advance_char(2);
                } else if cc == '\\' && self.peek_char(1) == '\r' && self.peek_char(2) == '\n' {
                    val_chars.push('\\');
                    val_chars.push('\r');
                    val_chars.push('\n');
                    self.advance_char(3);
                } else {
                    val_chars.push(cc);
                    self.advance_char(1);
                }
            }
            return Ok(Token {
                token_type: TokenType::String,
                value: val_chars.into_iter().collect(),
                line: self.line,
            });
        }

        let is_digit = |ch: char| -> bool { verified_is_bc_digit(ch as u32) };

        if is_digit(c) || (c == '.' && is_digit(self.peek_char(1))) {
            let mut val_chars = Vec::new();
            let mut has_dot = false;
            loop {
                let cc = self.peek_char(0);
                if is_digit(cc) {
                    val_chars.push(cc);
                    self.advance_char(1);
                } else if cc == '.' && !has_dot {
                    has_dot = true;
                    val_chars.push(cc);
                    self.advance_char(1);
                } else if cc == '\\' && self.peek_char(1) == '\n' {
                    self.advance_char(2);
                } else if cc == '\\' && self.peek_char(1) == '\r' && self.peek_char(2) == '\n' {
                    self.advance_char(3);
                } else {
                    break;
                }
            }
            return Ok(Token {
                token_type: TokenType::Number,
                value: val_chars.into_iter().collect(),
                line: self.line,
            });
        }

        if c.is_ascii_lowercase() {
            let mut letters = vec![c];
            self.advance_char(1);
            loop {
                let peek = self.peek_char(0);
                if verified_is_ident_continue(peek as u32) {
                    letters.push(peek);
                    self.advance_char(1);
                } else {
                    break;
                }
            }
            let word: String = letters.into_iter().collect();

            let token_type = match word.as_str() {
                "auto" => TokenType::Auto,
                "break" => TokenType::Break,
                "define" => TokenType::Define,
                "ibase" => TokenType::Ibase,
                "if" => TokenType::If,
                "for" => TokenType::For,
                "length" => TokenType::Length,
                "obase" => TokenType::Obase,
                "quit" => TokenType::Quit,
                "return" => TokenType::Return,
                "scale" => TokenType::Scale,
                "sqrt" => TokenType::Sqrt,
                "while" => TokenType::While,
                _ => TokenType::Letter,
            };

            return Ok(Token {
                token_type,
                value: word,
                line: self.line,
            });
        }

        self.illegal_character(c)
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

impl Register {
    /// The register's name as written in bc source.
    pub fn name(self) -> &'static str {
        match self {
            Self::Scale => "scale",
            Self::Ibase => "ibase",
            Self::Obase => "obase",
        }
    }
}

/// Enum representing an expression in bc AST.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Number(String),
    Variable(String),
    ArrayAccess(String, Box<Expr>),
    RegisterAccess(Register),
    UnaryOp(char, Box<Expr>),
    BinaryOp(String, Box<Expr>, Box<Expr>),
    RelationalOp(String, Box<Expr>, Box<Expr>),
    UpdateOp(String, bool, Box<Expr>),      // op, is_prefix, target
    AssignOp(String, Box<Expr>, Box<Expr>), // op, target, expr
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
    StringLiteral(String),
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
}

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
        })
    }

    /// Creates a new Parser from the Lexer.
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
        let name = self.current_token.value.clone();
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
    fn parse_statement(&mut self) -> Result<Stmt, BcError> {
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
        let name = self.current_token.value.clone();
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
        let left = self.parse_expression()?;
        if self.current_token.token_type == TokenType::RelOp {
            let op = self.current_token.value.clone();
            self.eat(TokenType::RelOp)?;
            let right = self.parse_expression()?;
            Ok(Expr::RelationalOp(op, Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    /// Parses arithmetic expressions.
    fn parse_expression(&mut self) -> Result<Expr, BcError> {
        self.parse_expr_precedence(0)
    }

    /// Implements Precedence Climbing algorithm.
    fn parse_expr_precedence(&mut self, min_prec: i8) -> Result<Expr, BcError> {
        let mut left = self.parse_prefix()?;
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

            let op_val = self.current_token.value.clone();
            self.eat(self.current_token.token_type)?;

            let right = self.parse_expr_precedence(next_min_prec)?;
            left = Expr::BinaryOp(op_val, Box::new(left), Box::new(right));
        }
        Ok(left)
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
    fn parse_prefix(&mut self) -> Result<Expr, BcError> {
        let t = self.current_token.token_type;
        if t == TokenType::Minus {
            self.eat(TokenType::Minus)?;
            let expr = self.parse_expr_precedence(5)?;
            Ok(Expr::UnaryOp('-', Box::new(expr)))
        } else if t == TokenType::IncrDecr {
            let op = self.current_token.value.clone();
            self.eat(TokenType::IncrDecr)?;
            let target = self.parse_named_expression()?;
            Ok(Expr::UpdateOp(op, true, Box::new(target)))
        } else {
            self.parse_primary()
        }
    }

    /// Parses primary expressions (literals, variables, built-ins, calls).
    fn parse_primary(&mut self) -> Result<Expr, BcError> {
        let t = self.current_token.token_type;
        match t {
            TokenType::Number => {
                let val = self.current_token.value.clone();
                self.eat(TokenType::Number)?;
                Ok(Expr::Number(val))
            }
            TokenType::Lparen => {
                self.eat(TokenType::Lparen)?;
                let expr = self.parse_expression()?;
                self.eat(TokenType::Rparen)?;
                Ok(Expr::Paren(Box::new(expr)))
            }
            TokenType::Length => {
                self.eat(TokenType::Length)?;
                self.eat(TokenType::Lparen)?;
                let expr = self.parse_expression()?;
                self.eat(TokenType::Rparen)?;
                Ok(Expr::LengthCall(Box::new(expr)))
            }
            TokenType::Sqrt => {
                self.eat(TokenType::Sqrt)?;
                self.eat(TokenType::Lparen)?;
                let expr = self.parse_expression()?;
                self.eat(TokenType::Rparen)?;
                Ok(Expr::SqrtCall(Box::new(expr)))
            }
            TokenType::Scale if self.peek_token_type(0)? == TokenType::Lparen => {
                self.eat(TokenType::Scale)?;
                self.eat(TokenType::Lparen)?;
                let expr = self.parse_expression()?;
                self.eat(TokenType::Rparen)?;
                Ok(Expr::ScaleCall(Box::new(expr)))
            }
            TokenType::Letter if self.peek_token_type(0)? == TokenType::Lparen => {
                let name = self.eat_name()?;
                self.eat(TokenType::Lparen)?;
                let args = self.parse_opt_argument_list()?;
                self.eat(TokenType::Rparen)?;
                Ok(Expr::Call(name, args))
            }
            _ => {
                let target = self.parse_named_expression()?;
                match self.current_token.token_type {
                    TokenType::IncrDecr => {
                        let op = self.current_token.value.clone();
                        self.eat(TokenType::IncrDecr)?;
                        Ok(Expr::UpdateOp(op, false, Box::new(target)))
                    }
                    // As in GNU bc's grammar, an assignment operator binds to the named
                    // expression right before it: `a + b = 3` is `a + (b = 3)` and `-a = 5`
                    // is `-(a = 5)`. The right-hand side extends as far as possible.
                    TokenType::AssignOp => {
                        let op = self.current_token.value.clone();
                        self.eat(TokenType::AssignOp)?;
                        let (_, _, rhs_min_prec) = verified_pratt_infix_info(TOK_ASSIGN_OP);
                        let value = self.parse_expr_precedence(rhs_min_prec)?;
                        Ok(Expr::AssignOp(op, Box::new(target), Box::new(value)))
                    }
                    _ => Ok(target),
                }
            }
        }
    }

    /// Parses variables, arrays, or register accesses.
    fn parse_named_expression(&mut self) -> Result<Expr, BcError> {
        let t = self.current_token.token_type;
        match t {
            TokenType::Scale => {
                self.eat(TokenType::Scale)?;
                Ok(Expr::RegisterAccess(Register::Scale))
            }
            TokenType::Ibase => {
                self.eat(TokenType::Ibase)?;
                Ok(Expr::RegisterAccess(Register::Ibase))
            }
            TokenType::Obase => {
                self.eat(TokenType::Obase)?;
                Ok(Expr::RegisterAccess(Register::Obase))
            }
            TokenType::Letter => {
                let name = self.eat_name()?;
                if self.current_token.token_type == TokenType::Lbracket {
                    self.eat(TokenType::Lbracket)?;
                    let idx = self.parse_expression()?;
                    self.eat(TokenType::Rbracket)?;
                    Ok(Expr::ArrayAccess(name, Box::new(idx)))
                } else {
                    Ok(Expr::Variable(name))
                }
            }
            _ => self.error(&format!("expected named expression, got {:?}", t)),
        }
    }

    /// Parses optional function call argument list.
    fn parse_opt_argument_list(&mut self) -> Result<Vec<ExprOrArray>, BcError> {
        if self.current_token.token_type == TokenType::Rparen {
            Ok(Vec::new())
        } else {
            self.parse_argument_list()
        }
    }

    /// Parses function call argument list.
    fn parse_argument_list(&mut self) -> Result<Vec<ExprOrArray>, BcError> {
        let mut args = Vec::new();
        loop {
            if self.current_token.token_type == TokenType::Letter
                && self.peek_token_type(0)? == TokenType::Lbracket
                && self.peek_token_type(1)? == TokenType::Rbracket
            {
                let name = self.eat_name()?;
                self.eat(TokenType::Lbracket)?;
                self.eat(TokenType::Rbracket)?;
                args.push(ExprOrArray::ArrayArg(name));
            } else {
                args.push(ExprOrArray::Expr(self.parse_expression()?));
            }

            if self.current_token.token_type == TokenType::Comma {
                self.eat(TokenType::Comma)?;
            } else {
                break;
            }
        }
        Ok(args)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lexer_basic() {
        let mut lexer = Lexer::new("a = 10 + 20; /* comment */ a");
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
            assert_eq!(tok.value, expected_val);
        }
    }

    #[test]
    fn test_lexer_backslash_newline() {
        let mut lexer = Lexer::new("1.2\\\n34 + \\\n  5.0");
        let tok1 = lexer.get_next_token();
        assert_eq!(tok1.token_type, TokenType::Number);
        assert_eq!(tok1.value, "1.234");

        let tok2 = lexer.get_next_token();
        assert_eq!(tok2.token_type, TokenType::Plus);

        let tok3 = lexer.get_next_token();
        assert_eq!(tok3.token_type, TokenType::Number);
        assert_eq!(tok3.value, "5.0");
    }

    #[test]
    fn test_lexer_crlf_and_carriage_return() {
        let mut lexer = Lexer::new("a = 10\r\n + \r20");
        let tok1 = lexer.get_next_token();
        assert_eq!(tok1.token_type, TokenType::Letter);
        assert_eq!(tok1.value, "a");

        let tok2 = lexer.get_next_token();
        assert_eq!(tok2.token_type, TokenType::AssignOp);

        let tok3 = lexer.get_next_token();
        assert_eq!(tok3.token_type, TokenType::Number);
        assert_eq!(tok3.value, "10");

        let tok4 = lexer.get_next_token();
        assert_eq!(tok4.token_type, TokenType::Newline);

        let tok5 = lexer.get_next_token();
        assert_eq!(tok5.token_type, TokenType::Plus);

        let tok6 = lexer.get_next_token();
        assert_eq!(tok6.token_type, TokenType::Number);
        assert_eq!(tok6.value, "20");

        let mut lexer2 = Lexer::new("1.2\\\r\n34");
        let tok_num = lexer2.get_next_token();
        assert_eq!(tok_num.token_type, TokenType::Number);
        assert_eq!(tok_num.value, "1.234");

        let mut lexer3 = Lexer::new("\"hello \\\r\nworld\"");
        let tok_str = lexer3.get_next_token();
        assert_eq!(tok_str.token_type, TokenType::String);
        assert_eq!(tok_str.value, "hello \\\r\nworld");
    }

    #[test]
    fn test_lexer_string_backslash_newline() {
        let mut lexer = Lexer::new("\"hello \\\nworld\"");
        let tok = lexer.get_next_token();
        assert_eq!(tok.token_type, TokenType::String);
        assert_eq!(tok.value, "hello \\\nworld");
    }

    #[test]
    fn test_parser_arithmetic_precedence() {
        let lexer = Lexer::new("2 + 3 * 4");
        let mut parser = Parser::new(lexer);
        let prog = parser.parse_program();
        assert_eq!(prog.len(), 1);
        assert_eq!(
            prog[0],
            Stmt::Block(vec![Stmt::Expr(Expr::BinaryOp(
                "+".to_string(),
                Box::new(Expr::Number("2".to_string())),
                Box::new(Expr::BinaryOp(
                    "*".to_string(),
                    Box::new(Expr::Number("3".to_string())),
                    Box::new(Expr::Number("4".to_string()))
                ))
            ))])
        );
    }

    #[test]
    #[should_panic(expected = "unterminated comment")]
    fn test_lexer_unterminated_comment() {
        let mut lexer = Lexer::new("/* unterminated");
        let _ = lexer.get_next_token();
    }

    fn parse_err(src: &str) -> BcError {
        Parser::try_new(Lexer::new(src))
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
        let empty = Parser::new(Lexer::new("define f() {\nreturn ()\n}\n")).parse_program();
        assert!(matches!(&empty[0], Stmt::FunctionDef(f) if f.body == vec![Stmt::Return(None)]));
        // Allowed: break in a loop inside a function, return inside a loop in a function.
        let ok = "define f() { while (1) { break }; for (i = 0; 1; i++) return (1) }\n";
        assert!(
            Parser::try_new(Lexer::new(ok))
                .and_then(|mut p| p.try_parse_program())
                .is_ok()
        );
    }

    #[test]
    fn test_assignment_binds_to_preceding_named_expression() {
        let parse = |src: &str| {
            let stmts = Parser::new(Lexer::new(src)).parse_program();
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
                "+".to_string(),
                var("a"),
                Box::new(Expr::AssignOp("=".to_string(), var("b"), num("3")))
            )
        );
        assert_eq!(
            parse("-a = 5\n"),
            Expr::UnaryOp(
                '-',
                Box::new(Expr::AssignOp("=".to_string(), var("a"), num("5")))
            )
        );
        assert_eq!(
            parse("(a = 5)\n"),
            Expr::Paren(Box::new(Expr::AssignOp(
                "=".to_string(),
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
        let _ = Parser::new(Lexer::new("quit\n")).parse_program();
    }

    #[test]
    #[should_panic(expected = "illegal character")]
    fn test_lexer_unterminated_string() {
        let mut lexer = Lexer::new("\"unterminated");
        let _ = lexer.get_next_token();
    }

    #[test]
    #[should_panic(expected = "unexpected character")]
    fn test_lexer_unexpected_char() {
        let mut lexer = Lexer::new("@");
        let _ = lexer.get_next_token();
    }

    #[test]
    #[should_panic(expected = "unexpected character '!'")]
    fn test_lexer_unexpected_bang() {
        let mut lexer = Lexer::new("!3");
        let _ = lexer.get_next_token();
    }

    #[test]
    fn test_lexer_advance_past_end() {
        let mut lexer = Lexer::new("abc");
        lexer.advance_char(10);
    }

    #[test]
    fn test_lexer_peek_past_eof() {
        let mut lexer = Lexer::new("123");
        let tok = lexer.peek_token(5);
        assert_eq!(tok.token_type, TokenType::Eof);
    }

    #[test]
    #[should_panic(expected = "expected")]
    fn test_parser_eat_mismatch() {
        let mut parser = Parser::new(Lexer::new("define f 123"));
        let _ = parser.parse_program();
    }

    #[test]
    #[should_panic(expected = "expected separator")]
    fn test_parser_expected_separator() {
        let mut parser = Parser::new(Lexer::new("{ a = 5 b = 10 }"));
        let _ = parser.parse_program();
    }

    #[test]
    #[should_panic(expected = "expected function name")]
    fn test_parser_expected_function_name() {
        let mut parser = Parser::new(Lexer::new("define 123() {}"));
        let _ = parser.parse_program();
    }

    #[test]
    #[should_panic(expected = "expected parameter name")]
    fn test_parser_expected_parameter_name() {
        let mut parser = Parser::new(Lexer::new("define f(123) {}"));
        let _ = parser.parse_program();
    }

    #[test]
    #[should_panic(expected = "expected newline or semicolon")]
    fn test_parser_expected_auto_separator() {
        let mut parser = Parser::new(Lexer::new("define f() { auto a 123; }"));
        let _ = parser.parse_program();
    }

    #[test]
    fn test_lexer_and_parser_mutant_edge_cases() {
        // 1. CRLF line tracking across comments and multi-line strings
        let mut lexer = Lexer::new("/* line 1\r\n line 2 */\r\n123");
        let tok1 = lexer.get_next_token();
        assert_eq!(tok1.token_type, TokenType::Newline);
        let tok2 = lexer.get_next_token();
        assert_eq!(tok2.token_type, TokenType::Number);
        assert_eq!(tok2.line, 3);

        // 2. Semicolons and empty statement list parsing
        let mut parser = Parser::new(Lexer::new("; ; a = 1; ; b = 2; ;"));
        let prog = parser.parse_program();
        assert!(!prog.is_empty());

        // 3. Complex argument list with expressions and array parameters
        let mut parser2 = Parser::new(Lexer::new("f(1 + 2, a[])"));
        let prog2 = parser2.parse_program();
        assert_eq!(prog2.len(), 1);

        // 4. Tokenizer operator coverage
        let ops = "+= -= *= /= %= ^= == != <= >= ++ --";
        let mut lexer_ops = Lexer::new(ops);
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
        let mut lexer_lf = Lexer::new("\"hello \\\nworld\"");
        let tok_lf = lexer_lf.get_next_token();
        assert_eq!(tok_lf.token_type, TokenType::String);

        let mut lexer_crlf = Lexer::new("\"hello \\\r\nworld\"");
        let tok_crlf = lexer_crlf.get_next_token();
        assert_eq!(tok_crlf.token_type, TokenType::String);

        // Number token with backslash-newline continuation inside digits
        let mut lexer_num = Lexer::new("123\\\n456");
        let tok_num = lexer_num.get_next_token();
        assert_eq!(tok_num.token_type, TokenType::Number);
        assert_eq!(tok_num.value, "123456");

        let mut lexer_num_crlf = Lexer::new("123\\\r\n456");
        let tok_num_crlf = lexer_num_crlf.get_next_token();
        assert_eq!(tok_num_crlf.token_type, TokenType::Number);
        assert_eq!(tok_num_crlf.value, "123456");
    }

    #[test]
    fn test_parser_precedence_associativity_and_bare_return() {
        // 1. Right-associativity of exponentiation operator '^'
        let mut parser_pow = Parser::new(Lexer::new("2^3^2"));
        let stmts_pow = parser_pow.parse_program();
        assert_eq!(stmts_pow.len(), 1);
        let target_stmt = match &stmts_pow[0] {
            Stmt::Block(inner) => &inner[0],
            other => other,
        };
        if let Stmt::Expr(Expr::BinaryOp(op1, left1, right1)) = target_stmt {
            assert_eq!(op1, "^");
            assert_eq!(**left1, Expr::Number("2".to_string()));
            if let Expr::BinaryOp(op2, left2, right2) = &**right1 {
                assert_eq!(op2, "^");
                assert_eq!(**left2, Expr::Number("3".to_string()));
                assert_eq!(**right2, Expr::Number("2".to_string()));
            } else {
                panic!("Expected right-associative nested exponentiation");
            }
        } else {
            panic!("Expected BinaryOp statement");
        }

        // 2. Bare GNU return statement parsing
        let mut parser_ret = Parser::new(Lexer::new("define f() { return }"));
        let stmts_ret = parser_ret.parse_program();
        assert_eq!(stmts_ret.len(), 1);
        if let Stmt::FunctionDef(fdef) = &stmts_ret[0] {
            assert_eq!(fdef.body.len(), 1);
            assert_eq!(fdef.body[0], Stmt::Return(None));
        } else {
            panic!("Expected FunctionDef statement");
        }

        // 3. Multi-argument call with array and expression arguments
        let mut parser_call = Parser::new(Lexer::new("f(1, a[], 3)"));
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
        let mut lexer_comment = Lexer::new("/* comment */ x = 5");
        let tok1 = lexer_comment.get_next_token();
        assert_eq!(tok1.token_type, TokenType::Letter);
        assert_eq!(tok1.value, "x");

        // 2. Minus operator vs negative numbers
        let mut lexer_minus = Lexer::new("x - 5");
        let _ = lexer_minus.get_next_token(); // x
        let tok_op = lexer_minus.get_next_token(); // -
        assert_eq!(tok_op.token_type, TokenType::Minus);

        // 3. Argument list parsing with multiple expressions
        let mut parser_args = Parser::new(Lexer::new("f(1 + 2, 3 * 4)"));
        let stmts_args = parser_args.parse_program();
        assert_eq!(stmts_args.len(), 1);
    }

    #[test]
    fn test_multi_array_parameter_call_parsing() {
        let mut parser_arrays = Parser::new(Lexer::new("f(x[], y[], z[])"));
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
        let mut lexer_nl = Lexer::new("a\n");
        let _ = lexer_nl.get_next_token(); // a
        let tok_nl = lexer_nl.get_next_token(); // \n
        assert_eq!(tok_nl.token_type, TokenType::Newline);
        assert_eq!(tok_nl.line, 2);

        // 2. String token with CRLF backslash continuation
        let mut lexer_str = Lexer::new("\"hello \\\r\n world\"");
        let tok_str = lexer_str.get_next_token();
        assert_eq!(tok_str.token_type, TokenType::String);
        assert_eq!(tok_str.value, "hello \\\r\n world");

        // 3. Number token with CRLF backslash continuation
        let mut lexer_num = Lexer::new("123\\\r\n456");
        let tok_num = lexer_num.get_next_token();
        assert_eq!(tok_num.token_type, TokenType::Number);
        assert_eq!(tok_num.value, "123456");
    }

    #[test]
    fn test_argument_list_invalid_syntax_error_message() {
        let panic_res =
            std::panic::catch_unwind(|| Parser::new(Lexer::new("f(a + ])")).parse_program());
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
        let mut lexer_comment = Lexer::new("/* a / b */ 42");
        let tok_comment = lexer_comment.get_next_token();
        assert_eq!(tok_comment.token_type, TokenType::Number);
        assert_eq!(tok_comment.value, "42");

        // 2. Standalone dot without trailing digit panics with unexpected character
        let panic_dot = std::panic::catch_unwind(|| {
            let mut lexer_dot = Lexer::new(". + 1");
            let _ = lexer_dot.get_next_token();
        });
        assert!(panic_dot.is_err());
    }

    #[test]
    fn test_number_and_string_scan_token_crlf_short_circuit_precedence() {
        // Number token ending before newline: 123+\n
        let mut lexer_num = Lexer::new("123+\n");
        let tok_num = lexer_num.get_next_token();
        assert_eq!(tok_num.token_type, TokenType::Number);
        assert_eq!(tok_num.value, "123");

        // String token with plus newline: "abc+\n"
        let mut lexer_str = Lexer::new("\"abc+\n\"");
        let tok_str = lexer_str.get_next_token();
        assert_eq!(tok_str.token_type, TokenType::String);
        assert_eq!(tok_str.value, "abc+\n");

        // String token with unescaped CRLF (kills == vs != mutants on line 416)
        let mut lexer_raw_crlf = Lexer::new("\"a\r\nb\"");
        let tok_raw_crlf = lexer_raw_crlf.get_next_token();
        assert_eq!(tok_raw_crlf.token_type, TokenType::String);
        assert_eq!(tok_raw_crlf.value, "a\r\nb");

        // Non-dot identifier followed by digit: x5 (kills == vs != on line 435)
        let mut lexer_x5 = Lexer::new("x5");
        let tok_x5 = lexer_x5.get_next_token();
        assert_eq!(tok_x5.token_type, TokenType::Letter);
        assert_eq!(tok_x5.value, "x5");

        // Number token followed by space plus newline: 123 + \n (kills && vs || on line 449)
        let mut lexer_num_space = Lexer::new("123 + \n");
        let tok_num_space = lexer_num_space.get_next_token();
        assert_eq!(tok_num_space.token_type, TokenType::Number);
        assert_eq!(tok_num_space.value, "123");

        // String token with backslash non-CRLF (kills line 416:59 and line 416:88)
        let mut lexer_str_bs_x = Lexer::new("\"a \\x\nb\"");
        let tok_str_bs_x = lexer_str_bs_x.get_next_token();
        assert_eq!(tok_str_bs_x.token_type, TokenType::String);
        assert_eq!(tok_str_bs_x.value, "a \\x\nb");

        let mut lexer_str_bs_rx = Lexer::new("\"a \\\rxb\"");
        let tok_str_bs_rx = lexer_str_bs_rx.get_next_token();
        assert_eq!(tok_str_bs_rx.token_type, TokenType::String);
        assert_eq!(tok_str_bs_rx.value, "a \\\rxb");

        // Number token followed by backslash x newline: 123 \x\n (kills line 449:38)
        let mut lexer_num_bs_x = Lexer::new("123 \\x\n");
        let tok_num_bs_x = lexer_num_bs_x.get_next_token();
        assert_eq!(tok_num_bs_x.token_type, TokenType::Number);
        assert_eq!(tok_num_bs_x.value, "123");
    }

    #[test]
    fn test_fallible_parser_and_lexer() {
        let mut lexer_err = Lexer::new("@");
        assert!(lexer_err.try_get_next_token().is_err());

        let mut lexer_peek_err = Lexer::new("1 @");
        assert!(lexer_peek_err.try_peek_token(1).is_err());

        assert!(Parser::try_new(Lexer::new("/* unterminated")).is_err());

        let mut parser_syntax = Parser::try_new(Lexer::new("1 + * 2\n")).unwrap();
        assert!(parser_syntax.try_parse_program().is_err());

        let mut parser_quit = Parser::try_new(Lexer::new("quit\n")).unwrap();
        assert_eq!(parser_quit.try_parse_program(), Err(BcError::Quit));

        // Verify statement & primary expression variants in try_parse_program
        let mut parser_variants = Parser::try_new(Lexer::new(
            "\"hello\"\nwhile (0) break\nif (1) x = 2\nlength(123)\nscale(1.23)\nobase = 16\nscale = 4\n",
        ))
        .unwrap();
        let stmts = parser_variants.try_parse_program().unwrap();
        assert_eq!(stmts.len(), 7);
        assert_eq!(
            stmts[0],
            Stmt::Block(vec![Stmt::StringLiteral("hello".to_string())])
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
