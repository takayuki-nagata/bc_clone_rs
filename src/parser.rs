//! Lexer, Parser, and Abstract Syntax Tree (AST) definitions for the bc clone.
//!
//! Conforms to standard POSIX bc lexical and syntax grammar rules, supporting
//! operator precedence climbing and backslash-newline continuation.

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
    fn error(&self, msg: &str) -> ! {
        panic!("Lexical error on line {}: {}", self.line, msg);
    }

    /// Peeks a character ahead of the current position by the given offset.
    fn peek_char(&self, offset: usize) -> char {
        let idx = self.pos + offset;
        if idx >= self.text.len() {
            '\0'
        } else {
            self.text[idx]
        }
    }

    /// Advances the position pointer by `steps`.
    fn advance_char(&mut self, steps: usize) {
        for _ in 0..steps {
            if self.pos < self.text.len() {
                if self.text[self.pos] == '\n' {
                    self.line += 1;
                }
                self.pos += 1;
            }
        }
    }

    /// Skips whitespace, comments (`/* ... */`), and backslash-newlines.
    fn skip_whitespace_and_comments(&mut self) {
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
                        self.error("unterminated comment");
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
    }

    /// Scans the next token from input.
    fn scan_token(&mut self) -> Token {
        self.skip_whitespace_and_comments();
        let c = self.peek_char(0);
        if c == '\0' {
            return Token {
                token_type: TokenType::Eof,
                value: String::new(),
                line: self.line,
            };
        }

        if c == '\n' {
            self.advance_char(1);
            return Token {
                token_type: TokenType::Newline,
                value: "\n".to_string(),
                line: self.line - 1,
            };
        }

        if c == ';' {
            self.advance_char(1);
            return Token {
                token_type: TokenType::Semicolon,
                value: ";".to_string(),
                line: self.line,
            };
        }
        if c == ',' {
            self.advance_char(1);
            return Token {
                token_type: TokenType::Comma,
                value: ",".to_string(),
                line: self.line,
            };
        }
        if c == '(' {
            self.advance_char(1);
            return Token {
                token_type: TokenType::Lparen,
                value: "(".to_string(),
                line: self.line,
            };
        }
        if c == ')' {
            self.advance_char(1);
            return Token {
                token_type: TokenType::Rparen,
                value: ")".to_string(),
                line: self.line,
            };
        }
        if c == '[' {
            self.advance_char(1);
            return Token {
                token_type: TokenType::Lbracket,
                value: "[".to_string(),
                line: self.line,
            };
        }
        if c == ']' {
            self.advance_char(1);
            return Token {
                token_type: TokenType::Rbracket,
                value: "]".to_string(),
                line: self.line,
            };
        }
        if c == '{' {
            self.advance_char(1);
            return Token {
                token_type: TokenType::Lbrace,
                value: "{".to_string(),
                line: self.line,
            };
        }
        if c == '}' {
            self.advance_char(1);
            return Token {
                token_type: TokenType::Rbrace,
                value: "}".to_string(),
                line: self.line,
            };
        }

        if c == '^' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::AssignOp,
                    value: "^=".to_string(),
                    line: self.line,
                };
            }
            self.advance_char(1);
            return Token {
                token_type: TokenType::Exp,
                value: "^".to_string(),
                line: self.line,
            };
        }

        if c == '+' {
            if self.peek_char(1) == '+' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::IncrDecr,
                    value: "++".to_string(),
                    line: self.line,
                };
            }
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::AssignOp,
                    value: "+=".to_string(),
                    line: self.line,
                };
            }
            self.advance_char(1);
            return Token {
                token_type: TokenType::Plus,
                value: "+".to_string(),
                line: self.line,
            };
        }

        if c == '-' {
            if self.peek_char(1) == '-' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::IncrDecr,
                    value: "--".to_string(),
                    line: self.line,
                };
            }
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::AssignOp,
                    value: "-=".to_string(),
                    line: self.line,
                };
            }
            self.advance_char(1);
            return Token {
                token_type: TokenType::Minus,
                value: "-".to_string(),
                line: self.line,
            };
        }

        if c == '*' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::AssignOp,
                    value: "*=".to_string(),
                    line: self.line,
                };
            }
            self.advance_char(1);
            return Token {
                token_type: TokenType::MulOp,
                value: "*".to_string(),
                line: self.line,
            };
        }

        if c == '/' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::AssignOp,
                    value: "/=".to_string(),
                    line: self.line,
                };
            }
            self.advance_char(1);
            return Token {
                token_type: TokenType::MulOp,
                value: "/".to_string(),
                line: self.line,
            };
        }

        if c == '%' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::AssignOp,
                    value: "%=".to_string(),
                    line: self.line,
                };
            }
            self.advance_char(1);
            return Token {
                token_type: TokenType::MulOp,
                value: "%".to_string(),
                line: self.line,
            };
        }

        if c == '=' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::RelOp,
                    value: "==".to_string(),
                    line: self.line,
                };
            }
            self.advance_char(1);
            return Token {
                token_type: TokenType::AssignOp,
                value: "=".to_string(),
                line: self.line,
            };
        }

        if c == '<' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::RelOp,
                    value: "<=".to_string(),
                    line: self.line,
                };
            }
            self.advance_char(1);
            return Token {
                token_type: TokenType::RelOp,
                value: "<".to_string(),
                line: self.line,
            };
        }

        if c == '>' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::RelOp,
                    value: ">=".to_string(),
                    line: self.line,
                };
            }
            self.advance_char(1);
            return Token {
                token_type: TokenType::RelOp,
                value: ">".to_string(),
                line: self.line,
            };
        }

        if c == '!' {
            if self.peek_char(1) == '=' {
                self.advance_char(2);
                return Token {
                    token_type: TokenType::RelOp,
                    value: "!=".to_string(),
                    line: self.line,
                };
            }
            self.error("unexpected character '!'");
        }

        if c == '"' {
            self.advance_char(1);
            let mut val_chars = Vec::new();
            loop {
                let cc = self.peek_char(0);
                if cc == '\0' {
                    self.error("unterminated string");
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
            return Token {
                token_type: TokenType::String,
                value: val_chars.into_iter().collect(),
                line: self.line,
            };
        }

        let is_digit = |ch: char| -> bool { ch.is_ascii_digit() || ('A'..='F').contains(&ch) };

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
            return Token {
                token_type: TokenType::Number,
                value: val_chars.into_iter().collect(),
                line: self.line,
            };
        }

        if c.is_ascii_lowercase() {
            let mut letters = vec![c];
            self.advance_char(1);
            loop {
                let peek = self.peek_char(0);
                if peek.is_ascii_lowercase() || peek.is_ascii_digit() || peek == '_' {
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

            return Token {
                token_type,
                value: word,
                line: self.line,
            };
        }

        self.error(&format!("unexpected character {:?}", c));
    }

    /// Obtains the next token, consuming it from the buffer or stream.
    pub fn get_next_token(&mut self) -> Token {
        if !self.buffer.is_empty() {
            self.buffer.remove(0)
        } else {
            self.scan_token()
        }
    }

    /// Peeks a token at a given offset forward.
    pub fn peek_token(&mut self, offset: usize) -> &Token {
        while self.buffer.len() <= offset {
            let tok = self.scan_token();
            let is_eof = tok.token_type == TokenType::Eof;
            self.buffer.push(tok);
            if is_eof {
                break;
            }
        }
        let idx = std::cmp::min(offset, self.buffer.len() - 1);
        &self.buffer[idx]
    }
}

// --- AST Node Definitions ---

/// Struct representing a formal parameter or local auto variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub is_array: bool,
}

/// Enum representing an expression in bc AST.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Number(String),
    Variable(String),
    ArrayAccess(String, Box<Expr>),
    RegisterAccess(String), // "scale", "ibase", "obase"
    UnaryOp(char, Box<Expr>),
    BinaryOp(String, Box<Expr>, Box<Expr>),
    RelationalOp(String, Box<Expr>, Box<Expr>),
    UpdateOp(String, bool, Box<Expr>),      // op, is_prefix, target
    AssignOp(String, Box<Expr>, Box<Expr>), // op, target, expr
    Call(String, Vec<ExprOrArray>),
    LengthCall(Box<Expr>),
    SqrtCall(Box<Expr>),
    ScaleCall(Box<Expr>),
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

/// Recursive descent parser with operator precedence support for bc.
pub struct Parser {
    pub lexer: Lexer,
    current_token: Token,
}

impl Parser {
    /// Creates a new Parser from the Lexer.
    pub fn new(mut lexer: Lexer) -> Self {
        let current_token = lexer.get_next_token();
        Self {
            lexer,
            current_token,
        }
    }

    /// Triggers a syntax error during parsing.
    fn error(&self, msg: &str) -> ! {
        panic!("Parser error on line {}: {}", self.current_token.line, msg);
    }

    /// Consumes a token of the expected type, otherwise raises error.
    fn eat(&mut self, token_type: TokenType) {
        if self.current_token.token_type == token_type {
            self.current_token = self.lexer.get_next_token();
        } else {
            self.error(&format!(
                "expected {:?}, got {:?}",
                token_type, self.current_token.token_type
            ));
        }
    }

    /// Peeks the token type of the token at `offset`.
    fn peek_token_type(&mut self, offset: usize) -> TokenType {
        self.lexer.peek_token(offset).token_type
    }

    /// Parses the program fully (entry point).
    pub fn parse_program(&mut self) -> Vec<Stmt> {
        let mut items = Vec::new();
        while self.current_token.token_type != TokenType::Eof {
            if let Some(item) = self.parse_input_item() {
                items.push(item);
            }
        }
        items
    }

    /// Parses a single top-level item (statement block or function definition).
    fn parse_input_item(&mut self) -> Option<Stmt> {
        if self.current_token.token_type == TokenType::Define {
            return Some(self.parse_function());
        }

        let lst = self.parse_semicolon_list();
        if self.current_token.token_type == TokenType::Newline {
            self.eat(TokenType::Newline);
        } else {
            self.eat(TokenType::Eof);
        }

        if lst.is_empty() {
            None
        } else {
            Some(Stmt::Block(lst))
        }
    }

    /// Parses a list of statements separated by semicolons.
    fn parse_semicolon_list(&mut self) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        loop {
            let t = self.current_token.token_type;
            if t == TokenType::Newline || t == TokenType::Eof || t == TokenType::Rbrace {
                break;
            }
            if t == TokenType::Semicolon {
                self.eat(TokenType::Semicolon);
                continue;
            }

            let stmt = self.parse_statement();
            stmts.push(stmt);

            if self.current_token.token_type == TokenType::Semicolon {
                self.eat(TokenType::Semicolon);
            } else {
                break;
            }
        }
        stmts
    }

    /// Parses a list of statements within a block (with newline and semicolon separations).
    fn parse_statement_list(&mut self) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        loop {
            self.skip_newlines();
            let t = self.current_token.token_type;
            if t == TokenType::Eof || t == TokenType::Rbrace {
                break;
            }

            let stmt = self.parse_statement();
            stmts.push(stmt);

            let nt = self.current_token.token_type;
            match nt {
                TokenType::Semicolon => {
                    self.eat(TokenType::Semicolon);
                }
                TokenType::Newline => {
                    self.eat(TokenType::Newline);
                }
                TokenType::Rbrace | TokenType::Eof => {}
                _ => self.error(&format!("expected separator, got {:?}", nt)),
            }
        }
        stmts
    }

    /// Skips sequence of newline tokens.
    fn skip_newlines(&mut self) {
        while self.current_token.token_type == TokenType::Newline {
            self.eat(TokenType::Newline);
        }
    }

    /// Parses a statement.
    fn parse_statement(&mut self) -> Stmt {
        let t = self.current_token.token_type;
        match t {
            TokenType::String => {
                let val = self.current_token.value.clone();
                self.eat(TokenType::String);
                Stmt::StringLiteral(val)
            }
            TokenType::Break => {
                self.eat(TokenType::Break);
                Stmt::Break
            }
            TokenType::Quit => {
                panic!("quit");
            }
            TokenType::Return => {
                self.eat(TokenType::Return);
                if self.current_token.token_type == TokenType::Lparen {
                    self.eat(TokenType::Lparen);
                    let expr = self.parse_expression();
                    self.eat(TokenType::Rparen);
                    Stmt::Return(Some(expr))
                } else {
                    // GNU extension: return without parentheses
                    let nt = self.current_token.token_type;
                    if nt != TokenType::Newline
                        && nt != TokenType::Semicolon
                        && nt != TokenType::Rbrace
                        && nt != TokenType::Eof
                    {
                        let expr = self.parse_expression();
                        Stmt::Return(Some(expr))
                    } else {
                        Stmt::Return(None)
                    }
                }
            }
            TokenType::For => {
                self.eat(TokenType::For);
                self.eat(TokenType::Lparen);
                let init = self.parse_expression();
                self.eat(TokenType::Semicolon);
                let cond = self.parse_relational_expression();
                self.eat(TokenType::Semicolon);
                let post = self.parse_expression();
                self.eat(TokenType::Rparen);
                let body = self.parse_statement();
                Stmt::For(init, cond, post, Box::new(body))
            }
            TokenType::If => {
                self.eat(TokenType::If);
                self.eat(TokenType::Lparen);
                let cond = self.parse_relational_expression();
                self.eat(TokenType::Rparen);
                let body = self.parse_statement();
                Stmt::If(cond, Box::new(body))
            }
            TokenType::While => {
                self.eat(TokenType::While);
                self.eat(TokenType::Lparen);
                let cond = self.parse_relational_expression();
                self.eat(TokenType::Rparen);
                let body = self.parse_statement();
                Stmt::While(cond, Box::new(body))
            }
            TokenType::Lbrace => {
                self.eat(TokenType::Lbrace);
                let stmts = self.parse_statement_list();
                self.eat(TokenType::Rbrace);
                Stmt::Block(stmts)
            }
            _ => Stmt::Expr(self.parse_relational_expression()),
        }
    }

    /// Parses a function definition `define f(x) { ... }`.
    fn parse_function(&mut self) -> Stmt {
        self.eat(TokenType::Define);
        if self.current_token.token_type != TokenType::Letter {
            self.error("expected function name (letter)");
        }
        let name = self.current_token.value.clone();
        self.eat(TokenType::Letter);

        self.eat(TokenType::Lparen);
        let params = self.parse_opt_define_list();
        self.eat(TokenType::Rparen);

        self.eat(TokenType::Lbrace);
        self.skip_newlines();

        let autos = self.parse_opt_auto_define_list();
        let body = self.parse_statement_list();
        self.eat(TokenType::Rbrace);

        Stmt::FunctionDef(FunctionDef {
            name,
            params,
            autos,
            body,
        })
    }

    /// Parses optional parameters/autos define list.
    fn parse_opt_define_list(&mut self) -> Vec<Param> {
        if self.current_token.token_type == TokenType::Rparen {
            Vec::new()
        } else {
            self.parse_define_list()
        }
    }

    /// Parses a define list of parameters or auto variables.
    fn parse_define_list(&mut self) -> Vec<Param> {
        let mut lst = Vec::new();
        loop {
            if self.current_token.token_type != TokenType::Letter {
                self.error("expected parameter name (letter)");
            }
            let pname = self.current_token.value.clone();
            self.eat(TokenType::Letter);
            let mut is_arr = false;
            if self.current_token.token_type == TokenType::Lbracket {
                self.eat(TokenType::Lbracket);
                self.eat(TokenType::Rbracket);
                is_arr = true;
            }
            lst.push(Param {
                name: pname,
                is_array: is_arr,
            });

            if self.current_token.token_type == TokenType::Comma {
                self.eat(TokenType::Comma);
            } else {
                break;
            }
        }
        lst
    }

    /// Parses auto list declarations `auto a, b[]`.
    fn parse_opt_auto_define_list(&mut self) -> Vec<Param> {
        if self.current_token.token_type != TokenType::Auto {
            return Vec::new();
        }
        self.eat(TokenType::Auto);
        let lst = self.parse_define_list();
        let t = self.current_token.token_type;
        if t == TokenType::Newline {
            self.eat(TokenType::Newline);
        } else if t == TokenType::Semicolon {
            self.eat(TokenType::Semicolon);
        } else {
            self.error("expected newline or semicolon after auto declaration");
        }
        lst
    }

    /// Parses expressions, including relational ones.
    fn parse_relational_expression(&mut self) -> Expr {
        let left = self.parse_expression();
        if self.current_token.token_type == TokenType::RelOp {
            let op = self.current_token.value.clone();
            self.eat(TokenType::RelOp);
            let right = self.parse_expression();
            Expr::RelationalOp(op, Box::new(left), Box::new(right))
        } else {
            left
        }
    }

    /// Parses arithmetic expressions.
    fn parse_expression(&mut self) -> Expr {
        self.parse_expr_precedence(0)
    }

    /// Implements Precedence Climbing algorithm.
    fn parse_expr_precedence(&mut self, min_prec: i8) -> Expr {
        let mut left = self.parse_prefix();
        loop {
            let (op_prec, op_class, right_assoc) = self.get_infix_info(&self.current_token);
            if op_prec < min_prec {
                break;
            }

            let op_val = self.current_token.value.clone();
            self.eat(self.current_token.token_type);

            let next_min_prec = if right_assoc { op_prec } else { op_prec + 1 };
            let right = self.parse_expr_precedence(next_min_prec);

            left = if op_class == "ASSIGN" {
                Expr::AssignOp(op_val, Box::new(left), Box::new(right))
            } else {
                Expr::BinaryOp(op_val, Box::new(left), Box::new(right))
            };
        }
        left
    }

    /// Retrieves precedence info for binary and assignment operators.
    fn get_infix_info(&self, token: &Token) -> (i8, &'static str, bool) {
        match token.token_type {
            TokenType::AssignOp => (1, "ASSIGN", true),
            TokenType::Plus | TokenType::Minus => (2, "BINARY", false),
            TokenType::MulOp => (3, "BINARY", false),
            TokenType::Exp => (4, "BINARY", true),
            _ => (-1, "", false),
        }
    }

    /// Parses prefixes (unary operators).
    fn parse_prefix(&mut self) -> Expr {
        let t = self.current_token.token_type;
        if t == TokenType::Minus {
            self.eat(TokenType::Minus);
            let expr = self.parse_expr_precedence(5);
            Expr::UnaryOp('-', Box::new(expr))
        } else if t == TokenType::IncrDecr {
            let op = self.current_token.value.clone();
            self.eat(TokenType::IncrDecr);
            let target = self.parse_named_expression();
            Expr::UpdateOp(op, true, Box::new(target))
        } else {
            self.parse_primary()
        }
    }

    /// Parses primary expressions (literals, variables, built-ins, calls).
    fn parse_primary(&mut self) -> Expr {
        let t = self.current_token.token_type;
        match t {
            TokenType::Number => {
                let val = self.current_token.value.clone();
                self.eat(TokenType::Number);
                Expr::Number(val)
            }
            TokenType::Lparen => {
                self.eat(TokenType::Lparen);
                let expr = self.parse_expression();
                self.eat(TokenType::Rparen);
                expr
            }
            TokenType::Length => {
                self.eat(TokenType::Length);
                self.eat(TokenType::Lparen);
                let expr = self.parse_expression();
                self.eat(TokenType::Rparen);
                Expr::LengthCall(Box::new(expr))
            }
            TokenType::Sqrt => {
                self.eat(TokenType::Sqrt);
                self.eat(TokenType::Lparen);
                let expr = self.parse_expression();
                self.eat(TokenType::Rparen);
                Expr::SqrtCall(Box::new(expr))
            }
            TokenType::Scale if self.peek_token_type(0) == TokenType::Lparen => {
                self.eat(TokenType::Scale);
                self.eat(TokenType::Lparen);
                let expr = self.parse_expression();
                self.eat(TokenType::Rparen);
                Expr::ScaleCall(Box::new(expr))
            }
            TokenType::Letter if self.peek_token_type(0) == TokenType::Lparen => {
                let name = self.current_token.value.clone();
                self.eat(TokenType::Letter);
                self.eat(TokenType::Lparen);
                let args = self.parse_opt_argument_list();
                self.eat(TokenType::Rparen);
                Expr::Call(name, args)
            }
            _ => {
                let target = self.parse_named_expression();
                if self.current_token.token_type == TokenType::IncrDecr {
                    let op = self.current_token.value.clone();
                    self.eat(TokenType::IncrDecr);
                    Expr::UpdateOp(op, false, Box::new(target))
                } else {
                    target
                }
            }
        }
    }

    /// Parses variables, arrays, or register accesses.
    fn parse_named_expression(&mut self) -> Expr {
        let t = self.current_token.token_type;
        match t {
            TokenType::Scale => {
                self.eat(TokenType::Scale);
                Expr::RegisterAccess("scale".to_string())
            }
            TokenType::Ibase => {
                self.eat(TokenType::Ibase);
                Expr::RegisterAccess("ibase".to_string())
            }
            TokenType::Obase => {
                self.eat(TokenType::Obase);
                Expr::RegisterAccess("obase".to_string())
            }
            TokenType::Letter => {
                let name = self.current_token.value.clone();
                self.eat(TokenType::Letter);
                if self.current_token.token_type == TokenType::Lbracket {
                    self.eat(TokenType::Lbracket);
                    let idx = self.parse_expression();
                    self.eat(TokenType::Rbracket);
                    Expr::ArrayAccess(name, Box::new(idx))
                } else {
                    Expr::Variable(name)
                }
            }
            _ => self.error(&format!("expected named expression, got {:?}", t)),
        }
    }

    /// Parses optional function call argument list.
    fn parse_opt_argument_list(&mut self) -> Vec<ExprOrArray> {
        if self.current_token.token_type == TokenType::Rparen {
            Vec::new()
        } else {
            self.parse_argument_list()
        }
    }

    /// Parses function call argument list.
    fn parse_argument_list(&mut self) -> Vec<ExprOrArray> {
        let mut args = Vec::new();
        loop {
            if self.current_token.token_type == TokenType::Letter
                && self.peek_token_type(0) == TokenType::Lbracket
                && self.peek_token_type(1) == TokenType::Rbracket
            {
                let name = self.current_token.value.clone();
                self.eat(TokenType::Letter);
                self.eat(TokenType::Lbracket);
                self.eat(TokenType::Rbracket);
                args.push(ExprOrArray::ArrayArg(name));
            } else {
                args.push(ExprOrArray::Expr(self.parse_expression()));
            }

            if self.current_token.token_type == TokenType::Comma {
                self.eat(TokenType::Comma);
            } else {
                break;
            }
        }
        args
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

    #[test]
    #[should_panic(expected = "unterminated string")]
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
}
