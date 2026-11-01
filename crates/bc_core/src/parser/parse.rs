// SPDX-License-Identifier: MIT

//! The parser: recursive descent, with Pratt precedence climbing for expressions.

use super::{
    AssignOp, BinOp, Expr, ExprOrArray, ExtensionPolicy, FunctionDef, Lexer, Param, Register,
    RelOp, Stmt, Token, TokenType,
};
use crate::error::BcError;
use crate::verified_kernels::{
    TOK_ASSIGN_OP, TOK_EXP_OP, TOK_MUL_OP, TOK_PLUS_MINUS, verified_nesting_within_limit,
    verified_pratt_infix_info,
};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

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
            let mut description = String::from("multiple letter name - ");
            description.push_str(name);
            self.extension(description);
        }
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

    /// Consumes a token of the expected type, otherwise raises error.
    fn eat(&mut self, token_type: TokenType) -> Result<(), BcError> {
        if self.current_token.token_type == token_type {
            self.last_line = self.current_token.line;
            self.current_token = self.lexer.try_get_next_token()?;
            Ok(())
        } else {
            self.error()
        }
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
                _ => return self.error(),
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
        self.eat(TokenType::String)?;
        Ok(Stmt::StringLiteral(val))
    }

    /// Parses `break`, which must be inside a loop. GNU bc reports a stray `break` on its own
    /// line, and a stray `return` on the line of the token after it.
    fn parse_break_stmt(&mut self) -> Result<Stmt, BcError> {
        if self.loop_depth == 0 {
            return self.misplaced("Break outside a for/while");
        }
        self.eat(TokenType::Break)?;
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
        self.eat(TokenType::Lbrace)?;
        let stmts = self.parse_statement_list()?;
        self.eat(TokenType::Rbrace)?;
        Ok(Stmt::Block(stmts))
    }

    /// Parses an expression statement; a relational one is a GNU extension.
    fn parse_expr_stmt(&mut self) -> Result<Stmt, BcError> {
        let expr = self.parse_relational_expression()?;
        if matches!(expr, Expr::RelationalOp(..)) {
            self.extension(String::from("comparison in expression"));
        }
        Ok(Stmt::Expr(expr))
    }

    /// Parses the `for` statement.
    fn parse_for(&mut self) -> Result<Stmt, BcError> {
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

    /// Parses the keyword `if` or `while` and the `( relational_expression )` after it.
    fn parse_cond(&mut self) -> Result<Expr, BcError> {
        self.eat(self.current_token.token_type)?;
        self.eat(TokenType::Lparen)?;
        let cond = self.parse_relational_expression()?;
        self.eat(TokenType::Rparen)?;
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
            return self.error();
        }
        let name = self.current_token.text();
        self.eat(TokenType::Letter)?;

        self.eat(TokenType::Lparen)?;
        let params = self.parse_opt_define_list()?;
        self.parse_function_body(name, params)
    }

    /// Parses the rest of a function definition after its parameter list.
    fn parse_function_body(&mut self, name: String, params: Vec<Param>) -> Result<Stmt, BcError> {
        self.eat(TokenType::Rparen)?;

        self.eat(TokenType::Lbrace)?;
        // POSIX requires a newline after `{`; GNU bc checks the name at this point too.
        if self.current_token.token_type != TokenType::Newline {
            self.extension(String::from("End of line required"));
        }
        self.note_name(&name);
        self.skip_newlines()?;

        let autos = self.parse_opt_auto_define_list()?;
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
                return self.error();
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
            return self.error();
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
            self.eat(self.current_token.token_type)?;

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

    /// Parses a keyword followed by a parenthesized expression: `length`, `sqrt` or `scale`
    /// (`which` is 0, 1 or 2).
    fn parse_builtin(&mut self, which: u8) -> Result<(Expr, Height), BcError> {
        self.eat(self.current_token.token_type)?;
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
                self.eat(TokenType::Number)?;
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
        let name = self.eat_name()?;
        self.eat(TokenType::Lparen)?;
        let (args, h) = self.parse_opt_argument_list()?;
        self.eat(TokenType::Rparen)?;
        Ok((Expr::Call(name, args), h + 1))
    }

    /// Parses a named expression, then a postfix `++`/`--` or an assignment that binds to it.
    fn parse_named_tail(&mut self) -> Result<(Expr, Height), BcError> {
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
        self.eat(TokenType::Lbracket)?;
        let (idx, h) = self.parse_expression_h()?;
        self.eat(TokenType::Rbracket)?;
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
