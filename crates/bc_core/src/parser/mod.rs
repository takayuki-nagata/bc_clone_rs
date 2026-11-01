// SPDX-License-Identifier: MIT

//! Lexer, Parser, and Abstract Syntax Tree (AST) definitions for the bc clone.
//!
//! Conforms to standard POSIX bc lexical and syntax grammar rules, supporting
//! operator precedence climbing and backslash-newline continuation.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

mod lexer;
mod parse;
#[cfg(test)]
mod tests;

pub use lexer::Lexer;
pub use parse::{DEFAULT_MAX_DEPTH, NESTING_TOO_DEEP, Parser};

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
    pub(super) fn text(&self) -> String {
        self.value.iter().map(|&b| char::from(b)).collect()
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
