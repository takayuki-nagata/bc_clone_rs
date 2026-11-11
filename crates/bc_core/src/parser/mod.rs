// SPDX-License-Identifier: MIT

//! Lexer, Parser, and Abstract Syntax Tree (AST) definitions for the bc clone.
//!
//! Conforms to standard POSIX bc lexical and syntax grammar rules, supporting
//! operator precedence climbing and backslash-newline continuation.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::refine::text_view;

mod lexer;
mod parse;
#[cfg(test)]
pub(crate) mod test_tree;
#[cfg(test)]
mod tests;

pub use lexer::Lexer;
pub(crate) use parse::parse_unit_ref;
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

verus! {

impl Token {
    /// The token's bytes as a `String`, when they are ASCII (names, numbers and operators).
    pub(super) fn text(&self) -> (r: String)
        requires
            all_ascii(self.value@),
        ensures
            text_view(r) == self.value@,
    {
        ascii_string(self.value.as_slice())
    }
}

/// Whether all the bytes are ASCII, so that each one is a character.
pub open spec fn all_ascii(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> b[i] < 0x80
}

/// Trusted: a `char` below 0x80 is one UTF-8 byte of the same value.
#[verifier::external_body]
pub(crate) fn ascii_string(b: &[u8]) -> (r: String)
    requires
        all_ascii(b@),
    ensures
        text_view(r) == b@,
{
    b.iter().map(|&x| char::from(x)).collect()
}

/// Trusted: cloning an `Rc` shares the same value.
#[verifier::external_body]
pub(crate) fn share_code(c: &Rc<Code>) -> (r: Rc<Code>)
    ensures
        *r == **c,
{
    Rc::clone(c)
}

} // verus!

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

/// A call argument: an expression (a node of the arena) or a whole array `a[]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Arg {
    Expr(usize),
    Array(String),
}

/// One node of the syntax tree. Children are indices into the arena [`Code`], and always smaller
/// than the node's own index. The variants and the order in which the parser adds them are those
/// of the specification's `Node` (`crates/bc_spec`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    Number(String),
    Var(String),
    Array(String, usize),
    Reg(Register),
    /// Unary minus.
    Neg(usize),
    Binary(BinOp, usize, usize),
    Rel(RelOp, usize, usize),
    /// `++`/`--` as `(increment, prefix, target)`.
    Update(bool, bool, usize),
    /// `(operator, target, value)`.
    Assign(AssignOp, usize, usize),
    Call(String, Vec<Arg>),
    Length(usize),
    Sqrt(usize),
    ScaleOf(usize),
    /// A parenthesized expression; kept so that `(a = 5)` is printed while `a = 5` is not.
    Paren(usize),
    Block(Vec<usize>),
    ExprStmt(usize),
    Str(Vec<u8>),
    Break,
    Return(Option<usize>),
    If(usize, usize),
    While(usize, usize),
    /// `(init, condition, post, body)`.
    For(usize, usize, usize, usize),
    /// A function definition, boxed so that it does not make every node larger.
    Define(Box<FunctionDecl>),
}

/// The parts of `Node::Define`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub autos: Vec<Param>,
    /// The statements of the body.
    pub body: Vec<usize>,
}

/// The syntax trees of one input unit. A flat arena: dropping or copying it does not recurse,
/// whatever the depth of the trees.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Code {
    pub nodes: Vec<Node>,
}

/// A defined function: the `Node::Define` at index `def` of the unit that defined it. The unit
/// is shared, so a call does not copy the body and a running body survives its redefinition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDef {
    pub code: Rc<Code>,
    pub def: usize,
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
pub struct ExTokenType(TokenType);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExToken(Token);

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
pub struct ExArg(Arg);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExFunctionDecl(FunctionDecl);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExNode(Node);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExCode(Code);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExFunctionDef(FunctionDef);

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
pub struct ExExtensionPolicy(ExtensionPolicy);

} // verus!

impl RelOp {
    /// The operator of a relational token (as `rel_code`).
    #[cfg(test)]
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
