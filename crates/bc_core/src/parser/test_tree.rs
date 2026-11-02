// SPDX-License-Identifier: MIT

//! Syntax trees for the unit tests: they build their inputs and state their expectations as
//! trees, which are converted to and from the arena that the parser and the evaluator use.

use super::{Arg, AssignOp, BinOp, Code, Node, Param, Parser, Register, RelOp};
use crate::error::BcError;
use crate::eval::Evaluator;
use crate::math::BCNum;
use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Number(String),
    Variable(String),
    ArrayAccess(String, Box<Expr>),
    RegisterAccess(Register),
    Negate(Box<Expr>),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
    RelationalOp(RelOp, Box<Expr>, Box<Expr>),
    Update(bool, bool, Box<Expr>),
    AssignOp(AssignOp, Box<Expr>, Box<Expr>),
    Call(String, Vec<ExprOrArray>),
    LengthCall(Box<Expr>),
    SqrtCall(Box<Expr>),
    ScaleCall(Box<Expr>),
    Paren(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprOrArray {
    Expr(Expr),
    ArrayArg(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDef {
    pub name: String,
    pub params: Vec<Param>,
    pub autos: Vec<Param>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Block(Vec<Stmt>),
    Expr(Expr),
    StringLiteral(Vec<u8>),
    Break,
    Return(Option<Expr>),
    If(Expr, Box<Stmt>),
    While(Expr, Box<Stmt>),
    For(Expr, Expr, Expr, Box<Stmt>),
    FunctionDef(FunctionDef),
}

fn push(code: &mut Code, n: Node) -> usize {
    code.nodes.push(n);
    code.nodes.len() - 1
}

pub fn lower_expr(code: &mut Code, e: &Expr) -> usize {
    let n = match e {
        Expr::Number(t) => Node::Number(t.clone()),
        Expr::Variable(x) => Node::Var(x.clone()),
        Expr::ArrayAccess(x, i) => Node::Array(x.clone(), lower_expr(code, i)),
        Expr::RegisterAccess(r) => Node::Reg(*r),
        Expr::Negate(a) => Node::Neg(lower_expr(code, a)),
        Expr::BinaryOp(op, l, r) => {
            let (a, b) = (lower_expr(code, l), lower_expr(code, r));
            Node::Binary(*op, a, b)
        }
        Expr::RelationalOp(op, l, r) => {
            let (a, b) = (lower_expr(code, l), lower_expr(code, r));
            Node::Rel(*op, a, b)
        }
        Expr::Update(inc, prefix, t) => Node::Update(*inc, *prefix, lower_expr(code, t)),
        Expr::AssignOp(op, t, v) => {
            let (a, b) = (lower_expr(code, t), lower_expr(code, v));
            Node::Assign(*op, a, b)
        }
        Expr::Call(name, args) => {
            let args = args
                .iter()
                .map(|a| match a {
                    ExprOrArray::Expr(x) => Arg::Expr(lower_expr(code, x)),
                    ExprOrArray::ArrayArg(x) => Arg::Array(x.clone()),
                })
                .collect();
            Node::Call(name.clone(), args)
        }
        Expr::LengthCall(a) => Node::Length(lower_expr(code, a)),
        Expr::SqrtCall(a) => Node::Sqrt(lower_expr(code, a)),
        Expr::ScaleCall(a) => Node::ScaleOf(lower_expr(code, a)),
        Expr::Paren(a) => Node::Paren(lower_expr(code, a)),
    };
    push(code, n)
}

pub fn lower_stmt(code: &mut Code, s: &Stmt) -> usize {
    let n = match s {
        Stmt::Block(l) => Node::Block(l.iter().map(|x| lower_stmt(code, x)).collect()),
        Stmt::Expr(e) => Node::ExprStmt(lower_expr(code, e)),
        Stmt::StringLiteral(t) => Node::Str(t.clone()),
        Stmt::Break => Node::Break,
        Stmt::Return(v) => Node::Return(v.as_ref().map(|e| lower_expr(code, e))),
        Stmt::If(c, b) => {
            let (i, j) = (lower_expr(code, c), lower_stmt(code, b));
            Node::If(i, j)
        }
        Stmt::While(c, b) => {
            let (i, j) = (lower_expr(code, c), lower_stmt(code, b));
            Node::While(i, j)
        }
        Stmt::For(i, c, p, b) => {
            let (a, d, e, f) = (
                lower_expr(code, i),
                lower_expr(code, c),
                lower_expr(code, p),
                lower_stmt(code, b),
            );
            Node::For(a, d, e, f)
        }
        Stmt::FunctionDef(fd) => {
            let body = fd.body.iter().map(|x| lower_stmt(code, x)).collect();
            Node::Define(fd.name.clone(), fd.params.clone(), fd.autos.clone(), body)
        }
    };
    push(code, n)
}

pub fn raise_expr(code: &Code, n: usize) -> Expr {
    let b = |i: &usize| Box::new(raise_expr(code, *i));
    match &code.nodes[n] {
        Node::Number(t) => Expr::Number(t.clone()),
        Node::Var(x) => Expr::Variable(x.clone()),
        Node::Array(x, i) => Expr::ArrayAccess(x.clone(), b(i)),
        Node::Reg(r) => Expr::RegisterAccess(*r),
        Node::Neg(a) => Expr::Negate(b(a)),
        Node::Binary(op, l, r) => Expr::BinaryOp(*op, b(l), b(r)),
        Node::Rel(op, l, r) => Expr::RelationalOp(*op, b(l), b(r)),
        Node::Update(inc, prefix, t) => Expr::Update(*inc, *prefix, b(t)),
        Node::Assign(op, t, v) => Expr::AssignOp(*op, b(t), b(v)),
        Node::Call(name, args) => Expr::Call(
            name.clone(),
            args.iter()
                .map(|a| match a {
                    Arg::Expr(x) => ExprOrArray::Expr(raise_expr(code, *x)),
                    Arg::Array(x) => ExprOrArray::ArrayArg(x.clone()),
                })
                .collect(),
        ),
        Node::Length(a) => Expr::LengthCall(b(a)),
        Node::Sqrt(a) => Expr::SqrtCall(b(a)),
        Node::ScaleOf(a) => Expr::ScaleCall(b(a)),
        Node::Paren(a) => Expr::Paren(b(a)),
        other => panic!("not an expression: {other:?}"),
    }
}

pub fn raise_stmt(code: &Code, n: usize) -> Stmt {
    let list = |l: &[usize]| l.iter().map(|i| raise_stmt(code, *i)).collect();
    match &code.nodes[n] {
        Node::Block(l) => Stmt::Block(list(l)),
        Node::ExprStmt(e) => Stmt::Expr(raise_expr(code, *e)),
        Node::Str(t) => Stmt::StringLiteral(t.clone()),
        Node::Break => Stmt::Break,
        Node::Return(v) => Stmt::Return(v.map(|e| raise_expr(code, e))),
        Node::If(c, b) => Stmt::If(raise_expr(code, *c), Box::new(raise_stmt(code, *b))),
        Node::While(c, b) => Stmt::While(raise_expr(code, *c), Box::new(raise_stmt(code, *b))),
        Node::For(i, c, p, b) => Stmt::For(
            raise_expr(code, *i),
            raise_expr(code, *c),
            raise_expr(code, *p),
            Box::new(raise_stmt(code, *b)),
        ),
        Node::Define(name, params, autos, body) => Stmt::FunctionDef(FunctionDef {
            name: name.clone(),
            params: params.clone(),
            autos: autos.clone(),
            body: list(body),
        }),
        other => panic!("not a statement: {other:?}"),
    }
}

impl Parser {
    /// Parses the program into trees.
    pub fn try_parse_tree(&mut self) -> Result<Vec<Stmt>, BcError> {
        let list = self.try_parse_program()?;
        let code = self.take_code();
        Ok(list.iter().map(|n| raise_stmt(&code, *n)).collect())
    }

    /// [`Parser::try_parse_tree`], panicking on an error.
    pub fn parse_program(&mut self) -> Vec<Stmt> {
        self.try_parse_tree().unwrap_or_else(|e| panic!("{}", e))
    }
}

impl Evaluator {
    pub fn try_evaluate_tree(&mut self, e: &Expr) -> Result<BCNum, BcError> {
        let mut code = Code::default();
        let n = lower_expr(&mut code, e);
        self.try_evaluate(&Rc::new(code), n)
    }

    pub fn try_execute_tree(&mut self, s: &Stmt) -> Result<(), BcError> {
        let mut code = Code::default();
        let n = lower_stmt(&mut code, s);
        self.try_execute(&Rc::new(code), n)
    }

    pub fn evaluate(&mut self, e: &Expr) -> BCNum {
        self.try_evaluate_tree(e)
            .unwrap_or_else(|x| panic!("{}", x))
    }

    pub fn execute(&mut self, s: &Stmt) {
        self.try_execute_tree(s).unwrap_or_else(|x| panic!("{}", x))
    }
}
