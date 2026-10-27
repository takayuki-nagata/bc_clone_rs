// SPDX-License-Identifier: MIT

//! The parser (`bc_core::parser::Parser`) over the token sequence of a unit.
//!
//! The syntax tree is an arena: `PState::nodes` holds every node, and nodes refer to their
//! children by index. Each function mirrors the production function of the same name: the
//! order in which tokens are consumed and peeked, the line of each diagnostic, the recorded
//! extension uses, and the nesting checks (`depth` and expression heights against
//! `max_depth`). Every function takes `fuel` and passes `fuel - 1` to the functions it calls,
//! which makes termination evident; running out of fuel is reported as `PErr::out_of_fuel`
//! (the oracle treats it as "not modeled").
//!
//! Correspondence with `parser::Expr` / `parser::Stmt`: `Node::Number`, `Var`, `Array`
//! (`ArrayAccess`), `Reg` (`RegisterAccess`), `Neg` (`UnaryOp('-')`), `Binary` (`BinaryOp`),
//! `Rel` (`RelationalOp`), `Update` (`UpdateOp`), `Assign` (`AssignOp`), `Call`, `Length`
//! (`LengthCall`), `Sqrt` (`SqrtCall`), `ScaleOf` (`ScaleCall`), `Paren`; `Block`,
//! `ExprStmt` (`Stmt::Expr`), `Str` (`StringLiteral`), `Break`, `Return`, `If`, `While`,
//! `For`, `Define` (`FunctionDef`). `quit` is not a node: parsing it stops with `PErr::quit`.
//!
//! Operator codes: `Binary` 0 `+`, 1 `-`, 2 `*`, 3 `/`, 4 `%`, 5 `^`; `Assign` 0 `=`, 1 `+=`,
//! 2 `-=`, 3 `*=`, 4 `/=`, 5 `%=`, 6 `^=`; `Rel` 0 `==`, 1 `!=`, 2 `<`, 3 `<=`, 4 `>`,
//! 5 `>=`; `Reg` 0 `scale`, 1 `ibase`, 2 `obase`.

use crate::lexer::*;
use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

exec_spec_verified! {

/// A parameter or `auto` local (`parser::Param`).
pub struct Param {
    pub name: Seq<u8>,
    pub is_array: bool,
}

/// A call argument: an expression node, or a whole array `name[]`.
pub struct Arg {
    pub is_array: bool,
    pub name: Seq<u8>,
    pub expr: usize,
}

/// A syntax-tree node (see the module documentation).
pub enum Node {
    Number(Seq<u8>),
    Var(Seq<u8>),
    Array(Seq<u8>, usize),
    Reg(u8),
    Neg(usize),
    Binary(u8, usize, usize),
    Rel(u8, usize, usize),
    /// `(increment, prefix, target)`.
    Update(bool, bool, usize),
    Assign(u8, usize, usize),
    Call(Seq<u8>, Seq<Arg>),
    Length(usize),
    Sqrt(usize),
    ScaleOf(usize),
    Paren(usize),
    Block(Seq<usize>),
    ExprStmt(usize),
    Str(Seq<u8>),
    Break,
    /// `(has_value, value)`.
    Return(bool, usize),
    If(usize, usize),
    While(usize, usize),
    For(usize, usize, usize, usize),
    Define(Seq<u8>, Seq<Param>, Seq<Param>, Seq<usize>),
}

/// A use of non-POSIX syntax, reported under `-w` and `-s`.
pub struct ExtUse {
    pub line: u64,
    pub desc: Seq<u8>,
}

/// Parser configuration: whether extension uses are recorded (`-w` or `-s`), and
/// `Evaluator::max_depth`.
pub struct PCfg {
    pub record_extensions: bool,
    pub max_depth: u64,
}

pub struct PState {
    pub cur: usize,
    pub depth: u64,
    pub last_line: u64,
    pub loop_depth: u64,
    pub in_function: bool,
    pub ext: Seq<ExtUse>,
    pub nodes: Seq<Node>,
}

/// Why parsing stopped: `quit`, a diagnostic (`line` within the unit), or exhausted fuel.
pub struct PErr {
    pub quit: bool,
    pub out_of_fuel: bool,
    pub line: u64,
    pub msg: Seq<u8>,
}

/// The result of a parsing function. Which payload fields are meaningful depends on the
/// function; `st` is the state after it (also when `!ok`, for the extension uses).
pub struct PR {
    pub ok: bool,
    pub err: PErr,
    pub st: PState,
    pub node: usize,
    pub h: u64,
    pub flag: bool,
    pub list: Seq<usize>,
    pub params: Seq<Param>,
    pub args: Seq<Arg>,
    pub name: Seq<u8>,
}

// ---------------------------------------------------------------------------------------------
// Results and state updates
// ---------------------------------------------------------------------------------------------

pub open spec fn no_err() -> PErr {
    PErr { quit: false, out_of_fuel: false, line: 0u64, msg: seq![] }
}

pub open spec fn pr_ok(st: PState) -> PR {
    PR { ok: true, err: no_err(), st: st, node: 0usize, h: 0u64, flag: false, list: seq![], params: seq![], args: seq![], name: seq![] }
}

pub open spec fn pr_err(st: PState, e: PErr) -> PR {
    PR { ok: false, err: e, st: st, node: 0usize, h: 0u64, flag: false, list: seq![], params: seq![], args: seq![], name: seq![] }
}

pub open spec fn pr_node(st: PState, node: usize, h: u64) -> PR {
    PR { ok: true, err: no_err(), st: st, node: node, h: h, flag: true, list: seq![], params: seq![], args: seq![], name: seq![] }
}

pub open spec fn pr_list(st: PState, list: Seq<usize>) -> PR {
    PR { ok: true, err: no_err(), st: st, node: 0usize, h: 0u64, flag: false, list: list, params: seq![], args: seq![], name: seq![] }
}

pub open spec fn pr_params(st: PState, params: Seq<Param>) -> PR {
    PR { ok: true, err: no_err(), st: st, node: 0usize, h: 0u64, flag: false, list: seq![], params: params, args: seq![], name: seq![] }
}

pub open spec fn pr_args(st: PState, args: Seq<Arg>, h: u64) -> PR {
    PR { ok: true, err: no_err(), st: st, node: 0usize, h: h, flag: false, list: seq![], params: seq![], args: args, name: seq![] }
}

pub open spec fn out_of_fuel(st: PState) -> PR {
    pr_err(st, PErr { quit: true, out_of_fuel: true, line: 0u64, msg: seq![] })
}

/// `BcError::syntax` at `line` (the message is always `syntax error`).
pub open spec fn syntax_at(st: PState, line: u64) -> PR {
    pr_err(st, PErr { quit: false, out_of_fuel: false, line: line, msg: syntax_error_msg() })
}

pub open spec fn st_set_cur(st: PState, cur: usize, last_line: u64) -> PState {
    PState { cur: cur, depth: st.depth, last_line: last_line, loop_depth: st.loop_depth, in_function: st.in_function, ext: st.ext, nodes: st.nodes }
}

pub open spec fn st_set_depth(st: PState, depth: u64) -> PState {
    PState { cur: st.cur, depth: depth, last_line: st.last_line, loop_depth: st.loop_depth, in_function: st.in_function, ext: st.ext, nodes: st.nodes }
}

pub open spec fn st_set_loop(st: PState, loop_depth: u64, in_function: bool) -> PState {
    PState { cur: st.cur, depth: st.depth, last_line: st.last_line, loop_depth: loop_depth, in_function: in_function, ext: st.ext, nodes: st.nodes }
}

pub open spec fn st_push_ext(st: PState, u: ExtUse) -> PState {
    PState { cur: st.cur, depth: st.depth, last_line: st.last_line, loop_depth: st.loop_depth, in_function: st.in_function, ext: st.ext.push(u), nodes: st.nodes }
}

/// Appends a node to the arena; its index is the old length.
pub open spec fn add_node(st: PState, n: Node, h: u64) -> PR {
    let idx = st.nodes.len() as usize;
    let st2 = PState { cur: st.cur, depth: st.depth, last_line: st.last_line, loop_depth: st.loop_depth, in_function: st.in_function, ext: st.ext, nodes: st.nodes.push(n) };
    pr_node(st2, idx, h)
}

// ---------------------------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------------------------

/// The token at `i`; past the end, the final `Eof` again (the lexer keeps returning `Eof`).
pub open spec fn token_at(toks: Seq<Token>, i: usize) -> Token {
    if i < toks.len() {
        toks[i as int]
    } else if toks.len() > 0 {
        toks[toks.len() - 1]
    } else {
        Token { kind: Tok::Eof, text: seq![], line: 1u64 }
    }
}

pub open spec fn cur_tok(toks: Seq<Token>, st: PState) -> Token {
    token_at(toks, st.cur)
}

/// The error of fetching the token at `i` when it is a lexical error.
pub open spec fn lex_error_at(toks: Seq<Token>, i: usize) -> bool {
    token_at(toks, i).kind is LexError
}

pub open spec fn lex_err(st: PState, t: Token) -> PR {
    pr_err(st, PErr { quit: false, out_of_fuel: false, line: t.line, msg: t.text })
}

/// `Parser::eat`: consumes the current token if it has `kind`, then fetches the next one.
pub open spec fn eat(toks: Seq<Token>, st: PState, kind: Tok) -> PR {
    let t = cur_tok(toks, st);
    if t.kind == kind {
        let next = if st.cur < 0xffff_fff0usize { (st.cur + 1) as usize } else { st.cur };
        let st2 = st_set_cur(st, next, t.line);
        if lex_error_at(toks, next) { lex_err(st2, token_at(toks, next)) } else { pr_ok(st2) }
    } else {
        syntax_at(st, t.line)
    }
}

/// `Parser::peek_token_type(off)`: the kind of the token `off + 1` after the current one,
/// failing if a lexical error is reached on the way.
pub open spec fn peek_kind(toks: Seq<Token>, st: PState, off: usize) -> (bool, Tok, Token) {
    let j = if st.cur < 0xffff_fff0usize && off < 8 { (st.cur + 1 + off) as usize } else { st.cur };
    let last = if toks.len() > 0 { (toks.len() - 1) as usize } else { 0usize };
    let le = toks.len() > 0 && toks[toks.len() - 1].kind is LexError;
    if le && last <= j {
        (false, Tok::Eof, token_at(toks, last))
    } else {
        (true, token_at(toks, j).kind, token_at(toks, j))
    }
}

/// `Parser::extension`.
pub open spec fn extension(toks: Seq<Token>, cfg: PCfg, st: PState, desc: Seq<u8>) -> PState {
    if cfg.record_extensions {
        st_push_ext(st, ExtUse { line: cur_tok(toks, st).line, desc: desc })
    } else {
        st
    }
}

/// `multiple letter name - `.
pub open spec fn multi_letter_prefix() -> Seq<u8> {
    seq![109u8, 117, 108, 116, 105, 112, 108, 101, 32, 108, 101, 116, 116, 101, 114, 32, 110, 97, 109, 101, 32, 45, 32]
}

/// `Parser::note_name`.
pub open spec fn note_name(toks: Seq<Token>, cfg: PCfg, st: PState, name: Seq<u8>) -> PState {
    if name.len() > 1 { extension(toks, cfg, st, multi_letter_prefix().add(name)) } else { st }
}

/// `Parser::eat_name`: the name in `PR::name`.
pub open spec fn eat_name(toks: Seq<Token>, cfg: PCfg, st: PState) -> PR {
    let name = cur_tok(toks, st).text;
    let r = eat(toks, st, Tok::Letter);
    if !r.ok {
        r
    } else {
        let st2 = note_name(toks, cfg, r.st, name);
        PR { ok: true, err: no_err(), st: st2, node: 0usize, h: 0u64, flag: false, list: seq![], params: seq![], args: seq![], name: name }
    }
}

/// `nesting too deep`, reported at the line of the last consumed token.
pub open spec fn too_deep(st: PState) -> PR {
    pr_err(st, PErr { quit: false, out_of_fuel: false, line: st.last_line,
        msg: seq![110u8, 101, 115, 116, 105, 110, 103, 32, 116, 111, 111, 32, 100, 101, 101, 112] })
}

/// `verified_nesting_within_limit(depth, h, max_depth)`.
pub open spec fn within(depth: u64, h: u64, max_depth: u64) -> bool {
    h <= max_depth && depth <= max_depth - h
}

pub open spec fn max_u64(a: u64, b: u64) -> u64 {
    if a >= b { a } else { b }
}

pub open spec fn inc(h: u64) -> u64 {
    if h < 0xffff_ffff_ffff_ffffu64 { (h + 1) as u64 } else { h }
}

/// A message-carrying syntax diagnostic (`Parser::misplaced`).
pub open spec fn misplaced(toks: Seq<Token>, st: PState, msg: Seq<u8>) -> PR {
    pr_err(st, PErr { quit: false, out_of_fuel: false, line: cur_tok(toks, st).line, msg: msg })
}

pub open spec fn binop_code(t: Token) -> u8 {
    let c = if t.text.len() > 0 { t.text[0] } else { 0u8 };
    if c == 43u8 { 0u8 } else if c == 45u8 { 1u8 } else if c == 42u8 { 2u8 }
    else if c == 47u8 { 3u8 } else if c == 37u8 { 4u8 } else { 5u8 }
}

pub open spec fn assign_code(t: Token) -> u8 {
    let c = if t.text.len() > 0 { t.text[0] } else { 0u8 };
    if t.text.len() == 1 { 0u8 }
    else if c == 43u8 { 1u8 } else if c == 45u8 { 2u8 } else if c == 42u8 { 3u8 }
    else if c == 47u8 { 4u8 } else if c == 37u8 { 5u8 } else { 6u8 }
}

pub open spec fn rel_code(t: Token) -> u8 {
    let c = if t.text.len() > 0 { t.text[0] } else { 0u8 };
    let two = t.text.len() == 2;
    if c == 61u8 { 0u8 } else if c == 33u8 { 1u8 }
    else if c == 60u8 { if two { 3u8 } else { 2u8 } }
    else { if two { 5u8 } else { 4u8 } }
}

/// `get_infix_info` with `verified_pratt_infix_info`: `(precedence, is_assignment,
/// next_min_precedence)`; precedence -1 for a token that is not an infix operator.
pub open spec fn infix_info(k: Tok) -> (i8, bool, i8) {
    match k {
        Tok::AssignOp => (1i8, true, 1i8),
        Tok::Plus => (2i8, false, 3i8),
        Tok::Minus => (2i8, false, 3i8),
        Tok::MulOp => (3i8, false, 4i8),
        Tok::Exp => (4i8, false, 4i8),
        _ => (-1i8, false, 0i8),
    }
}

// ---------------------------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------------------------

/// `Parser::try_parse_program` after the items `acc`.
pub open spec fn p_program(toks: Seq<Token>, cfg: PCfg, st: PState, acc: Seq<usize>, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else if cur_tok(toks, st).kind is Eof { pr_list(st, acc) }
    else {
        let r = p_input_item(toks, cfg, st, (fuel - 1) as u64);
        if !r.ok { r }
        else if r.flag { p_program(toks, cfg, r.st, acc.push(r.node), (fuel - 1) as u64) }
        else { p_program(toks, cfg, r.st, acc, (fuel - 1) as u64) }
    }
}

/// `Parser::parse_input_item`: `flag` tells whether there is an item.
pub open spec fn p_input_item(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else if cur_tok(toks, st).kind is Define { p_function(toks, cfg, st, (fuel - 1) as u64) }
    else {
        let r = p_semicolon_list(toks, cfg, st, seq![], (fuel - 1) as u64);
        if !r.ok { r }
        else {
            let e = if cur_tok(toks, r.st).kind is Newline { eat(toks, r.st, Tok::Newline) } else { eat(toks, r.st, Tok::Eof) };
            if !e.ok { e }
            else if r.list.len() == 0 { pr_ok(e.st) }
            else { add_node(e.st, Node::Block(r.list), 0u64) }
        }
    }
}

/// `Parser::parse_semicolon_list` after the statements `acc`.
pub open spec fn p_semicolon_list(toks: Seq<Token>, cfg: PCfg, st: PState, acc: Seq<usize>, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let k = cur_tok(toks, st).kind;
        if k is Newline || k is Eof || k is Rbrace { pr_list(st, acc) }
        else if k is Semicolon {
            let e = eat(toks, st, Tok::Semicolon);
            if !e.ok { e } else { p_semicolon_list(toks, cfg, e.st, acc, (fuel - 1) as u64) }
        } else {
            let r = p_statement(toks, cfg, st, (fuel - 1) as u64);
            if !r.ok { r }
            else if cur_tok(toks, r.st).kind is Semicolon {
                let e = eat(toks, r.st, Tok::Semicolon);
                if !e.ok { e } else { p_semicolon_list(toks, cfg, e.st, acc.push(r.node), (fuel - 1) as u64) }
            } else {
                pr_list(r.st, acc.push(r.node))
            }
        }
    }
}

/// `Parser::skip_newlines`.
pub open spec fn p_skip_newlines(toks: Seq<Token>, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else if cur_tok(toks, st).kind is Newline {
        let e = eat(toks, st, Tok::Newline);
        if !e.ok { e } else { p_skip_newlines(toks, e.st, (fuel - 1) as u64) }
    } else { pr_ok(st) }
}

/// `Parser::parse_statement_list` after the statements `acc`.
pub open spec fn p_statement_list(toks: Seq<Token>, cfg: PCfg, st: PState, acc: Seq<usize>, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let s = p_skip_newlines(toks, st, (fuel - 1) as u64);
        if !s.ok { s }
        else {
            let k = cur_tok(toks, s.st).kind;
            if k is Eof || k is Rbrace { pr_list(s.st, acc) }
            else {
                let r = p_statement(toks, cfg, s.st, (fuel - 1) as u64);
                if !r.ok { r }
                else {
                    let nk = cur_tok(toks, r.st).kind;
                    if nk is Semicolon {
                        let e = eat(toks, r.st, Tok::Semicolon);
                        if !e.ok { e } else { p_statement_list(toks, cfg, e.st, acc.push(r.node), (fuel - 1) as u64) }
                    } else if nk is Newline {
                        let e = eat(toks, r.st, Tok::Newline);
                        if !e.ok { e } else { p_statement_list(toks, cfg, e.st, acc.push(r.node), (fuel - 1) as u64) }
                    } else if nk is Rbrace || nk is Eof {
                        pr_list(r.st, acc.push(r.node))
                    } else {
                        syntax_at(r.st, cur_tok(toks, r.st).line)
                    }
                }
            }
        }
    }
}

/// `Parser::parse_statement`: one nesting level around `parse_statement_inner`.
pub open spec fn p_statement(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else if !within(st.depth, 1u64, cfg.max_depth) { too_deep(st) }
    else {
        let r = p_statement_inner(toks, cfg, st_set_depth(st, (st.depth + 1) as u64), (fuel - 1) as u64);
        if !r.ok { r } else { pr_node(st_set_depth(r.st, st.depth), r.node, r.h) }
    }
}

/// `Parser::parse_loop_body`.
pub open spec fn p_loop_body(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let r = p_statement(toks, cfg, st_set_loop(st, inc(st.loop_depth), st.in_function), (fuel - 1) as u64);
        if !r.ok { r } else { pr_node(st_set_loop(r.st, st.loop_depth, r.st.in_function), r.node, r.h) }
    }
}

/// `Break outside a for/while`.
pub open spec fn break_msg() -> Seq<u8> {
    seq![66u8, 114, 101, 97, 107, 32, 111, 117, 116, 115, 105, 100, 101, 32, 97, 32, 102, 111, 114, 47, 119, 104, 105, 108, 101]
}

/// `Return outside of a function.`
pub open spec fn return_msg() -> Seq<u8> {
    seq![82u8, 101, 116, 117, 114, 110, 32, 111, 117, 116, 115, 105, 100, 101, 32, 111, 102, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 46]
}

/// `comparison in expression`.
pub open spec fn comparison_msg() -> Seq<u8> {
    seq![99u8, 111, 109, 112, 97, 114, 105, 115, 111, 110, 32, 105, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110]
}

/// `Parser::parse_statement_inner`.
pub open spec fn p_statement_inner(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let k = cur_tok(toks, st).kind;
        let f = (fuel - 1) as u64;
        if k is Str { p_string_stmt(toks, st) }
        else if k is Break { p_break_stmt(toks, st) }
        else if k is Quit { pr_err(st, PErr { quit: true, out_of_fuel: false, line: 0u64, msg: seq![] }) }
        else if k is Return { p_return_stmt(toks, cfg, st, f) }
        else if k is For { p_for(toks, cfg, st, f) }
        else if k is If { p_if(toks, cfg, st, f) }
        else if k is While { p_while(toks, cfg, st, f) }
        else if k is Lbrace { p_block(toks, cfg, st, f) }
        else { p_expr_stmt(toks, cfg, st, f) }
    }
}

/// A string statement.
pub open spec fn p_string_stmt(toks: Seq<Token>, st: PState) -> PR {
    let text = cur_tok(toks, st).text;
    let e = eat(toks, st, Tok::Str);
    if !e.ok { e } else { add_node(e.st, Node::Str(text), 0u64) }
}

/// `break`, which must be inside a loop.
pub open spec fn p_break_stmt(toks: Seq<Token>, st: PState) -> PR {
    if st.loop_depth == 0 { misplaced(toks, st, break_msg()) }
    else {
        let e = eat(toks, st, Tok::Break);
        if !e.ok { e } else { add_node(e.st, Node::Break, 0u64) }
    }
}

/// `return`, which must be inside a function (checked after the statement is parsed).
pub open spec fn p_return_stmt(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let r = p_return(toks, cfg, st, (fuel - 1) as u64);
        if !r.ok { r }
        else if !r.st.in_function { misplaced(toks, r.st, return_msg()) }
        else { r }
    }
}

/// `{ statement_list }`.
pub open spec fn p_block(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let e = eat(toks, st, Tok::Lbrace);
        if !e.ok { e }
        else {
            let l = p_statement_list(toks, cfg, e.st, seq![], (fuel - 1) as u64);
            if !l.ok { l } else { p_block_end(toks, l.st, l.list) }
        }
    }
}

pub open spec fn p_block_end(toks: Seq<Token>, st: PState, list: Seq<usize>) -> PR {
    let e = eat(toks, st, Tok::Rbrace);
    if !e.ok { e } else { add_node(e.st, Node::Block(list), 0u64) }
}

/// An expression statement; a relational one is a GNU extension.
pub open spec fn p_expr_stmt(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let r = p_relational(toks, cfg, st, (fuel - 1) as u64);
        if !r.ok { r }
        else {
            let is_rel = r.node < r.st.nodes.len() && r.st.nodes[r.node as int] is Rel;
            let st2 = if is_rel { extension(toks, cfg, r.st, comparison_msg()) } else { r.st };
            add_node(st2, Node::ExprStmt(r.node), 0u64)
        }
    }
}

/// The `for` statement.
pub open spec fn p_for(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let e1 = eat(toks, st, Tok::For);
        if !e1.ok { e1 } else {
        let e2 = eat(toks, e1.st, Tok::Lparen);
        if !e2.ok { e2 } else {
        let init = p_expr_prec(toks, cfg, e2.st, 0i8, f);
        if !init.ok { init } else {
        let e3 = eat(toks, init.st, Tok::Semicolon);
        if !e3.ok { e3 } else {
        let cond = p_relational(toks, cfg, e3.st, f);
        if !cond.ok { cond } else {
        let e4 = eat(toks, cond.st, Tok::Semicolon);
        if !e4.ok { e4 } else {
        let post = p_expr_prec(toks, cfg, e4.st, 0i8, f);
        if !post.ok { post } else {
        let e5 = eat(toks, post.st, Tok::Rparen);
        if !e5.ok { e5 } else {
        let body = p_loop_body(toks, cfg, e5.st, f);
        if !body.ok { body } else {
        add_node(body.st, Node::For(init.node, cond.node, post.node, body.node), 0u64)
        }}}}}}}}}
    }
}

/// `( relational_expression )` after `if` or `while`: the condition in `node`.
pub open spec fn p_cond(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let e1 = eat(toks, st, cur_tok(toks, st).kind);
        if !e1.ok { e1 } else {
        let e2 = eat(toks, e1.st, Tok::Lparen);
        if !e2.ok { e2 } else {
        let cond = p_relational(toks, cfg, e2.st, (fuel - 1) as u64);
        if !cond.ok { cond } else {
        let e3 = eat(toks, cond.st, Tok::Rparen);
        if !e3.ok { e3 } else { pr_node(e3.st, cond.node, 0u64) }
        }}}
    }
}

/// The `if` statement.
pub open spec fn p_if(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let c = p_cond(toks, cfg, st, (fuel - 1) as u64);
        if !c.ok { c } else {
        let body = p_statement(toks, cfg, c.st, (fuel - 1) as u64);
        if !body.ok { body } else { add_node(body.st, Node::If(c.node, body.node), 0u64) }
        }
    }
}

/// The `while` statement.
pub open spec fn p_while(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let c = p_cond(toks, cfg, st, (fuel - 1) as u64);
        if !c.ok { c } else {
        let body = p_loop_body(toks, cfg, c.st, (fuel - 1) as u64);
        if !body.ok { body } else { add_node(body.st, Node::While(c.node, body.node), 0u64) }
        }
    }
}

/// `return expression requires parenthesis`.
pub open spec fn return_paren_msg() -> Seq<u8> {
    seq![114u8, 101, 116, 117, 114, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 114, 101, 113, 117, 105, 114, 101, 115, 32, 112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 115]
}

/// `Parser::parse_return`.
pub open spec fn p_return(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let e = eat(toks, st, Tok::Return);
        if !e.ok { e }
        else if cur_tok(toks, e.st).kind is Lparen {
            let e2 = eat(toks, e.st, Tok::Lparen);
            if !e2.ok { e2 }
            else if cur_tok(toks, e2.st).kind is Rparen {
                let e3 = eat(toks, e2.st, Tok::Rparen);
                if !e3.ok { e3 } else { add_node(e3.st, Node::Return(false, 0usize), 0u64) }
            } else {
                let v = p_expr_prec(toks, cfg, e2.st, 0i8, f);
                if !v.ok { v }
                else {
                    let e3 = eat(toks, v.st, Tok::Rparen);
                    if !e3.ok { e3 } else { add_node(e3.st, Node::Return(true, v.node), 0u64) }
                }
            }
        } else {
            let nk = cur_tok(toks, e.st).kind;
            if !(nk is Newline) && !(nk is Semicolon) && !(nk is Rbrace) && !(nk is Eof) {
                let v = p_expr_prec(toks, cfg, e.st, 0i8, f);
                if !v.ok { v }
                else {
                    let st2 = extension(toks, cfg, v.st, return_paren_msg());
                    add_node(st2, Node::Return(true, v.node), 0u64)
                }
            } else {
                add_node(e.st, Node::Return(false, 0usize), 0u64)
            }
        }
    }
}

/// `End of line required`.
pub open spec fn eol_msg() -> Seq<u8> {
    seq![69u8, 110, 100, 32, 111, 102, 32, 108, 105, 110, 101, 32, 114, 101, 113, 117, 105, 114, 101, 100]
}

/// `Parser::parse_function`: `define name ( params ) {`, then the body.
pub open spec fn p_function(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let e1 = eat(toks, st, Tok::Define);
        if !e1.ok { e1 }
        else if !(cur_tok(toks, e1.st).kind is Letter) { syntax_at(e1.st, cur_tok(toks, e1.st).line) }
        else {
            let name = cur_tok(toks, e1.st).text;
            let e2 = eat(toks, e1.st, Tok::Letter);
            if !e2.ok { e2 } else {
            let e3 = eat(toks, e2.st, Tok::Lparen);
            if !e3.ok { e3 } else {
            let ps = if cur_tok(toks, e3.st).kind is Rparen { pr_params(e3.st, seq![]) } else { p_define_list(toks, cfg, e3.st, seq![], f) };
            if !ps.ok { ps } else { p_function_body(toks, cfg, ps.st, name, ps.params, f) }
            }}
        }
    }
}

/// The rest of a function definition after its parameter list.
pub open spec fn p_function_body(toks: Seq<Token>, cfg: PCfg, st: PState, name: Seq<u8>, params: Seq<Param>, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let e4 = eat(toks, st, Tok::Rparen);
        if !e4.ok { e4 } else {
        let e5 = eat(toks, e4.st, Tok::Lbrace);
        if !e5.ok { e5 } else {
        let st6 = if !(cur_tok(toks, e5.st).kind is Newline) { extension(toks, cfg, e5.st, eol_msg()) } else { e5.st };
        let st7 = note_name(toks, cfg, st6, name);
        let s = p_skip_newlines(toks, st7, f);
        if !s.ok { s } else {
        let au = p_opt_auto(toks, cfg, s.st, f);
        if !au.ok { au } else { p_function_stmts(toks, cfg, au.st, name, params, au.params, f) }
        }}}
    }
}

/// The statements of a function body, parsed with `in_function` set and no enclosing loop.
pub open spec fn p_function_stmts(toks: Seq<Token>, cfg: PCfg, st: PState, name: Seq<u8>, params: Seq<Param>, autos: Seq<Param>, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let body = p_statement_list(toks, cfg, st_set_loop(st, 0u64, true), seq![], (fuel - 1) as u64);
        if !body.ok { body } else {
        let e8 = eat(toks, st_set_loop(body.st, st.loop_depth, st.in_function), Tok::Rbrace);
        if !e8.ok { e8 } else { add_node(e8.st, Node::Define(name, params, autos, body.list), 0u64) }
        }
    }
}

/// `Parser::parse_define_list` after the parameters `acc`.
pub open spec fn p_define_list(toks: Seq<Token>, cfg: PCfg, st: PState, acc: Seq<Param>, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else if !(cur_tok(toks, st).kind is Letter) { syntax_at(st, cur_tok(toks, st).line) }
    else {
        let n = eat_name(toks, cfg, st);
        if !n.ok { n } else {
        let name = n.name;
        let arr = if cur_tok(toks, n.st).kind is Lbracket {
            let e1 = eat(toks, n.st, Tok::Lbracket);
            if !e1.ok { e1 } else { let e2 = eat(toks, e1.st, Tok::Rbracket); if !e2.ok { e2 } else { pr_node(e2.st, 1usize, 0u64) } }
        } else { pr_node(n.st, 0usize, 0u64) };
        if !arr.ok { arr } else {
        let acc2 = acc.push(Param { name: name, is_array: arr.node == 1 });
        if cur_tok(toks, arr.st).kind is Comma {
            let e = eat(toks, arr.st, Tok::Comma);
            if !e.ok { e } else { p_define_list(toks, cfg, e.st, acc2, (fuel - 1) as u64) }
        } else { pr_params(arr.st, acc2) }
        }}
    }
}

/// `Parser::parse_opt_auto_define_list`.
pub open spec fn p_opt_auto(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else if !(cur_tok(toks, st).kind is Auto) { pr_params(st, seq![]) }
    else {
        let e = eat(toks, st, Tok::Auto);
        if !e.ok { e } else {
        let l = p_define_list(toks, cfg, e.st, seq![], (fuel - 1) as u64);
        if !l.ok { l } else {
        let k = cur_tok(toks, l.st).kind;
        let e2 = if k is Newline { eat(toks, l.st, Tok::Newline) }
            else if k is Semicolon { eat(toks, l.st, Tok::Semicolon) }
            else { syntax_at(l.st, cur_tok(toks, l.st).line) };
        if !e2.ok { e2 } else { pr_params(e2.st, l.params) }
        }}
    }
}

// ---------------------------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------------------------

/// `Parser::parse_relational_expression`.
pub open spec fn p_relational(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let l = p_expr_prec(toks, cfg, st, 0i8, f);
        if !l.ok { l }
        else if cur_tok(toks, l.st).kind is RelOp {
            let op = rel_code(cur_tok(toks, l.st));
            let e = eat(toks, l.st, Tok::RelOp);
            if !e.ok { e } else {
            let r = p_expr_prec(toks, cfg, e.st, 0i8, f);
            if !r.ok { r } else {
            let h = inc(max_u64(l.h, r.h));
            if !within(r.st.depth, h, cfg.max_depth) { too_deep(r.st) }
            else { add_node(r.st, Node::Rel(op, l.node, r.node), h) }
            }}
        } else { l }
    }
}

/// `Parser::parse_expr_precedence`: one nesting level around the Pratt loop.
pub open spec fn p_expr_prec(toks: Seq<Token>, cfg: PCfg, st: PState, min_prec: i8, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else if !within(st.depth, 1u64, cfg.max_depth) { too_deep(st) }
    else {
        let f = (fuel - 1) as u64;
        let st1 = st_set_depth(st, (st.depth + 1) as u64);
        let p = p_prefix(toks, cfg, st1, f);
        if !p.ok { p }
        else {
            let r = p_expr_loop(toks, cfg, p.st, p.node, p.h, min_prec, f);
            if !r.ok { r } else { pr_node(st_set_depth(r.st, st.depth), r.node, r.h) }
        }
    }
}

/// The loop of `Parser::parse_expr_precedence_inner` with `left` of height `h`.
pub open spec fn p_expr_loop(toks: Seq<Token>, cfg: PCfg, st: PState, left: usize, h: u64, min_prec: i8, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let t = cur_tok(toks, st);
        let info = infix_info(t.kind);
        if info.0 < min_prec {
            if within(st.depth, h, cfg.max_depth) { pr_node(st, left, h) } else { too_deep(st) }
        } else if info.1 {
            syntax_at(st, t.line)
        } else {
            let op = binop_code(t);
            let e = eat(toks, st, t.kind);
            if !e.ok { e } else {
            let r = p_expr_prec(toks, cfg, e.st, info.2, (fuel - 1) as u64);
            if !r.ok { r } else {
            let h2 = inc(max_u64(h, r.h));
            if !within(r.st.depth, h2, cfg.max_depth) { too_deep(r.st) }
            else {
                let n = add_node(r.st, Node::Binary(op, left, r.node), h2);
                p_expr_loop(toks, cfg, n.st, n.node, h2, min_prec, (fuel - 1) as u64)
            }
            }}
        }
    }
}

/// `Parser::parse_prefix`.
pub open spec fn p_prefix(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let t = cur_tok(toks, st);
        if t.kind is Minus {
            let e = eat(toks, st, Tok::Minus);
            if !e.ok { e } else {
            let x = p_expr_prec(toks, cfg, e.st, 5i8, f);
            if !x.ok { x } else { add_node(x.st, Node::Neg(x.node), inc(x.h)) }
            }
        } else if t.kind is IncrDecr {
            let is_inc = t.text.len() > 0 && t.text[0] == 43u8;
            let e = eat(toks, st, Tok::IncrDecr);
            if !e.ok { e } else {
            let x = p_named(toks, cfg, e.st, f);
            if !x.ok { x } else { add_node(x.st, Node::Update(is_inc, true, x.node), inc(x.h)) }
            }
        } else {
            p_primary(toks, cfg, st, f)
        }
    }
}

/// `Parser::parse_parenthesized`.
pub open spec fn p_parenthesized(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let e = eat(toks, st, Tok::Lparen);
        if !e.ok { e } else {
        let x = p_expr_prec(toks, cfg, e.st, 0i8, (fuel - 1) as u64);
        if !x.ok { x } else {
        let e2 = eat(toks, x.st, Tok::Rparen);
        if !e2.ok { e2 } else { pr_node(e2.st, x.node, x.h) }
        }}
    }
}

/// A keyword followed by a parenthesized expression: `length`, `sqrt`, `scale` (`which` 0, 1, 2).
pub open spec fn p_builtin(toks: Seq<Token>, cfg: PCfg, st: PState, which: u8, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let e = eat(toks, st, cur_tok(toks, st).kind);
        if !e.ok { e } else {
        let x = p_parenthesized(toks, cfg, e.st, (fuel - 1) as u64);
        if !x.ok { x }
        else if which == 0 { add_node(x.st, Node::Length(x.node), inc(x.h)) }
        else if which == 1 { add_node(x.st, Node::Sqrt(x.node), inc(x.h)) }
        else { add_node(x.st, Node::ScaleOf(x.node), inc(x.h)) }
        }
    }
}

/// `Parser::parse_primary`.
pub open spec fn p_primary(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let t = cur_tok(toks, st);
        if t.kind is Number {
            let e = eat(toks, st, Tok::Number);
            if !e.ok { e } else { add_node(e.st, Node::Number(t.text), 1u64) }
        } else if t.kind is Lparen {
            let x = p_parenthesized(toks, cfg, st, f);
            if !x.ok { x } else { add_node(x.st, Node::Paren(x.node), inc(x.h)) }
        } else if t.kind is Length {
            p_builtin(toks, cfg, st, 0u8, f)
        } else if t.kind is Sqrt {
            p_builtin(toks, cfg, st, 1u8, f)
        } else if t.kind is Scale || t.kind is Letter {
            let pk = peek_kind(toks, st, 0usize);
            if !pk.0 { lex_err(st, pk.2) }
            else if pk.1 is Lparen && t.kind is Scale { p_builtin(toks, cfg, st, 2u8, f) }
            else if pk.1 is Lparen { p_call(toks, cfg, st, f) }
            else { p_named_tail(toks, cfg, st, f) }
        } else {
            p_named_tail(toks, cfg, st, f)
        }
    }
}

/// A function call `name(args)`.
pub open spec fn p_call(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let n = eat_name(toks, cfg, st);
        if !n.ok { n } else {
        let name = n.name;
        let e = eat(toks, n.st, Tok::Lparen);
        if !e.ok { e } else {
        let a = if cur_tok(toks, e.st).kind is Rparen { pr_args(e.st, seq![], 0u64) } else { p_arg_list(toks, cfg, e.st, seq![], 0u64, (fuel - 1) as u64) };
        if !a.ok { a } else {
        let e2 = eat(toks, a.st, Tok::Rparen);
        if !e2.ok { e2 } else { add_node(e2.st, Node::Call(name, a.args), inc(a.h)) }
        }}}
    }
}

/// The default arm of `parse_primary`: a named expression, then a postfix `++`/`--` or an
/// assignment that binds to it.
pub open spec fn p_named_tail(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let x = p_named(toks, cfg, st, (fuel - 1) as u64);
        if !x.ok { x } else {
        let t = cur_tok(toks, x.st);
        if t.kind is IncrDecr {
            let is_inc = t.text.len() > 0 && t.text[0] == 43u8;
            let e = eat(toks, x.st, Tok::IncrDecr);
            if !e.ok { e } else { add_node(e.st, Node::Update(is_inc, false, x.node), inc(x.h)) }
        } else if t.kind is AssignOp {
            let op = assign_code(t);
            let e = eat(toks, x.st, Tok::AssignOp);
            if !e.ok { e } else {
            let v = p_expr_prec(toks, cfg, e.st, 1i8, (fuel - 1) as u64);
            if !v.ok { v } else { add_node(v.st, Node::Assign(op, x.node, v.node), inc(max_u64(x.h, v.h))) }
            }
        } else {
            x
        }
        }
    }
}

/// `Parser::parse_named_expression`.
pub open spec fn p_named(toks: Seq<Token>, cfg: PCfg, st: PState, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let t = cur_tok(toks, st);
        if t.kind is Scale || t.kind is Ibase || t.kind is Obase {
            let r = if t.kind is Scale { 0u8 } else if t.kind is Ibase { 1u8 } else { 2u8 };
            let e = eat(toks, st, t.kind);
            if !e.ok { e } else { add_node(e.st, Node::Reg(r), 1u64) }
        } else if t.kind is Letter {
            let n = eat_name(toks, cfg, st);
            if !n.ok { n }
            else if cur_tok(toks, n.st).kind is Lbracket { p_subscript(toks, cfg, n.st, n.name, (fuel - 1) as u64) }
            else { add_node(n.st, Node::Var(n.name), 1u64) }
        } else {
            syntax_at(st, t.line)
        }
    }
}

/// `[ expression ]` after an array name.
pub open spec fn p_subscript(toks: Seq<Token>, cfg: PCfg, st: PState, name: Seq<u8>, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let e = eat(toks, st, Tok::Lbracket);
        if !e.ok { e } else {
        let i = p_expr_prec(toks, cfg, e.st, 0i8, (fuel - 1) as u64);
        if !i.ok { i } else {
        let e2 = eat(toks, i.st, Tok::Rbracket);
        if !e2.ok { e2 } else { add_node(e2.st, Node::Array(name, i.node), inc(i.h)) }
        }}
    }
}

/// `Parser::parse_argument_list` after the arguments `acc` of height `h`.
pub open spec fn p_arg_list(toks: Seq<Token>, cfg: PCfg, st: PState, acc: Seq<Arg>, h: u64, fuel: u64) -> PR
    decreases fuel
{
    if fuel == 0 { out_of_fuel(st) }
    else {
        let f = (fuel - 1) as u64;
        let is_letter = cur_tok(toks, st).kind is Letter;
        let p0 = if is_letter { peek_kind(toks, st, 0usize) } else { (true, Tok::Eof, cur_tok(toks, st)) };
        let p1 = if is_letter && p0.0 && p0.1 is Lbracket { peek_kind(toks, st, 1usize) } else { (true, Tok::Eof, cur_tok(toks, st)) };
        if !p0.0 { lex_err(st, p0.2) }
        else if !p1.0 { lex_err(st, p1.2) }
        else {
            let is_arr = is_letter && p0.1 is Lbracket && p1.1 is Rbracket;
            let a = if is_arr {
                let n = eat_name(toks, cfg, st);
                if !n.ok { n } else {
                let e1 = eat(toks, n.st, Tok::Lbracket);
                if !e1.ok { e1 } else {
                let e2 = eat(toks, e1.st, Tok::Rbracket);
                if !e2.ok { e2 } else {
                PR { ok: true, err: no_err(), st: e2.st, node: 0usize, h: 1u64, flag: false, list: seq![], params: seq![], args: seq![], name: n.name }
                }}}
            } else {
                p_expr_prec(toks, cfg, st, 0i8, f)
            };
            if !a.ok { a } else {
            let arg = Arg { is_array: is_arr, name: a.name, expr: a.node };
            let acc2 = acc.push(arg);
            let h2 = max_u64(h, a.h);
            if cur_tok(toks, a.st).kind is Comma {
                let e = eat(toks, a.st, Tok::Comma);
                if !e.ok { e } else { p_arg_list(toks, cfg, e.st, acc2, h2, f) }
            } else { pr_args(a.st, acc2, h2) }
            }
        }
    }
}

/// Parses a unit: `Parser::try_new` and `try_parse_program`. `list` holds the items.
pub open spec fn parse_unit(toks: Seq<Token>, cfg: PCfg) -> PR {
    let st0 = PState { cur: 0usize, depth: 0u64, last_line: 1u64, loop_depth: 0u64, in_function: false, ext: seq![], nodes: seq![] };
    if lex_error_at(toks, 0usize) { lex_err(st0, token_at(toks, 0usize)) }
    else { p_program(toks, cfg, st0, seq![], 0x4000_0000_0000_0000u64) }
}

} // exec_spec_verified!

} // verus!
