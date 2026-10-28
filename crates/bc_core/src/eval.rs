// SPDX-License-Identifier: MIT

//! Tree-walking AST evaluator and dynamic scope manager for the bc clone.
//!
//! Complies with POSIX bc specifications for registers, arrays, function definitions,
//! dynamic scope resolution, and WrappedStdout formatting.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt::Write as FmtWrite;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

use crate::error::{BcError, RuntimeError};
use crate::format::wrap_output;
use crate::math::{BCNum, pow10};
use crate::parser::{
    AssignOp, BinOp, DEFAULT_MAX_DEPTH, Expr, ExprOrArray, ExtensionPolicy, FunctionDef, Register,
    RelOp, Stmt,
};
#[cfg(verus_keep_ghost)]
use crate::refine::*;
use crate::verified_kernels::{
    BC_BASE_MAX, BC_DIM_MAX, BC_SCALE_MAX, IBASE_MAX, verified_clamp_register,
    verified_hex_char_val, verified_loop_post_body_action, verified_nesting_within_limit,
    verified_should_abort_execution,
};
#[cfg(verus_keep_ghost)]
use bc_spec::eval::EState;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Abstract output writer trait compatible with both no_std and std environments.
pub trait BcWriter: FmtWrite + Send {
    /// Flushes any buffered content.
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

impl BcWriter for String {}

impl WrappedStdout {
    /// Creates a new WrappedStdout writing to the given writer.
    pub fn new(writer: Box<dyn BcWriter>) -> Self {
        Self { writer, col: 0 }
    }

    /// Writes a string to the output stream with POSIX line wrapping: a backslash-newline
    /// before a character at column 68 or beyond (`format::wrap_output`, verified against the
    /// specification's `write_wrapped`).
    pub fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let (out, col) = wrap_output(self.col, s.as_bytes());
        self.col = col;
        // Backslash-newlines go only before the first byte of a character, so `out` is UTF-8.
        match core::str::from_utf8(&out) {
            Ok(text) => self.writer.write_str(text),
            Err(_) => Err(core::fmt::Error),
        }
    }

    /// Flushes the underlying writer.
    pub fn flush(&mut self) -> core::fmt::Result {
        self.writer.flush()
    }
}

verus! {

/// Wrapper to write output characters with POSIX-style 70-character line wrapping. Opaque to
/// Verus: the refinement proofs see it through `out_log` and `out_col`.
#[verifier::external_body]
pub struct WrappedStdout {
    writer: Box<dyn BcWriter>,
    col: usize,
}

/// The diagnostic stream. Opaque to Verus: the refinement proofs see it through `err_log`.
#[verifier::external_body]
pub struct ErrWriter {
    writer: Box<dyn BcWriter>,
}

/// The bytes written to standard output so far (the model of the output stream).
pub uninterp spec fn out_log(w: &WrappedStdout) -> Seq<u8>;

/// The output column of standard output (`write_wrapped`'s column).
pub uninterp spec fn out_col(w: &WrappedStdout) -> u64;

/// The bytes written to the diagnostic stream so far.
pub uninterp spec fn err_log(w: &ErrWriter) -> Seq<u8>;

/// Evaluator maintaining registers, scoped variables, functions, and state.
pub struct Evaluator {
    pub variables: BTreeMap<String, Vec<BCNum>>,
    pub arrays: BTreeMap<String, Vec<BTreeMap<usize, BCNum>>>,
    pub functions: BTreeMap<String, FunctionDef>,
    // Registers are private so that every value stays within its valid range; in particular
    // `scale <= BC_SCALE_MAX` is what the verified scale kernels rely on.
    pub(crate) scale: usize,
    pub(crate) ibase: usize,
    pub(crate) obase: usize,
    pub math_enabled: bool,
    pub stdout_writer: WrappedStdout,
    pub stderr_writer: ErrWriter,

    pub break_flag: bool,
    pub return_flag: bool,
    pub return_value: BCNum,
    pub quit_flag: bool,
    /// How non-POSIX syntax is treated (`-s` / `-w`); applied by the input-unit driver.
    pub extension_policy: ExtensionPolicy,

    /// Names of the user functions currently executing, innermost last (for diagnostics).
    pub(crate) call_stack: Vec<String>,

    /// Nesting limit: the syntax tree of an input unit is at most this deep, and at most this
    /// many expressions and statements (across function calls) are evaluated at once. It bounds
    /// the native stack that parsing and evaluation use (`docs/COMPATIBILITY.md` §2), so a
    /// front end sets it for the stack it runs on.
    pub max_depth: usize,
    /// Expressions and statements currently being evaluated.
    pub(crate) eval_depth: usize,
    /// `ibase` when the innermost executing function was invoked (`None` at top level). POSIX:
    /// numeric constants within a function are interpreted in this base.
    pub(crate) invocation_ibase: Option<usize>,
}

/// An assignment target whose array subscript has already been evaluated.
enum Place {
    Variable(String),
    Element(String, usize),
    Register(Register),
}

/// The caller's state saved when a function is entered, restored by `Evaluator::leave_call`.
struct SavedCall {
    return_flag: bool,
    return_value: BCNum,
    invocation_ibase: Option<usize>,
}

/// The output streams as written so far.
pub(crate) open spec fn r_output(out: WrappedStdout, err: ErrWriter, st: EState) -> bool {
    out_log(&out) == st.out && out_col(&out) == st.col && err_log(&err) == st.err
}

/// The whole evaluator state corresponds to the specification's `EState` (without `-l`).
pub(crate) open spec fn r_state(e: Evaluator, st: EState) -> bool {
    &&& !e.math_enabled
    &&& r_vars(e.variables@, st.vars)
    &&& r_arrays(e.arrays@, st.arrays)
    &&& r_funcs(e.functions@, st.funcs)
    &&& e.scale == st.scale && e.ibase == st.ibase && e.obase == st.obase
    &&& e.break_flag == st.brk && e.return_flag == st.ret && r_num(e.return_value, st.ret_val)
    &&& r_calls(e.call_stack@, st.calls)
    &&& e.eval_depth == st.depth && e.max_depth == st.max_depth
    &&& match e.invocation_ibase {
        Some(b) => st.has_inv && b == st.inv_ibase,
        None => !st.has_inv,
    }
    &&& r_output(e.stdout_writer, e.stderr_writer, st)
}

} // verus!

impl ErrWriter {
    /// Creates the diagnostic stream writing to the given writer.
    pub fn new(writer: Box<dyn BcWriter>) -> Self {
        Self { writer }
    }

    /// Flushes the underlying writer.
    pub fn flush(&mut self) -> core::fmt::Result {
        self.writer.flush()
    }

    /// Writes formatted text, so that `writeln!(evaluator.stderr_writer, ...)` works without
    /// importing `fmt::Write`.
    pub fn write_fmt(&mut self, args: core::fmt::Arguments<'_>) -> core::fmt::Result {
        FmtWrite::write_fmt(self, args)
    }
}

impl FmtWrite for ErrWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.writer.write_str(s)
    }
}

impl Evaluator {
    /// Creates a new Evaluator with abstract BcWriter streams.
    pub fn new(
        math_enabled: bool,
        stdout_writer: Box<dyn BcWriter>,
        stderr_writer: Box<dyn BcWriter>,
    ) -> Self {
        Self {
            variables: BTreeMap::new(),
            arrays: BTreeMap::new(),
            functions: BTreeMap::new(),
            scale: 0,
            ibase: 10,
            obase: 10,
            math_enabled,
            stdout_writer: WrappedStdout::new(stdout_writer),
            stderr_writer: ErrWriter::new(stderr_writer),
            break_flag: false,
            return_flag: false,
            return_value: BCNum::zero(),
            quit_flag: false,
            extension_policy: ExtensionPolicy::Allow,
            call_stack: Vec::new(),
            max_depth: DEFAULT_MAX_DEPTH,
            eval_depth: 0,
            invocation_ibase: None,
        }
    }

    /// The `scale` register.
    pub fn scale(&self) -> usize {
        self.scale
    }

    /// The `ibase` register.
    pub fn ibase(&self) -> usize {
        self.ibase
    }

    /// The `obase` register.
    pub fn obase(&self) -> usize {
        self.obase
    }

    /// Sets the `scale` register (e.g. a front end's default scale), clamped to `BC_SCALE_MAX`.
    pub fn set_scale(&mut self, scale: usize) {
        self.scale = verified_clamp_register(scale, false, 0, BC_SCALE_MAX).0;
    }

    /// Writes `Runtime warning (func=<current function>): <msg>` to the diagnostic stream.
    fn warn(&mut self, msg: &str) {
        let func = self.call_stack.last().map_or("(main)", String::as_str);
        let _ = writeln!(
            self.stderr_writer,
            "Runtime warning (func={}): {}",
            func, msg
        );
    }

    /// Resolves an assignment target, evaluating an array subscript exactly once. Returns
    /// `None` for an expression that is not a named expression (the parser never produces one).
    fn resolve_place(&mut self, target: &Expr) -> Result<Option<Place>, BcError> {
        Ok(match target {
            Expr::Variable(name) => Some(Place::Variable(name.clone())),
            Expr::ArrayAccess(name, index_expr) => {
                let idx = self.try_evaluate(index_expr)?;
                Some(Place::Element(name.clone(), Self::array_index(name, &idx)?))
            }
            Expr::RegisterAccess(reg) => Some(Place::Register(*reg)),
            _ => None,
        })
    }

    /// Reads the current value of a resolved target.
    fn load(&mut self, place: &Place) -> BCNum {
        match place {
            Place::Variable(name) => self.variable_top(name.clone()).clone(),
            Place::Element(name, index) => self
                .array_top(name.clone())
                .get(index)
                .cloned()
                .unwrap_or_else(BCNum::zero),
            Place::Register(reg) => BCNum::new(BigInt::from(self.register(*reg)), 0),
        }
    }

    /// Writes `val` to a resolved target and returns the value now held there (registers clamp
    /// it to their range).
    fn store(&mut self, place: Place, val: &BCNum) -> BCNum {
        match place {
            Place::Variable(name) => {
                *self.variable_top(name) = val.clone();
            }
            Place::Element(name, index) => {
                self.array_top(name).insert(index, val.clone());
            }
            Place::Register(reg) => {
                let stored = self.store_register(reg, val);
                return BCNum::new(BigInt::from(stored), 0);
            }
        }
        val.clone()
    }

    fn register(&self, reg: Register) -> usize {
        match reg {
            Register::Scale => self.scale,
            Register::Ibase => self.ibase,
            Register::Obase => self.obase,
        }
    }

    /// The innermost frame of a scope stack. The evaluator keeps a global frame at the bottom of
    /// every stack; a stack emptied through the public `variables`/`arrays` fields gets a fresh
    /// one from `init`, so this never fails.
    /// The current value of variable `name`.
    fn variable_top(&mut self, name: String) -> &mut BCNum {
        let stack = self.variable_stack(name);
        if stack.is_empty() {
            stack.push(BCNum::zero());
        }
        let top = stack.len() - 1;
        &mut stack[top]
    }

    /// The current frame of array `name`.
    fn array_top(&mut self, name: String) -> &mut BTreeMap<usize, BCNum> {
        let stack = self.array_stack(name);
        if stack.is_empty() {
            stack.push(BTreeMap::new());
        }
        let top = stack.len() - 1;
        &mut stack[top]
    }

    /// The scope stack of variable `name`, created with its global frame (0) if needed.
    fn variable_stack(&mut self, name: String) -> &mut Vec<BCNum> {
        self.variables
            .entry(name)
            .or_insert_with(|| vec![BCNum::zero()])
    }

    /// The scope stack of array `name`, created with its global frame (empty) if needed.
    fn array_stack(&mut self, name: String) -> &mut Vec<BTreeMap<usize, BCNum>> {
        self.arrays
            .entry(name)
            .or_insert_with(|| vec![BTreeMap::new()])
    }

    /// Whether an expression statement is an assignment, whose value is not printed (POSIX).
    /// As in GNU bc, unary minus keeps that property (`-a = 5` prints nothing) and parentheses
    /// remove it (`(a = 5)` prints 5).
    fn is_assignment(expr: &Expr) -> bool {
        match expr {
            Expr::AssignOp(..) => true,
            Expr::Negate(inner) => Self::is_assignment(inner),
            _ => false,
        }
    }

    /// Converts the subscript `idx` of array `name` to an index, truncating it to an integer.
    /// Negative subscripts and subscripts of at least `BC_DIM_MAX` are runtime errors.
    fn array_index(name: &str, idx: &BCNum) -> Result<usize, BcError> {
        let index = &idx.coeff / pow10(idx.scale);
        match index.to_usize() {
            Some(i) if !idx.coeff.is_negative() && i < BC_DIM_MAX => Ok(i),
            _ => Err(RuntimeError::ArraySubscriptOutOfBounds(String::from(name)).into()),
        }
    }

    /// Stores `val`, truncated to an integer, into register `reg`, clamping it to the register's range with a warning (`docs/COMPATIBILITY.md`
    /// §3.3). Returns the stored value.
    fn store_register(&mut self, reg: Register, val: &BCNum) -> usize {
        let magnitude = (&val.coeff / pow10(val.scale))
            .abs()
            .to_usize()
            .unwrap_or(usize::MAX);
        let (min, max) = match reg {
            Register::Scale => (0, BC_SCALE_MAX),
            Register::Ibase => (2, IBASE_MAX),
            Register::Obase => (2, BC_BASE_MAX),
        };
        let name = reg.name();
        let (v, kind) = verified_clamp_register(magnitude, val.coeff.is_negative(), min, max);
        match kind {
            -2 => self.warn(&format!("negative {}, set to {}", name, min)),
            -1 => self.warn(&format!("{} too small, set to {}", name, min)),
            1 => self.warn(&format!("{} too large, set to {}", name, max)),
            _ => {}
        }
        match reg {
            Register::Scale => self.scale = v,
            Register::Ibase => self.ibase = v,
            Register::Obase => self.obase = v,
        }
        v
    }

    /// Converts a numeric literal: at top level in the current `ibase`, and in a function body
    /// in the `ibase` in effect when the function was invoked (POSIX). A literal with more than
    /// `BC_SCALE_MAX` fractional digits is rejected to keep the scale invariant.
    fn literal(&self, digits: &str) -> Result<BCNum, BcError> {
        Ok(BCNum::try_from_string(
            digits,
            self.invocation_ibase.unwrap_or(self.ibase),
        )?)
    }

    /// Computes `base ^ exp`, warning when the exponent has a fractional part.
    fn power(&mut self, base: &BCNum, exp: &BCNum) -> Result<BCNum, BcError> {
        if exp.scale > 0 {
            self.warn("non-zero scale in exponent");
        }
        Ok(base.try_pow(exp, self.scale)?)
    }

    /// Executes a function body, stopping after `return` (or `quit`).
    fn run_body(&mut self, body: &[Stmt]) -> Result<(), BcError> {
        for stmt in body {
            self.try_execute(stmt)?;
            if self.return_flag || self.quit_flag {
                break;
            }
        }
        Ok(())
    }

    /// Leaves function `func`: pops the call, restores the caller's return state and
    /// invocation `ibase`, and pops the `auto` frames and then the parameter frames, each list
    /// last first (the specification's `leave_call`).
    fn leave_call(&mut self, func: &FunctionDef, saved: SavedCall) {
        self.call_stack.pop();
        self.return_flag = saved.return_flag;
        self.return_value = saved.return_value;
        self.invocation_ibase = saved.invocation_ibase;
        for param in func.autos.iter().rev().chain(func.params.iter().rev()) {
            if param.is_array {
                if let Some(stack) = self.arrays.get_mut(&param.name) {
                    stack.pop();
                }
            } else if let Some(stack) = self.variables.get_mut(&param.name) {
                stack.pop();
            }
        }
    }

    /// `l <op> r` at the current `scale` (the specification's `arith`).
    fn arith(&mut self, op: BinOp, l: &BCNum, r: &BCNum) -> Result<BCNum, BcError> {
        match op {
            BinOp::Add => Ok(l.add(r)),
            BinOp::Sub => Ok(l.sub(r)),
            BinOp::Mul => Ok(l.mul(r, self.scale)),
            BinOp::Div => Ok(l.try_div(r, self.scale)?),
            BinOp::Mod => Ok(l.try_mod_op(r, self.scale)?),
            BinOp::Pow => self.power(l, r),
        }
    }

    /// Evaluates an AST expression node, returning Err on runtime math/call errors.
    pub fn try_evaluate(&mut self, node: &Expr) -> Result<BCNum, BcError> {
        self.enter_eval()?;
        let result = self.evaluate_node(node);
        self.eval_depth -= 1;
        result
    }

    /// Counts one more level of evaluation, failing with `NestingTooDeep` beyond `max_depth`.
    /// Every caller decrements `eval_depth` when the level is left; `bc_core` does not unwind.
    fn enter_eval(&mut self) -> Result<(), BcError> {
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_depth) {
            return Err(RuntimeError::NestingTooDeep.into());
        }
        self.eval_depth += 1;
        Ok(())
    }

    fn evaluate_node(&mut self, node: &Expr) -> Result<BCNum, BcError> {
        match node {
            Expr::Number(value) => self.literal(value),
            Expr::Variable(name) => Ok(self.variable_top(name.clone()).clone()),
            Expr::ArrayAccess(name, index_expr) => {
                let idx = self.try_evaluate(index_expr)?;
                let idx_val = Self::array_index(name, &idx)?;
                Ok(self
                    .array_top(name.clone())
                    .get(&idx_val)
                    .cloned()
                    .unwrap_or_else(BCNum::zero))
            }
            Expr::RegisterAccess(reg) => Ok(BCNum::new(BigInt::from(self.register(*reg)), 0)),
            Expr::Negate(expr) => {
                let val = self.try_evaluate(expr)?;
                Ok(BCNum::new(-val.coeff, val.scale))
            }
            Expr::BinaryOp(op, left, right) => {
                let l = self.try_evaluate(left)?;
                let r = self.try_evaluate(right)?;
                self.arith(*op, &l, &r)
            }
            Expr::RelationalOp(op, left, right) => {
                let l = self.try_evaluate(left)?;
                let r = self.try_evaluate(right)?;
                let ord = l.cmp_val(&r);
                let res = match op {
                    RelOp::Eq => ord == Ordering::Equal,
                    RelOp::Ne => ord != Ordering::Equal,
                    RelOp::Lt => ord == Ordering::Less,
                    RelOp::Le => ord != Ordering::Greater,
                    RelOp::Gt => ord == Ordering::Greater,
                    RelOp::Ge => ord != Ordering::Less,
                };
                Ok(BCNum::new(BigInt::from(if res { 1 } else { 0 }), 0))
            }
            Expr::AssignOp(op, target, expr) => {
                // The named expression is evaluated once, before the right-hand side, as in
                // GNU bc: `a[i++] = i` stores into a[0], and `c += c++` adds the old value.
                let place = self.resolve_place(target)?;

                let val = match (&place, op, &**expr) {
                    // POSIX: a single digit assigned to ibase or obase is read as hexadecimal.
                    (
                        Some(Place::Register(Register::Ibase | Register::Obase)),
                        AssignOp::Assign,
                        Expr::Number(digits),
                    ) if digits.replace("\\\n", "").len() == 1 => {
                        let b = digits.replace("\\\n", "").as_bytes()[0];
                        BCNum::new(BigInt::from(verified_hex_char_val(b)), 0)
                    }
                    (_, AssignOp::Assign, _) => self.try_evaluate(expr)?,
                    (_, AssignOp::Compound(bin), _) => {
                        let old_val = match &place {
                            Some(place) => self.load(place),
                            None => self.try_evaluate(target)?,
                        };
                        let rhs = self.try_evaluate(expr)?;
                        self.arith(*bin, &old_val, &rhs)?
                    }
                };

                // As in GNU bc, the value of the assignment is the value assigned, even when a
                // register clamps it.
                if let Some(place) = place {
                    self.store(place, &val);
                }
                Ok(val)
            }
            Expr::Update(increment, is_prefix, target) => {
                let place = self.resolve_place(target)?;
                let old_val = match &place {
                    Some(place) => self.load(place),
                    None => self.try_evaluate(target)?,
                };
                let step = BCNum::new(BigInt::from(1), 0);
                let new_val = if *increment {
                    old_val.add(&step)
                } else {
                    old_val.sub(&step)
                };
                let stored = match place {
                    Some(place) => self.store(place, &new_val),
                    None => new_val,
                };
                Ok(if *is_prefix { stored } else { old_val })
            }
            Expr::Call(name, args) => {
                if let Some(func) = self.functions.get(name).cloned() {
                    if args.len() != func.params.len() {
                        return Err(RuntimeError::ParameterMismatch.into());
                    }

                    /// A parameter value, evaluated before any frame is pushed.
                    enum ArgValue {
                        Array(BTreeMap<usize, BCNum>),
                        Scalar(BCNum),
                    }
                    let mut evaluated_args = Vec::new();
                    for (i, arg) in args.iter().enumerate() {
                        let param = &func.params[i];
                        if param.is_array {
                            if let ExprOrArray::ArrayArg(arg_name) = arg {
                                let arr_copy = self.array_top(arg_name.clone()).clone();
                                evaluated_args
                                    .push((param.name.clone(), ArgValue::Array(arr_copy)));
                            } else {
                                return Err(RuntimeError::ParameterTypeMismatch(
                                    param.name.clone(),
                                )
                                .into());
                            }
                        } else if let ExprOrArray::Expr(expr) = arg {
                            let val = self.try_evaluate(expr)?;
                            evaluated_args.push((param.name.clone(), ArgValue::Scalar(val)));
                        } else {
                            return Err(
                                RuntimeError::ParameterTypeMismatch(param.name.clone()).into()
                            );
                        }
                    }

                    // Every name keeps its global frame at the bottom of its stack, so popping
                    // the function's frames in `leave_call` never leaves an empty stack
                    // (a name first seen as a parameter or `auto` stays usable afterwards).
                    for (pname, value) in evaluated_args {
                        match value {
                            ArgValue::Array(arr) => self.array_stack(pname).push(arr),
                            ArgValue::Scalar(val) => self.variable_stack(pname).push(val),
                        }
                    }

                    for auto in &func.autos {
                        if auto.is_array {
                            self.array_stack(auto.name.clone()).push(BTreeMap::new());
                        } else {
                            self.variable_stack(auto.name.clone()).push(BCNum::zero());
                        }
                    }

                    let saved = SavedCall {
                        return_flag: self.return_flag,
                        return_value: self.return_value.clone(),
                        invocation_ibase: self.invocation_ibase.replace(self.ibase),
                    };
                    self.return_flag = false;
                    self.return_value = BCNum::zero();
                    self.call_stack.push(name.clone());

                    let body = self.run_body(&func.body).map_err(|e| e.in_function(name));
                    let ret_val = self.return_value.clone();
                    // Restored on every return path, including errors.
                    self.leave_call(&func, saved);
                    return body.map(|()| ret_val);
                }

                if self.math_enabled {
                    use crate::math::{bc_atan, bc_bessel, bc_cos, bc_exp, bc_ln, bc_sin};
                    match (name.as_str(), args.as_slice()) {
                        ("s", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_sin(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("c", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_cos(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("a", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_atan(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("l", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_ln(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("e", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_exp(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("j", [ExprOrArray::Expr(expr_n), ExprOrArray::Expr(expr_x)]) => {
                            let n_val = self.try_evaluate(expr_n)?;
                            let x_val = self.try_evaluate(expr_x)?;
                            return Ok(bc_bessel(&n_val, &x_val, self.scale)?);
                        }
                        _ => {}
                    }
                }

                Err(RuntimeError::UndefinedFunction(name.clone()).into())
            }
            Expr::LengthCall(expr) => Ok(self.try_evaluate(expr)?.length()),
            Expr::SqrtCall(expr) => self
                .try_evaluate(expr)?
                .try_sqrt(self.scale)
                .map_err(BcError::from),
            Expr::ScaleCall(expr) => Ok(self.try_evaluate(expr)?.scale_func()),
            Expr::Paren(expr) => self.try_evaluate(expr),
        }
    }

    /// Evaluates an AST expression node and returns a BCNum.
    #[cfg(test)]
    pub fn evaluate(&mut self, node: &Expr) -> BCNum {
        self.try_evaluate(node).unwrap_or_else(|e| panic!("{}", e))
    }

    /// Executes an AST statement node, returning Err on runtime errors.
    pub fn try_execute(&mut self, node: &Stmt) -> Result<(), BcError> {
        self.enter_eval()?;
        let result = self.execute_node(node);
        self.eval_depth -= 1;
        result
    }

    fn execute_node(&mut self, node: &Stmt) -> Result<(), BcError> {
        if verified_should_abort_execution(self.break_flag, self.return_flag, self.quit_flag) {
            return Ok(());
        }

        match node {
            Stmt::Block(stmts) => {
                for stmt in stmts {
                    self.try_execute(stmt)?;
                    if verified_should_abort_execution(
                        self.break_flag,
                        self.return_flag,
                        self.quit_flag,
                    ) {
                        break;
                    }
                }
            }
            Stmt::Expr(expr) => {
                if Self::is_assignment(expr) {
                    self.try_evaluate(expr)?;
                } else {
                    let val = self.try_evaluate(expr)?;
                    let out_str = val.format_obase(self.obase);
                    let _ = self.stdout_writer.write_str(&format!("{}\n", out_str));
                    let _ = self.stdout_writer.flush();
                }
            }
            Stmt::StringLiteral(s) => {
                let _ = self.stdout_writer.write_str(s);
                let _ = self.stdout_writer.flush();
            }
            Stmt::Break => {
                self.break_flag = true;
            }
            Stmt::Quit => {
                self.quit_flag = true;
            }
            Stmt::Return(expr_opt) => {
                if let Some(expr) = expr_opt {
                    self.return_value = self.try_evaluate(expr)?;
                } else {
                    self.return_value = BCNum::zero();
                }
                self.return_flag = true;
            }
            Stmt::If(cond, body) => {
                let c = self.try_evaluate(cond)?;
                if !c.is_zero() {
                    self.try_execute(body)?;
                }
            }
            Stmt::While(cond, body) => loop {
                let c = self.try_evaluate(cond)?;
                if c.is_zero() || self.quit_flag {
                    break;
                }
                self.try_execute(body)?;
                let (should_break, next_break) = verified_loop_post_body_action(
                    self.break_flag,
                    self.return_flag,
                    self.quit_flag,
                );
                self.break_flag = next_break;
                if should_break {
                    break;
                }
            },
            Stmt::For(init, cond, post, body) => {
                self.try_evaluate(init)?;
                loop {
                    let c = self.try_evaluate(cond)?;
                    if c.is_zero() || self.quit_flag {
                        break;
                    }
                    self.try_execute(body)?;
                    let (should_break, next_break) = verified_loop_post_body_action(
                        self.break_flag,
                        self.return_flag,
                        self.quit_flag,
                    );
                    self.break_flag = next_break;
                    if should_break {
                        break;
                    }
                    self.try_evaluate(post)?;
                }
            }
            Stmt::FunctionDef(func) => {
                self.functions.insert(func.name.clone(), func.clone());
            }
        }
        Ok(())
    }

    /// Executes an AST statement node.
    #[cfg(test)]
    pub fn execute(&mut self, node: &Stmt) {
        self.try_execute(node).unwrap_or_else(|e| panic!("{}", e))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Lexer;
    use crate::parser::Param;
    use crate::parser::Parser;
    use alloc::string::ToString;

    #[derive(Clone)]
    struct TestWriter {
        buf: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
    }

    impl FmtWrite for TestWriter {
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            self.buf.lock().unwrap().extend_from_slice(s.as_bytes());
            Ok(())
        }
    }

    impl BcWriter for TestWriter {
        fn flush(&mut self) -> core::fmt::Result {
            Ok(())
        }
    }

    fn test_eval(input: &str) -> (String, String) {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let stmts = parser.parse_program();

        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));

        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };

        let mut eval = Evaluator::new(true, Box::new(stdout), Box::new(stderr));

        for stmt in &stmts {
            eval.execute(stmt);
        }

        let out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        (out, err)
    }

    #[test]
    fn test_emptied_public_scope_stacks_do_not_panic() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: std::sync::Arc::new(std::sync::Mutex::new(Vec::new())),
        };
        let mut eval = Evaluator::new(false, Box::new(stdout), Box::new(stderr));
        // An embedder may leave an empty stack in the public fields; reads see the global
        // default and writes recreate the frame.
        eval.variables.insert("x".to_string(), Vec::new());
        eval.arrays.insert("a".to_string(), Vec::new());
        eval.arrays.insert("b".to_string(), Vec::new());
        let summary = eval.run_source(
            "x; a[0]; x += 2; x; a[1] = 3; a[1]\ndefine f(c[]) {\nreturn (c[0])\n}\nf(b[])\n",
            "(test)",
        );
        assert_eq!(summary.errors, 0);
        let out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(out, "0\n0\n2\n3\n0\n");
    }

    #[test]
    fn test_evaluator_basic() {
        let (out, _) = test_eval("1 + 2; 5 * 6");
        assert_eq!(out, "3\n30\n");
    }

    #[test]
    fn test_scoping_functions() {
        let input = "
            define f(x) {
                auto a;
                a = 10;
                return (x + a);
            }
            f(5)
        ";
        let (out, _) = test_eval(input);
        assert_eq!(out, "15\n");
    }

    #[test]
    fn test_while_loop() {
        let input = "
            a = 0;
            while (a < 3) {
                a = a + 1;
                a;
            }
        ";
        let (out, _) = test_eval(input);
        assert_eq!(out, "1\n2\n3\n");
    }

    #[test]
    fn test_ibase_warning() {
        let (_, err1) = test_eval("ibase = 1");
        assert!(err1.contains("ibase too small"));

        let (_, err2) = test_eval("ibase = 20");
        assert!(err2.contains("ibase too large"));
    }

    #[test]
    fn test_eval_uncovered_lines() {
        use crate::parser::{Expr, ExprOrArray, FunctionDef, Param, Register, Stmt};

        let mut evaluator = Evaluator::new(true, Box::new(String::new()), Box::new(String::new()));

        // 1. Array access with fractional index (lines 108-109)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::ArrayAccess(
                "a".to_string(),
                Box::new(Expr::Number("1.5".to_string())),
            )),
            Box::new(Expr::Number("42".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::ArrayAccess(
            "a".to_string(),
            Box::new(Expr::Number("1.5".to_string())),
        )));

        // 6. Assign single non-hex char to ibase and obase
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("Z".to_string())),
        )));
        assert_eq!(evaluator.ibase, 2);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("Z".to_string())),
        )));
        assert_eq!(evaluator.obase, 2);

        // Assign single non-hex char to variable (distinguishes is_base_reg && op == "=" from ||)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("var_g".to_string())),
            Box::new(Expr::Number("G".to_string())),
        )));
        let var_g = evaluator.evaluate(&Expr::Variable("var_g".to_string()));
        assert_eq!(var_g.coeff, BigInt::from(16));

        // 8. Assign fractional value to register (lines 257-258)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("2.5".to_string())),
        )));

        // 9. obase < 2 update (line 290)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("1".to_string())),
        )));

        // 10. Update of a non-named expression (unreachable from the parser)
        let node_update_unreach = Expr::Update(true, true, Box::new(Expr::Number("1".to_string())));
        let res_unreach_val = evaluator.evaluate(&node_update_unreach);
        assert_eq!(res_unreach_val.coeff, BigInt::from(2));

        // 10b. Additional tests for ibase single-character assignment edge cases
        // A) multi-character number (cleaned.len() != 1)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("10".to_string())),
        )));
        // B) non-number (expr is not Expr::Number)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Variable("x".to_string())),
        )));
        // C) single character non-hex digit (c is not ascii digit or A-F)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number(".".to_string())),
        )));

        // AssignOp non-lvalue target fallback (line 301)
        let node_assign_unreach = Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Number("1".to_string())),
            Box::new(Expr::Number("2".to_string())),
        );
        let res_assign_unreach = evaluator.evaluate(&node_assign_unreach);
        assert_eq!(res_assign_unreach.coeff, BigInt::from(2));

        // 11. Increment/decrement array at a fractional index (lines 325-326)
        evaluator.execute(&Stmt::Expr(Expr::Update(
            true,
            true,
            Box::new(Expr::ArrayAccess(
                "a".to_string(),
                Box::new(Expr::Number("1.5".to_string())),
            )),
        )));

        // 12. Increment/decrement a register with a fractional value (lines 340-341)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("2.5".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::Update(
            true,
            true,
            Box::new(Expr::RegisterAccess(Register::Scale)),
        )));

        // 13. Update obase with cap (line 360)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("2".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::Update(
            false,
            true,
            Box::new(Expr::RegisterAccess(Register::Obase)),
        )));

        // 14. Function argument errors (lines 379, 399, 405)
        evaluator.functions.insert(
            "f_param_err".to_string(),
            FunctionDef {
                name: "f_param_err".to_string(),
                params: vec![Param {
                    name: "x".to_string(),
                    is_array: false,
                }],
                autos: vec![],
                body: vec![],
            },
        );
        let res_f_arg_cnt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluator.evaluate(&Expr::Call("f_param_err".to_string(), vec![]));
        }));
        assert!(res_f_arg_cnt.is_err());

        let res_f_arg_arr_mismatch = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluator.evaluate(&Expr::Call(
                "f_param_err".to_string(),
                vec![ExprOrArray::ArrayArg("a".to_string())],
            ));
        }));
        assert!(res_f_arg_arr_mismatch.is_err());

        evaluator.functions.insert(
            "f_arr_err".to_string(),
            FunctionDef {
                name: "f_arr_err".to_string(),
                params: vec![Param {
                    name: "x".to_string(),
                    is_array: true,
                }],
                autos: vec![],
                body: vec![],
            },
        );
        let res_f_arr_expr_mismatch =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                evaluator.evaluate(&Expr::Call(
                    "f_arr_err".to_string(),
                    vec![ExprOrArray::Expr(Expr::Number("1".to_string()))],
                ));
            }));
        assert!(res_f_arr_expr_mismatch.is_err());

        // 15. Undefined function call in math mode (line 500)
        let res_undef_func = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluator.evaluate(&Expr::Call("nonexistent".to_string(), vec![]));
        }));
        assert!(res_undef_func.is_err());

        // 16. Early execute return (line 515)
        evaluator.break_flag = true;
        evaluator.execute(&Stmt::Expr(Expr::Number("10".to_string())));
        evaluator.break_flag = false;

        // 17. Stmt::Quit execution (lines 544-546)
        evaluator.execute(&Stmt::Quit);
        assert!(evaluator.quit_flag);

        // 18. Uninitialized variables and arrays access to cover entry().or_insert_with() closures
        let _ = evaluator.evaluate(&Expr::Variable("uninit_var".to_string()));
        let _ = evaluator.evaluate(&Expr::ArrayAccess(
            "uninit_arr".to_string(),
            Box::new(Expr::Number("0".to_string())),
        ));
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("uninit_var_assign".to_string())),
            Box::new(Expr::Number("10".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::ArrayAccess(
                "uninit_arr_assign".to_string(),
                Box::new(Expr::Number("0".to_string())),
            )),
            Box::new(Expr::Number("10".to_string())),
        )));
        let _ = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::Variable("uninit_var_inc".to_string())),
        ));
        let _ = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::ArrayAccess(
                "uninit_arr_inc".to_string(),
                Box::new(Expr::Number("0".to_string())),
            )),
        ));
        evaluator.functions.insert(
            "f_uninit_arr_arg".to_string(),
            FunctionDef {
                name: "f_uninit_arr_arg".to_string(),
                params: vec![Param {
                    name: "x".to_string(),
                    is_array: true,
                }],
                autos: vec![],
                body: vec![],
            },
        );
        let _ = evaluator.evaluate(&Expr::Call(
            "f_uninit_arr_arg".to_string(),
            vec![ExprOrArray::ArrayArg("uninit_arr_arg".to_string())],
        ));

        // 19. Frames are restored when a function returns an error
        evaluator.quit_flag = false;
        evaluator.variables.insert(
            "shadowed_var".to_string(),
            vec![BCNum::new(BigInt::from(99), 0)],
        );
        evaluator.functions.insert(
            "f_panic".to_string(),
            FunctionDef {
                name: "f_panic".to_string(),
                params: vec![],
                autos: vec![Param {
                    name: "shadowed_var".to_string(),
                    is_array: false,
                }],
                body: vec![Stmt::Expr(Expr::BinaryOp(
                    BinOp::Div,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("0".to_string())),
                ))],
            },
        );
        let panic_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluator.evaluate(&Expr::Call("f_panic".to_string(), vec![]));
        }));
        assert!(panic_res.is_err());
        let restored_val = evaluator.evaluate(&Expr::Variable("shadowed_var".to_string()));
        assert_eq!(restored_val.coeff, BigInt::from(99));
    }

    #[test]
    fn test_evaluator_operator_and_assignment_mutants() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // Test all relational operations cleanly
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Eq,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("1".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Eq,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Ne,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Ne,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("1".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Lt,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Lt,
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Le,
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Le,
                    Box::new(Expr::Number("3".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Gt,
                    Box::new(Expr::Number("3".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Gt,
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Ge,
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Ge,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        // Test compound assignments +=, -=, *=, /=, %=, ^=
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("10".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Add),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("5".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(15)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Sub),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("3".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(12)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Mul),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("2".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(24)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Div),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("4".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(6)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Mod),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("4".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(2)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Pow),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("3".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(8)
        );

        // Test pre/post increment and decrement
        let pre_inc = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(pre_inc.coeff, BigInt::from(9));

        let post_inc = evaluator.evaluate(&Expr::Update(
            true,
            false,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(post_inc.coeff, BigInt::from(9));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(10)
        );

        let pre_dec = evaluator.evaluate(&Expr::Update(
            false,
            true,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(pre_dec.coeff, BigInt::from(9));

        let post_dec = evaluator.evaluate(&Expr::Update(
            false,
            false,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(post_dec.coeff, BigInt::from(9));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(8)
        );

        // Test Stmt::For and Stmt::If control flow branches
        evaluator.execute(&Stmt::For(
            Expr::AssignOp(
                AssignOp::Assign,
                Box::new(Expr::Variable("var_i".to_string())),
                Box::new(Expr::Number("0".to_string())),
            ),
            Expr::RelationalOp(
                RelOp::Lt,
                Box::new(Expr::Variable("var_i".to_string())),
                Box::new(Expr::Number("3".to_string())),
            ),
            Expr::Update(true, true, Box::new(Expr::Variable("var_i".to_string()))),
            Box::new(Stmt::Block(vec![])),
        ));
        assert_eq!(
            evaluator
                .evaluate(&Expr::Variable("var_i".to_string()))
                .coeff,
            BigInt::from(3)
        );

        // Test Stmt::StringLiteral
        evaluator.execute(&Stmt::StringLiteral("out: hello".to_string()));
        let out_str = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert!(out_str.contains("out: hello"));
    }

    #[test]
    fn test_fractional_indices_and_register_truncation() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Assign to array using fractional index a[3.8] = 99
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::ArrayAccess(
                "arr".to_string(),
                Box::new(Expr::Number("3.8".to_string())),
            )),
            Box::new(Expr::Number("99".to_string())),
        )));

        // Read from array using fractional index a[3.1]
        let val_arr = evaluator.evaluate(&Expr::ArrayAccess(
            "arr".to_string(),
            Box::new(Expr::Number("3.1".to_string())),
        ));
        assert_eq!(val_arr.coeff, BigInt::from(99));

        // 2. Assign fractional values to scale, obase, ibase registers
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("5.9".to_string())),
        )));
        assert_eq!(evaluator.scale, 5);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("10.4".to_string())),
        )));
        assert_eq!(evaluator.obase, 10);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("16.7".to_string())),
        )));
        assert_eq!(evaluator.ibase, 16);
    }

    #[test]
    fn test_control_flow_truth_tables() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // Test if conditions for truth values of relational operators
        for (lhs, rhs, op, expected) in [
            ("5", "5", "==", true),
            ("5", "3", "==", false),
            ("5", "3", "!=", true),
            ("5", "5", "!=", false),
            ("3", "5", "<", true),
            ("5", "5", "<", false),
            ("3", "5", "<=", true),
            ("5", "5", "<=", true),
            ("6", "5", "<=", false),
            ("5", "3", ">", true),
            ("5", "5", ">", false),
            ("5", "3", ">=", true),
            ("5", "5", ">=", true),
            ("3", "5", ">=", false),
        ] {
            evaluator.variables.clear();
            evaluator.execute(&Stmt::If(
                Expr::RelationalOp(
                    RelOp::from_symbol(op),
                    Box::new(Expr::Number(lhs.to_string())),
                    Box::new(Expr::Number(rhs.to_string())),
                ),
                Box::new(Stmt::Expr(Expr::AssignOp(
                    AssignOp::Assign,
                    Box::new(Expr::Variable("hit".to_string())),
                    Box::new(Expr::Number("1".to_string())),
                ))),
            ));
            let hit = evaluator.evaluate(&Expr::Variable("hit".to_string())).coeff;
            assert_eq!(hit == BigInt::from(1), expected);
        }
    }

    #[test]
    fn test_evaluator_compound_assignment_scale_and_scoping() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Compound assignment scale propagation
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("4".to_string())),
        )));

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("5.5".to_string())),
        )));

        // x += 1.25 -> 6.75 (max scale = 2)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Add),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("1.25".to_string())),
        )));
        let x_add = evaluator.evaluate(&Expr::Variable("x".to_string()));
        assert_eq!(x_add.coeff, BigInt::from(675));
        assert_eq!(x_add.scale, 2);

        // x /= 2 -> 3.3750
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Div),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("2".to_string())),
        )));
        let x_div = evaluator.evaluate(&Expr::Variable("x".to_string()));
        assert_eq!(x_div.coeff, BigInt::from(33750));
        assert_eq!(x_div.scale, 4);

        // 2. Dynamic Scope & Auto Variable Stack
        let f_def = FunctionDef {
            name: "test_fn".to_string(),
            params: vec![Param {
                name: "param1".to_string(),
                is_array: false,
            }],
            autos: vec![Param {
                name: "auto1".to_string(),
                is_array: false,
            }],
            body: vec![
                Stmt::Expr(Expr::AssignOp(
                    AssignOp::Assign,
                    Box::new(Expr::Variable("auto1".to_string())),
                    Box::new(Expr::Number("99".to_string())),
                )),
                Stmt::Return(Some(Expr::Variable("auto1".to_string()))),
            ],
        };
        evaluator.functions.insert("test_fn".to_string(), f_def);

        let call_res = evaluator.evaluate(&Expr::Call(
            "test_fn".to_string(),
            vec![ExprOrArray::Expr(Expr::Number("10".to_string()))],
        ));
        assert_eq!(call_res.coeff, BigInt::from(99));

        // After call, auto1 is restored to 0
        let auto1_after = evaluator.evaluate(&Expr::Variable("auto1".to_string()));
        assert_eq!(auto1_after.coeff, BigInt::from(0));
    }

    #[test]
    fn test_unary_op_scale_preservation_and_assign_registers() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Unary minus scale preservation
        let num_expr = Box::new(Expr::Number("5.25".to_string()));

        let uminus = evaluator.evaluate(&Expr::Negate(num_expr));
        assert_eq!(uminus.coeff, BigInt::from(-525));
        assert_eq!(uminus.scale, 2);

        // 2. Register assignments to ibase and obase
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("10".to_string())),
        )));
        assert_eq!(evaluator.obase, 10);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("16".to_string())),
        )));
        assert_eq!(evaluator.ibase, 16);
        assert!(stderr_buf.lock().unwrap().is_empty());

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("2".to_string())),
        )));
        assert_eq!(evaluator.ibase, 2);
        assert!(stderr_buf.lock().unwrap().is_empty());

        // UpdateOp on ibase and obase registers
        evaluator.ibase = 10;
        let ibase_inc = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
        ));
        assert_eq!(ibase_inc.coeff, BigInt::from(11));
        assert_eq!(evaluator.ibase, 11);

        evaluator.obase = 10;
        let obase_inc = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::RegisterAccess(Register::Obase)),
        ));
        assert_eq!(obase_inc.coeff, BigInt::from(11));
        assert_eq!(evaluator.obase, 11);

        // 3. WrappedStdout flush & 70-char wrapping
        stdout_buf.lock().unwrap().clear();
        let mut wrapped = WrappedStdout::new(Box::new(TestWriter {
            buf: stdout_buf.clone(),
        }));
        assert!(wrapped.write_str(&"1".repeat(70)).is_ok());
        assert!(wrapped.write_str("\n").is_ok());
        assert!(wrapped.flush().is_ok());
        let wrapped_out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(wrapped_out, format!("{}\\\n11\n", "1".repeat(68)));
    }

    #[test]
    fn test_relational_op_scale_normalization_and_register_scopes() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Relational Ops with scale_left < scale_right (diff < 0)
        let expr_eq_lt = Expr::RelationalOp(
            RelOp::Eq,
            Box::new(Expr::Number("1.5".to_string())), // scale 1
            Box::new(Expr::Number("1.500".to_string())), // scale 3
        );
        assert_eq!(evaluator.evaluate(&expr_eq_lt).coeff, BigInt::from(1));

        let expr_lt = Expr::RelationalOp(
            RelOp::Lt,
            Box::new(Expr::Number("1.5".to_string())), // scale 1
            Box::new(Expr::Number("1.501".to_string())), // scale 3
        );
        assert_eq!(evaluator.evaluate(&expr_lt).coeff, BigInt::from(1));

        let expr_gt = Expr::RelationalOp(
            RelOp::Gt,
            Box::new(Expr::Number("1.5".to_string())), // scale 1
            Box::new(Expr::Number("1.499".to_string())), // scale 3
        );
        assert_eq!(evaluator.evaluate(&expr_gt).coeff, BigInt::from(1));

        // 2. Relational Ops with scale_left > scale_right (diff > 0)
        let expr_eq_gt = Expr::RelationalOp(
            RelOp::Eq,
            Box::new(Expr::Number("1.500".to_string())), // scale 3
            Box::new(Expr::Number("1.5".to_string())),   // scale 1
        );
        assert_eq!(evaluator.evaluate(&expr_eq_gt).coeff, BigInt::from(1));

        // 3. Register access for scale
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("4".to_string())),
        )));
        assert_eq!(evaluator.scale, 4);

        let scale_res = evaluator.evaluate(&Expr::RegisterAccess(Register::Scale));
        assert_eq!(scale_res.coeff, BigInt::from(4));
    }

    #[test]
    fn test_hex_base_assignment_obase_clamping_and_fractional_index() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Single character hex base assignment (ibase = A -> 10, ibase = F -> 15)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("A".to_string())),
        )));
        assert_eq!(evaluator.ibase, 10);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("F".to_string())),
        )));
        assert_eq!(evaluator.ibase, 15);

        // Reset ibase back to 10
        evaluator.ibase = 10;

        // 2. obase min clamping (obase < 2 -> 2)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("0".to_string())),
        )));
        assert_eq!(evaluator.obase, 2);

        // 3. Fractional array index truncation (a[2.7] = 42 -> a[2] == 42)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::ArrayAccess(
                "a".to_string(),
                Box::new(Expr::Number("2.7".to_string())),
            )),
            Box::new(Expr::Number("42".to_string())),
        )));

        let arr_val = evaluator.evaluate(&Expr::ArrayAccess(
            "a".to_string(),
            Box::new(Expr::Number("2".to_string())),
        ));
        assert_eq!(arr_val.coeff, BigInt::from(42));

        // Fractional array index truncation in UpdateOp (++b[2.7] -> b[2] == 1)
        evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::ArrayAccess(
                "b".to_string(),
                Box::new(Expr::Number("2.7".to_string())),
            )),
        ));
        let arr_val_b = evaluator.evaluate(&Expr::ArrayAccess(
            "b".to_string(),
            Box::new(Expr::Number("2".to_string())),
        ));
        assert_eq!(arr_val_b.coeff, BigInt::from(1));

        // 4. Block execution break on quit_flag
        evaluator.execute(&Stmt::Block(vec![
            Stmt::Quit,
            Stmt::Expr(Expr::AssignOp(
                AssignOp::Assign,
                Box::new(Expr::Variable("stopped".to_string())),
                Box::new(Expr::Number("1".to_string())),
            )),
        ]));
        let stopped_var = evaluator.evaluate(&Expr::Variable("stopped".to_string()));
        assert_eq!(stopped_var.coeff, BigInt::from(0));
    }

    #[test]
    fn test_return_inside_while_and_for_loops() {
        let mut evaluator = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let mut parser_while = Parser::new(Lexer::new(
            "define f_while() { i = 0; while (i < 10) { i = i + 1; return (i); }; return (999); }; f_while()",
        ));
        for stmt in parser_while.parse_program() {
            evaluator.execute(&stmt);
        }
        let res_while = evaluator.evaluate(&Expr::Variable("i".to_string()));
        assert_eq!(res_while.coeff, BigInt::from(1));

        let mut evaluator_for =
            Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let mut parser_for = Parser::new(Lexer::new(
            "define f_for() { for (i = 0; i < 10; i = i + 1) { return (i + 1); }; return (999); }; f_for()",
        ));
        for stmt in parser_for.parse_program() {
            evaluator_for.execute(&stmt);
        }
        let res_for = evaluator_for.evaluate(&Expr::Variable("i".to_string()));
        assert_eq!(res_for.coeff, BigInt::from(0));
    }

    struct FailingFlushWriter;
    impl FmtWrite for FailingFlushWriter {
        fn write_str(&mut self, _s: &str) -> core::fmt::Result {
            Ok(())
        }
    }
    impl BcWriter for FailingFlushWriter {
        fn flush(&mut self) -> core::fmt::Result {
            Err(core::fmt::Error)
        }
    }

    #[test]
    fn test_wrapped_stdout_flush_error_propagation() {
        let mut stdout = WrappedStdout::new(Box::new(FailingFlushWriter));
        assert!(stdout.flush().is_err());
    }

    #[test]
    fn test_function_early_return_short_circuits_body_loop() {
        let mut evaluator = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let mut parser = Parser::new(Lexer::new(
            "define f() { return (10); x = 99; return (20); }; f()",
        ));
        for stmt in parser.parse_program() {
            evaluator.execute(&stmt);
        }
        let res = evaluator.evaluate(&Expr::Call("f".to_string(), vec![]));
        assert_eq!(res.coeff, BigInt::from(10));
        let x_var = evaluator.evaluate(&Expr::Variable("x".to_string()));
        assert_eq!(x_var.coeff, BigInt::from(0));
    }

    #[test]
    fn test_execute_entry_and_block_guard_when_flags_set() {
        let mut evaluator = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        evaluator.break_flag = true;
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("mut_var".to_string())),
            Box::new(Expr::Number("99".to_string())),
        )));
        let val1 = evaluator.evaluate(&Expr::Variable("mut_var".to_string()));
        assert_eq!(val1.coeff, BigInt::from(0));

        evaluator.break_flag = false;
        evaluator.return_flag = true;
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("mut_var2".to_string())),
            Box::new(Expr::Number("99".to_string())),
        )));
        let val2 = evaluator.evaluate(&Expr::Variable("mut_var2".to_string()));
        assert_eq!(val2.coeff, BigInt::from(0));

        // Block loop short-circuit when statement inside block sets return_flag or break_flag (kills line 530 mutants)
        let mut evaluator2 =
            Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let stmt_ret = Stmt::Return(Some(Expr::Number("10".to_string())));
        let stmt_assign1 = Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("block_var1".to_string())),
            Box::new(Expr::Number("99".to_string())),
        ));
        let block_ret = Stmt::Block(vec![stmt_ret, stmt_assign1]);
        evaluator2.execute(&block_ret);
        let val3 = evaluator2.evaluate(&Expr::Variable("block_var1".to_string()));
        assert_eq!(val3.coeff, BigInt::from(0));

        let mut evaluator3 =
            Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let stmt_break = Stmt::Break;
        let stmt_assign2 = Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("block_var2".to_string())),
            Box::new(Expr::Number("99".to_string())),
        ));
        let block_break = Stmt::Block(vec![stmt_break, stmt_assign2]);
        evaluator3.execute(&block_break);
        let val4 = evaluator3.evaluate(&Expr::Variable("block_var2".to_string()));
        assert_eq!(val4.coeff, BigInt::from(0));
    }

    #[test]
    fn test_names_first_seen_as_parameters_or_autos_stay_usable() {
        let out = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let mut ev = Evaluator::new(
            false,
            Box::new(TestWriter { buf: out.clone() }),
            Box::new(String::new()),
        );
        let src = "define f(p, q[]) {\nauto r, s[]\nr = p; s[0] = q[0]\nreturn (r + s[0])\n}\n\
                   t[0] = 2; f(1, t[])\n\
                   p = 5; q[0] = 6; r++; s[1] = 7; p; q[0]; r; s[1]\n";
        let summary = ev.run_source(src, "test");
        assert_eq!(summary.errors, 0);
        let out = String::from_utf8(out.lock().unwrap().clone()).unwrap();
        assert_eq!(out, "3\n0\n5\n6\n1\n7\n");
    }

    #[test]
    fn test_fallible_evaluator_and_scope_restoration() {
        let mut ev = Evaluator::new(true, Box::new(String::new()), Box::new(String::new()));

        let mut p_setup = Parser::try_new(Lexer::new(
            "x = 42; a[0] = 7\ndefine bad(x, a[]) {\n  auto y, b[]\n  x = 99\n  y = 1 / 0\n  return (y)\n}\n",
        ))
        .unwrap();
        for stmt in p_setup.try_parse_program().unwrap() {
            assert!(ev.try_execute(&stmt).is_ok());
        }

        // Calling bad(10, a[]) must fail with "Divide by zero" inside bad() AND leave_call must restore x = 42
        let mut p_call = Parser::try_new(Lexer::new("bad(10, a[])\n")).unwrap();
        let call_stmts = p_call.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&call_stmts[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::DivideByZero,
                func: Some("bad".to_string())
            })
        );
        let x_after = ev.try_evaluate(&Expr::Variable("x".to_string())).unwrap();
        assert_eq!(x_after.coeff, BigInt::from(42));

        // Argument errors and undefined function
        let mut p_mismatch = Parser::try_new(Lexer::new("bad(10)\n")).unwrap();
        let stmts_mismatch = p_mismatch.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_mismatch[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::ParameterMismatch,
                func: None
            })
        );

        let mut p_arr_err = Parser::try_new(Lexer::new("bad(10, 20)\n")).unwrap();
        let stmts_arr_err = p_arr_err.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_arr_err[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::ParameterTypeMismatch("a".to_string()),
                func: None
            })
        );

        let mut p_scalar_err = Parser::try_new(Lexer::new("bad(a[], a[])\n")).unwrap();
        let stmts_scalar_err = p_scalar_err.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_scalar_err[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::ParameterTypeMismatch("x".to_string()),
                func: None
            })
        );

        let mut p_undef = Parser::try_new(Lexer::new("nonexistent(1)\n")).unwrap();
        let stmts_undef = p_undef.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_undef[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::UndefinedFunction("nonexistent".to_string()),
                func: None
            })
        );

        let mut p_sqrt = Parser::try_new(Lexer::new("sqrt(-1)\n")).unwrap();
        let stmts_sqrt = p_sqrt.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_sqrt[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::NegativeSqrt,
                func: None
            })
        );

        // Verify binary operators (-, %, ^) and math library functions (s, c, a, l, e, j) via try_evaluate
        ev.scale = 4;
        let eval_expr = |ev: &mut Evaluator, src: &str| -> BCNum {
            let mut p = Parser::try_new(Lexer::new(src)).unwrap();
            let stmts = p.try_parse_program().unwrap();
            let inner = match &stmts[0] {
                Stmt::Block(b) => &b[0],
                other => other,
            };
            if let Stmt::Expr(e) = inner {
                ev.try_evaluate(e).unwrap()
            } else {
                panic!("expected Stmt::Expr");
            }
        };
        assert_eq!(eval_expr(&mut ev, "10 - 3\n").coeff, BigInt::from(7));
        assert_eq!(eval_expr(&mut ev, "10 % 3\n").coeff, BigInt::from(1));
        assert_eq!(eval_expr(&mut ev, "2 ^ 3\n").coeff, BigInt::from(8));
        assert!(eval_expr(&mut ev, "s(1)\n").coeff > BigInt::from(0));
        assert_eq!(eval_expr(&mut ev, "c(0)\n").coeff, BigInt::from(10000));
        assert!(eval_expr(&mut ev, "a(1)\n").coeff > BigInt::from(0));
        assert!(eval_expr(&mut ev, "l(2)\n").coeff > BigInt::from(0));
        assert_eq!(eval_expr(&mut ev, "e(0)\n").coeff, BigInt::from(10000));
        assert_eq!(eval_expr(&mut ev, "j(0, 0)\n").coeff, BigInt::from(10000));
    }
}
