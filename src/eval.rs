//! Tree-walking AST evaluator and dynamic scope manager for the bc clone.
//!
//! Complies with POSIX bc specifications for registers, arrays, function definitions,
//! dynamic scope resolution, and WrappedStdout formatting.

use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::collections::HashMap;
use std::io::Write;

use crate::bc_math::BCNum;
use crate::parser::{Expr, ExprOrArray, FunctionDef, Param, Stmt};

/// Wrapper to write output characters with POSIX-style 70-character line wrapping.
pub struct WrappedStdout {
    writer: Box<dyn Write + Send>,
    col: usize,
}

impl WrappedStdout {
    /// Creates a new WrappedStdout writing to the given writer.
    pub fn new(writer: Box<dyn Write + Send>) -> Self {
        Self { writer, col: 0 }
    }

    /// Writes a string to the output stream, handling wrapping if columns exceed 68.
    pub fn write_str(&mut self, s: &str) -> std::io::Result<()> {
        for c in s.chars() {
            if c == '\n' {
                self.writer.write_all(b"\n")?;
                self.col = 0;
            } else {
                if self.col >= 68 {
                    self.writer.write_all(b"\\\n")?;
                    self.col = 0;
                }
                let mut buf = [0; 4];
                let bytes = c.encode_utf8(&mut buf);
                self.writer.write_all(bytes.as_bytes())?;
                self.col += 1;
            }
        }
        Ok(())
    }

    /// Flushes the underlying writer.
    pub fn flush(&mut self) -> std::io::Result<()> {
        self.writer.flush()
    }
}

/// Evaluator maintaining registers, scoped variables, functions, and state.
pub struct Evaluator {
    pub variables: HashMap<String, Vec<BCNum>>,
    pub arrays: HashMap<String, Vec<HashMap<BigInt, BCNum>>>,
    pub functions: HashMap<String, FunctionDef>,
    pub scale: usize,
    pub ibase: usize,
    pub obase: usize,
    pub math_enabled: bool,
    pub stdout_writer: WrappedStdout,
    pub stderr_writer: Box<dyn Write + Send>,

    pub break_flag: bool,
    pub return_flag: bool,
    pub return_value: BCNum,
    pub quit_flag: bool,
}

struct ScopeGuard<'a> {
    evaluator: &'a mut Evaluator,
    autos: &'a [Param],
    params: &'a [Param],
    prev_return_flag: bool,
    prev_return_value: BCNum,
}

impl<'a> Drop for ScopeGuard<'a> {
    fn drop(&mut self) {
        self.evaluator.return_flag = self.prev_return_flag;
        self.evaluator.return_value = self.prev_return_value.clone();

        for auto in self.autos.iter().rev() {
            if auto.is_array {
                if let Some(stack) = self.evaluator.arrays.get_mut(&auto.name) {
                    stack.pop();
                }
            } else if let Some(stack) = self.evaluator.variables.get_mut(&auto.name) {
                stack.pop();
            }
        }
        for param in self.params.iter().rev() {
            if param.is_array {
                if let Some(stack) = self.evaluator.arrays.get_mut(&param.name) {
                    stack.pop();
                }
            } else if let Some(stack) = self.evaluator.variables.get_mut(&param.name) {
                stack.pop();
            }
        }
    }
}

impl Evaluator {
    /// Creates a new Evaluator.
    pub fn new(
        math_enabled: bool,
        stdout_stream: Box<dyn Write + Send>,
        stderr_stream: Box<dyn Write + Send>,
    ) -> Self {
        Self {
            variables: HashMap::new(),
            arrays: HashMap::new(),
            functions: HashMap::new(),
            scale: 0,
            ibase: 10,
            obase: 10,
            math_enabled,
            stdout_writer: WrappedStdout::new(stdout_stream),
            stderr_writer: stderr_stream,
            break_flag: false,
            return_flag: false,
            return_value: BCNum::zero(),
            quit_flag: false,
        }
    }

    /// Evaluates an AST expression node and returns a BCNum.
    pub fn evaluate(&mut self, node: &Expr) -> BCNum {
        match node {
            Expr::Number(value) => BCNum::from_string(value, self.ibase),
            Expr::Variable(name) => {
                let stack = self
                    .variables
                    .entry(name.clone())
                    .or_insert_with(|| vec![BCNum::zero()]);
                stack.last().cloned().unwrap_or_else(BCNum::zero)
            }
            Expr::ArrayAccess(name, index_expr) => {
                let idx = self.evaluate(index_expr);
                let idx_val = if idx.scale > 0 {
                    let divisor = BigInt::from(10).pow(idx.scale as u32);
                    &idx.coeff / divisor
                } else {
                    idx.coeff.clone()
                };
                let stack = self
                    .arrays
                    .entry(name.clone())
                    .or_insert_with(|| vec![HashMap::new()]);
                stack
                    .last()
                    .unwrap()
                    .get(&idx_val)
                    .cloned()
                    .unwrap_or_else(BCNum::zero)
            }
            Expr::RegisterAccess(name) => {
                let val = match name.as_str() {
                    "scale" => self.scale,
                    "ibase" => self.ibase,
                    "obase" => self.obase,
                    _ => 0,
                };
                BCNum::new(BigInt::from(val), 0)
            }
            Expr::UnaryOp(op, expr) => {
                let val = self.evaluate(expr);
                if *op == '-' {
                    BCNum::new(-val.coeff, val.scale)
                } else {
                    val
                }
            }
            Expr::BinaryOp(op, left, right) => {
                let l = self.evaluate(left);
                let r = self.evaluate(right);
                match op.as_str() {
                    "+" => l.add(&r),
                    "-" => l.sub(&r),
                    "*" => l.mul(&r, self.scale),
                    "/" => l.div(&r, self.scale),
                    "%" => l.mod_op(&r, self.scale),
                    "^" => l.pow(&r, self.scale),
                    _ => BCNum::zero(),
                }
            }
            Expr::RelationalOp(op, left, right) => {
                let l = self.evaluate(left);
                let r = self.evaluate(right);
                let diff = l.scale as i64 - r.scale as i64;
                let (coeff_l, coeff_r) = if diff > 0 {
                    let factor = BigInt::from(10).pow(diff as u32);
                    (l.coeff.clone(), &r.coeff * factor)
                } else if diff < 0 {
                    let factor = BigInt::from(10).pow((-diff) as u32);
                    (&l.coeff * factor, r.coeff.clone())
                } else {
                    (l.coeff.clone(), r.coeff.clone())
                };

                let res = match op.as_str() {
                    "==" => coeff_l == coeff_r,
                    "<=" => coeff_l <= coeff_r,
                    ">=" => coeff_l >= coeff_r,
                    "!=" => coeff_l != coeff_r,
                    "<" => coeff_l < coeff_r,
                    ">" => coeff_l > coeff_r,
                    _ => false,
                };
                BCNum::new(BigInt::from(if res { 1 } else { 0 }), 0)
            }
            Expr::AssignOp(op, target, expr) => {
                let is_base_reg = if let Expr::RegisterAccess(reg_name) = &**target {
                    reg_name == "ibase" || reg_name == "obase"
                } else {
                    false
                };

                let val = if is_base_reg && op == "=" {
                    let mut is_single_char = false;
                    let mut char_val = 0usize;
                    if let Expr::Number(num_val) = &**expr {
                        let cleaned = num_val.replace("\\\n", "");
                        if cleaned.len() == 1 {
                            let c = cleaned.chars().next().unwrap();
                            is_single_char = true;
                            char_val = if c.is_ascii_digit() {
                                (c as usize) - ('0' as usize)
                            } else {
                                let cu = c.to_ascii_uppercase();
                                if ('A'..='F').contains(&cu) {
                                    (cu as usize) - ('A' as usize) + 10
                                } else {
                                    0
                                }
                            };
                        }
                    }
                    if is_single_char {
                        BCNum::new(BigInt::from(char_val), 0)
                    } else {
                        self.evaluate(expr)
                    }
                } else {
                    let mut val = self.evaluate(expr);
                    if op != "=" {
                        let old_val = self.evaluate(target);
                        let base_op = &op[..op.len() - 1];
                        val = match base_op {
                            "+" => old_val.add(&val),
                            "-" => old_val.sub(&val),
                            "*" => old_val.mul(&val, self.scale),
                            "/" => old_val.div(&val, self.scale),
                            "%" => old_val.mod_op(&val, self.scale),
                            "^" => old_val.pow(&val, self.scale),
                            _ => BCNum::zero(),
                        };
                    }
                    val
                };

                match &**target {
                    Expr::Variable(name) => {
                        let var_stack = self
                            .variables
                            .entry(name.clone())
                            .or_insert_with(|| vec![BCNum::zero()]);
                        *var_stack.last_mut().unwrap() = val.clone();
                    }
                    Expr::ArrayAccess(name, idx_expr) => {
                        let idx = self.evaluate(idx_expr);
                        let idx_val = if idx.scale > 0 {
                            let divisor = BigInt::from(10).pow(idx.scale as u32);
                            &idx.coeff / divisor
                        } else {
                            idx.coeff.clone()
                        };
                        let arr_stack = self
                            .arrays
                            .entry(name.clone())
                            .or_insert_with(|| vec![HashMap::new()]);
                        arr_stack.last_mut().unwrap().insert(idx_val, val.clone());
                    }
                    Expr::RegisterAccess(name) => {
                        let mut reg_val = if val.scale > 0 {
                            let divisor = BigInt::from(10).pow(val.scale as u32);
                            &val.coeff / divisor
                        } else {
                            val.coeff.clone()
                        };
                        let reg_val_usize = reg_val.to_usize().unwrap_or(0);
                        match name.as_str() {
                            "scale" => {
                                let v = reg_val.to_usize().unwrap_or(0);
                                self.scale = v;
                                reg_val = BigInt::from(v);
                            }
                            "ibase" => {
                                let mut v = reg_val_usize;
                                if v < 2 {
                                    let _ = writeln!(
                                        self.stderr_writer,
                                        "Runtime warning (func=(main), adr=3): ibase too small, set to 2"
                                    );
                                    v = 2;
                                } else if v > 16 {
                                    let _ = writeln!(
                                        self.stderr_writer,
                                        "Runtime warning (func=(main), adr=3): ibase too large, set to 16"
                                    );
                                    v = 16;
                                }
                                self.ibase = v;
                                reg_val = BigInt::from(v);
                            }
                            "obase" => {
                                let mut v = reg_val_usize;
                                if v < 2 {
                                    v = 2;
                                }
                                self.obase = v;
                                reg_val = BigInt::from(v);
                            }
                            _ => {
                                reg_val = BigInt::from(0);
                            }
                        }
                        return BCNum::new(reg_val, 0);
                    }
                    _ => {}
                }
                val
            }
            Expr::UpdateOp(op, is_prefix, target) => {
                let old_val = self.evaluate(target);
                let step = BCNum::new(BigInt::from(1), 0);
                let new_val = if op == "++" {
                    old_val.add(&step)
                } else {
                    old_val.sub(&step)
                };

                match &**target {
                    Expr::Variable(name) => {
                        let var_stack = self
                            .variables
                            .entry(name.clone())
                            .or_insert_with(|| vec![BCNum::zero()]);
                        *var_stack.last_mut().unwrap() = new_val.clone();
                    }
                    Expr::ArrayAccess(name, idx_expr) => {
                        let idx = self.evaluate(idx_expr);
                        let idx_val = if idx.scale > 0 {
                            let divisor = BigInt::from(10).pow(idx.scale as u32);
                            &idx.coeff / divisor
                        } else {
                            idx.coeff.clone()
                        };
                        let arr_stack = self
                            .arrays
                            .entry(name.clone())
                            .or_insert_with(|| vec![HashMap::new()]);
                        arr_stack
                            .last_mut()
                            .unwrap()
                            .insert(idx_val, new_val.clone());
                    }
                    Expr::RegisterAccess(name) => {
                        let mut reg_val = new_val.coeff.clone();
                        let reg_val_usize = reg_val.to_usize().unwrap_or(0);
                        match name.as_str() {
                            "scale" => {
                                let v = reg_val.to_usize().unwrap_or(0);
                                self.scale = v;
                                reg_val = BigInt::from(v);
                            }
                            "ibase" => {
                                let v = reg_val_usize.clamp(2, 16);
                                self.ibase = v;
                                reg_val = BigInt::from(v);
                            }
                            "obase" => {
                                let mut v = reg_val_usize;
                                if v < 2 {
                                    v = 2;
                                }
                                self.obase = v;
                                reg_val = BigInt::from(v);
                            }
                            _ => {
                                reg_val = BigInt::from(0);
                            }
                        }
                        let final_val = BCNum::new(reg_val, 0);
                        return if *is_prefix { final_val } else { old_val };
                    }
                    _ => {}
                }

                if *is_prefix { new_val } else { old_val }
            }
            Expr::Call(name, args) => {
                if self.functions.contains_key(name) {
                    let func = self.functions.get(name).unwrap().clone();
                    if args.len() != func.params.len() {
                        panic!("argument count mismatch");
                    }

                    let mut evaluated_args = Vec::new();
                    for (i, arg) in args.iter().enumerate() {
                        let param = &func.params[i];
                        if param.is_array {
                            if let ExprOrArray::ArrayArg(arg_name) = arg {
                                let arr_stack = self
                                    .arrays
                                    .entry(arg_name.clone())
                                    .or_insert_with(|| vec![HashMap::new()]);
                                let arr_copy = arr_stack.last().unwrap().clone();
                                evaluated_args.push((
                                    true,
                                    param.name.clone(),
                                    Some(arr_copy),
                                    None,
                                ));
                            } else {
                                panic!("expected array argument");
                            }
                        } else if let ExprOrArray::Expr(expr) = arg {
                            let val = self.evaluate(expr);
                            evaluated_args.push((false, param.name.clone(), None, Some(val)));
                        } else {
                            panic!("argument count mismatch");
                        }
                    }

                    for (is_arr, pname, arr_opt, val_opt) in evaluated_args {
                        if is_arr {
                            let stack = self.arrays.entry(pname).or_default();
                            stack.push(arr_opt.unwrap());
                        } else {
                            let stack = self.variables.entry(pname).or_default();
                            stack.push(val_opt.unwrap());
                        }
                    }

                    for auto in &func.autos {
                        if auto.is_array {
                            let stack = self.arrays.entry(auto.name.clone()).or_default();
                            stack.push(HashMap::new());
                        } else {
                            let stack = self.variables.entry(auto.name.clone()).or_default();
                            stack.push(BCNum::zero());
                        }
                    }

                    let prev_return_flag = self.return_flag;
                    let prev_return_value = self.return_value.clone();
                    self.return_flag = false;
                    self.return_value = BCNum::zero();

                    let guard = ScopeGuard {
                        evaluator: self,
                        autos: &func.autos,
                        params: &func.params,
                        prev_return_flag,
                        prev_return_value,
                    };

                    for stmt in &func.body {
                        guard.evaluator.execute(stmt);
                        if guard.evaluator.return_flag || guard.evaluator.quit_flag {
                            break;
                        }
                    }

                    let ret_val = guard.evaluator.return_value.clone();
                    drop(guard);

                    return ret_val;
                }

                if self.math_enabled {
                    use crate::bc_math::{bc_atan, bc_bessel, bc_cos, bc_exp, bc_ln, bc_sin};
                    match (name.as_str(), args.as_slice()) {
                        ("s", [ExprOrArray::Expr(expr)]) => {
                            return bc_sin(&self.evaluate(expr), self.scale);
                        }
                        ("c", [ExprOrArray::Expr(expr)]) => {
                            return bc_cos(&self.evaluate(expr), self.scale);
                        }
                        ("a", [ExprOrArray::Expr(expr)]) => {
                            return bc_atan(&self.evaluate(expr), self.scale);
                        }
                        ("l", [ExprOrArray::Expr(expr)]) => {
                            return bc_ln(&self.evaluate(expr), self.scale);
                        }
                        ("e", [ExprOrArray::Expr(expr)]) => {
                            return bc_exp(&self.evaluate(expr), self.scale);
                        }
                        ("j", [ExprOrArray::Expr(expr_n), ExprOrArray::Expr(expr_x)]) => {
                            return bc_bessel(
                                &self.evaluate(expr_n),
                                &self.evaluate(expr_x),
                                self.scale,
                            );
                        }
                        _ => {}
                    }
                }

                panic!("undefined function {}", name);
            }
            Expr::LengthCall(expr) => self.evaluate(expr).length(),
            Expr::SqrtCall(expr) => self.evaluate(expr).sqrt(self.scale),
            Expr::ScaleCall(expr) => self.evaluate(expr).scale_func(),
        }
    }

    /// Executes an AST statement node.
    pub fn execute(&mut self, node: &Stmt) {
        if self.break_flag || self.return_flag || self.quit_flag {
            return;
        }

        match node {
            Stmt::Block(stmts) => {
                for stmt in stmts {
                    self.execute(stmt);
                    if self.break_flag || self.return_flag || self.quit_flag {
                        break;
                    }
                }
            }
            Stmt::Expr(expr) => {
                if let Expr::AssignOp(..) = expr {
                    self.evaluate(expr);
                } else {
                    let val = self.evaluate(expr);
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
                    self.return_value = self.evaluate(expr);
                } else {
                    self.return_value = BCNum::zero();
                }
                self.return_flag = true;
            }
            Stmt::If(cond, body) => {
                let c = self.evaluate(cond);
                if !c.is_zero() {
                    self.execute(body);
                }
            }
            Stmt::While(cond, body) => loop {
                let c = self.evaluate(cond);
                if c.is_zero() || self.quit_flag {
                    break;
                }
                self.execute(body);
                if self.break_flag {
                    self.break_flag = false;
                    break;
                }
                if self.return_flag || self.quit_flag {
                    break;
                }
            },
            Stmt::For(init, cond, post, body) => {
                self.evaluate(init);
                loop {
                    let c = self.evaluate(cond);
                    if c.is_zero() || self.quit_flag {
                        break;
                    }
                    self.execute(body);
                    if self.break_flag {
                        self.break_flag = false;
                        break;
                    }
                    if self.return_flag || self.quit_flag {
                        break;
                    }
                    self.evaluate(post);
                }
            }
            Stmt::FunctionDef(func) => {
                self.functions.insert(func.name.clone(), func.clone());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Lexer;
    use crate::parser::Parser;

    #[derive(Clone)]
    struct TestWriter {
        buf: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
    }

    impl Write for TestWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.buf.lock().unwrap().write(buf)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            self.buf.lock().unwrap().flush()
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
        use crate::parser::{Expr, ExprOrArray, FunctionDef, Param, Stmt};

        let mut evaluator = Evaluator::new(true, Box::new(Vec::new()), Box::new(Vec::new()));

        // 1. Array access with fractional index (lines 108-109)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
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

        // 2. RegisterAccess fallback
        let node_reg = Expr::RegisterAccess("dummy".to_string());
        let res_reg = evaluator.evaluate(&node_reg);
        assert_eq!(res_reg.coeff, BigInt::from(0));

        // 3. Unreachable binary op operator
        let node_bin = Expr::BinaryOp(
            "dummy".to_string(),
            Box::new(Expr::Number("1".to_string())),
            Box::new(Expr::Number("1".to_string())),
        );
        let res_bin = evaluator.evaluate(&node_bin);
        assert_eq!(res_bin.coeff, BigInt::from(0));

        // 4. Unreachable relational op operator
        let node_rel = Expr::RelationalOp(
            "dummy".to_string(),
            Box::new(Expr::Number("1".to_string())),
            Box::new(Expr::Number("1".to_string())),
        );
        let res_rel = evaluator.evaluate(&node_rel);
        assert_eq!(res_rel.coeff, BigInt::from(0));

        // 5. Unary op not minus (line 138)
        let node_unary = Expr::UnaryOp('+', Box::new(Expr::Number("5".to_string())));
        let res_unary = evaluator.evaluate(&node_unary);
        assert_eq!(res_unary.coeff, BigInt::from(5));

        // 6. Assign single non-hex char to ibase (line 201)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("ibase".to_string())),
            Box::new(Expr::Number("Z".to_string())),
        )));

        // 7. Unreachable AssignOp fallback (line 223)
        let node_assign = Expr::AssignOp(
            "dummy=".to_string(),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("1".to_string())),
        );
        let res_assign_val = evaluator.evaluate(&node_assign);
        assert_eq!(res_assign_val.coeff, BigInt::from(0));

        // 8. Assign fractional value to register (lines 257-258)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("scale".to_string())),
            Box::new(Expr::Number("2.5".to_string())),
        )));

        // 9. obase < 2 update (line 290)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("obase".to_string())),
            Box::new(Expr::Number("1".to_string())),
        )));

        // 10. RegisterAccess / AssignOp unreachable fallbacks
        let node_reg_assign = Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("dummy".to_string())),
            Box::new(Expr::Number("1".to_string())),
        );
        let res_assign_val = evaluator.evaluate(&node_reg_assign);
        assert_eq!(res_assign_val.coeff, BigInt::from(0));

        let node_reg_update = Expr::UpdateOp(
            "++".to_string(),
            true,
            Box::new(Expr::RegisterAccess("dummy".to_string())),
        );
        let res_update_val = evaluator.evaluate(&node_reg_update);
        assert_eq!(res_update_val.coeff, BigInt::from(0));

        let node_update_unreach = Expr::UpdateOp(
            "++".to_string(),
            true,
            Box::new(Expr::Number("1".to_string())),
        );
        let res_unreach_val = evaluator.evaluate(&node_update_unreach);
        assert_eq!(res_unreach_val.coeff, BigInt::from(2));

        // 10b. Additional tests for ibase single-character assignment edge cases
        // A) multi-character number (cleaned.len() != 1)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("ibase".to_string())),
            Box::new(Expr::Number("10".to_string())),
        )));
        // B) non-number (expr is not Expr::Number)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("ibase".to_string())),
            Box::new(Expr::Variable("x".to_string())),
        )));
        // C) single character non-hex digit (c is not ascii digit or A-F)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("ibase".to_string())),
            Box::new(Expr::Number(".".to_string())),
        )));

        // Unreachable BinaryOp / RelationalOp fallback (line 151, 175)
        let node_bin_unreach = Expr::BinaryOp(
            "dummy".to_string(),
            Box::new(Expr::Number("1".to_string())),
            Box::new(Expr::Number("2".to_string())),
        );
        let res_bin_val = evaluator.evaluate(&node_bin_unreach);
        assert_eq!(res_bin_val.coeff, BigInt::from(0));

        let node_rel_unreach = Expr::RelationalOp(
            "dummy".to_string(),
            Box::new(Expr::Number("1".to_string())),
            Box::new(Expr::Number("2".to_string())),
        );
        let res_rel_val = evaluator.evaluate(&node_rel_unreach);
        assert_eq!(res_rel_val.coeff, BigInt::from(0));

        // AssignOp non-lvalue target fallback (line 301)
        let node_assign_unreach = Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::Number("1".to_string())),
            Box::new(Expr::Number("2".to_string())),
        );
        let res_assign_unreach = evaluator.evaluate(&node_assign_unreach);
        assert_eq!(res_assign_unreach.coeff, BigInt::from(2));

        // 11. Increment/decrement array at a fractional index (lines 325-326)
        evaluator.execute(&Stmt::Expr(Expr::UpdateOp(
            "++".to_string(),
            true,
            Box::new(Expr::ArrayAccess(
                "a".to_string(),
                Box::new(Expr::Number("1.5".to_string())),
            )),
        )));

        // 12. Increment/decrement a register with a fractional value (lines 340-341)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("scale".to_string())),
            Box::new(Expr::Number("2.5".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::UpdateOp(
            "++".to_string(),
            true,
            Box::new(Expr::RegisterAccess("scale".to_string())),
        )));

        // 13. Update obase with cap (line 360)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("obase".to_string())),
            Box::new(Expr::Number("2".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::UpdateOp(
            "--".to_string(),
            true,
            Box::new(Expr::RegisterAccess("obase".to_string())),
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
        let _ = evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::Variable("uninit_var_assign".to_string())),
            Box::new(Expr::Number("10".to_string())),
        )));
        let _ = evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::ArrayAccess(
                "uninit_arr_assign".to_string(),
                Box::new(Expr::Number("0".to_string())),
            )),
            Box::new(Expr::Number("10".to_string())),
        )));
        let _ = evaluator.evaluate(&Expr::UpdateOp(
            "++".to_string(),
            true,
            Box::new(Expr::Variable("uninit_var_inc".to_string())),
        ));
        let _ = evaluator.evaluate(&Expr::UpdateOp(
            "++".to_string(),
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

        // 19. ScopeGuard unwinding test
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
                    "/".to_string(),
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
                    "==".to_string(),
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("1".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    "==".to_string(),
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    "!=".to_string(),
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    "!=".to_string(),
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("1".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    "<".to_string(),
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    "<".to_string(),
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    "<=".to_string(),
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    "<=".to_string(),
                    Box::new(Expr::Number("3".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    ">".to_string(),
                    Box::new(Expr::Number("3".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    ">".to_string(),
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    ">=".to_string(),
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    ">=".to_string(),
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        // Test compound assignments +=, -=, *=, /=, %=, ^=
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("10".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "+=".to_string(),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("5".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(15)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "-=".to_string(),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("3".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(12)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "*=".to_string(),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("2".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(24)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "/=".to_string(),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("4".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(6)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "%=".to_string(),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("4".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(2)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "^=".to_string(),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("3".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(8)
        );

        // Test pre/post increment and decrement
        let pre_inc = evaluator.evaluate(&Expr::UpdateOp(
            "++".to_string(),
            true,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(pre_inc.coeff, BigInt::from(9));

        let post_inc = evaluator.evaluate(&Expr::UpdateOp(
            "++".to_string(),
            false,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(post_inc.coeff, BigInt::from(9));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(10)
        );

        let pre_dec = evaluator.evaluate(&Expr::UpdateOp(
            "--".to_string(),
            true,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(pre_dec.coeff, BigInt::from(9));

        let post_dec = evaluator.evaluate(&Expr::UpdateOp(
            "--".to_string(),
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
                "=".to_string(),
                Box::new(Expr::Variable("var_i".to_string())),
                Box::new(Expr::Number("0".to_string())),
            ),
            Expr::RelationalOp(
                "<".to_string(),
                Box::new(Expr::Variable("var_i".to_string())),
                Box::new(Expr::Number("3".to_string())),
            ),
            Expr::UpdateOp(
                "++".to_string(),
                true,
                Box::new(Expr::Variable("var_i".to_string())),
            ),
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
            "=".to_string(),
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
            "=".to_string(),
            Box::new(Expr::RegisterAccess("scale".to_string())),
            Box::new(Expr::Number("5.9".to_string())),
        )));
        assert_eq!(evaluator.scale, 5);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("obase".to_string())),
            Box::new(Expr::Number("10.4".to_string())),
        )));
        assert_eq!(evaluator.obase, 10);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            "=".to_string(),
            Box::new(Expr::RegisterAccess("ibase".to_string())),
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
                    op.to_string(),
                    Box::new(Expr::Number(lhs.to_string())),
                    Box::new(Expr::Number(rhs.to_string())),
                ),
                Box::new(Stmt::Expr(Expr::AssignOp(
                    "=".to_string(),
                    Box::new(Expr::Variable("hit".to_string())),
                    Box::new(Expr::Number("1".to_string())),
                ))),
            ));
            let hit = evaluator.evaluate(&Expr::Variable("hit".to_string())).coeff;
            assert_eq!(hit == BigInt::from(1), expected);
        }
    }
}
