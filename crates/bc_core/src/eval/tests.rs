// SPDX-License-Identifier: MIT

use super::*;
use crate::parser::Lexer;
use crate::parser::Param;
use crate::parser::Parser;
use alloc::format;
use alloc::string::ToString;
use num_bigint::BigInt;

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
    let res_f_arr_expr_mismatch = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
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
fn test_default_write_bytes_replaces_invalid_utf8() {
    // A writer that stores text receives invalid UTF-8 as U+FFFD; valid text is unchanged.
    let mut text = String::new();
    assert!(BcWriter::write_bytes(&mut text, "\u{e9}".as_bytes()).is_ok());
    assert!(BcWriter::write_bytes(&mut text, b"a\xffb").is_ok());
    assert_eq!(text, "\u{e9}a\u{fffd}b");
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

    let mut evaluator_for = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
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
    let mut evaluator2 = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
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

    let mut evaluator3 = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
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

#[test]
fn test_front_end_control_methods() {
    let mut evaluator = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
    evaluator.request_quit();
    assert!(evaluator.quit_flag);
    evaluator.clear_quit();
    assert!(!evaluator.quit_flag);

    evaluator.break_flag = true;
    evaluator.return_flag = true;
    evaluator.reset_control_flags();
    assert!(!evaluator.break_flag);
    assert!(!evaluator.return_flag);
}
