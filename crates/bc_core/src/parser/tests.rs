// SPDX-License-Identifier: MIT

use super::*;
use crate::error::BcError;
use crate::parser::test_tree::{Expr, ExprOrArray, Stmt};
use alloc::boxed::Box;
use alloc::format;
use alloc::string::ToString;
use alloc::vec;

#[test]
fn test_lexer_basic() {
    let mut lexer = Lexer::new(b"a = 10 + 20; /* comment */ a");
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
        assert_eq!(tok.value, expected_val.as_bytes());
    }
}

#[test]
fn test_lexer_backslash_newline() {
    let mut lexer = Lexer::new(b"1.2\\\n34 + \\\n  5.0");
    let tok1 = lexer.get_next_token();
    assert_eq!(tok1.token_type, TokenType::Number);
    assert_eq!(tok1.value, b"1.234");

    let tok2 = lexer.get_next_token();
    assert_eq!(tok2.token_type, TokenType::Plus);

    let tok3 = lexer.get_next_token();
    assert_eq!(tok3.token_type, TokenType::Number);
    assert_eq!(tok3.value, b"5.0");
}

#[test]
fn test_lexer_crlf_and_carriage_return() {
    let mut lexer = Lexer::new(b"a = 10\r\n + \r20");
    let tok1 = lexer.get_next_token();
    assert_eq!(tok1.token_type, TokenType::Letter);
    assert_eq!(tok1.value, b"a");

    let tok2 = lexer.get_next_token();
    assert_eq!(tok2.token_type, TokenType::AssignOp);

    let tok3 = lexer.get_next_token();
    assert_eq!(tok3.token_type, TokenType::Number);
    assert_eq!(tok3.value, b"10");

    let tok4 = lexer.get_next_token();
    assert_eq!(tok4.token_type, TokenType::Newline);

    let tok5 = lexer.get_next_token();
    assert_eq!(tok5.token_type, TokenType::Plus);

    let tok6 = lexer.get_next_token();
    assert_eq!(tok6.token_type, TokenType::Number);
    assert_eq!(tok6.value, b"20");

    let mut lexer2 = Lexer::new(b"1.2\\\r\n34");
    let tok_num = lexer2.get_next_token();
    assert_eq!(tok_num.token_type, TokenType::Number);
    assert_eq!(tok_num.value, b"1.234");

    // A number ends before a lone backslash and before an operator followed by CRLF.
    for (input, next_ok) in [(&b"12\\ 3"[..], false), (&b"12+\r\n"[..], true)] {
        let mut lexer = Lexer::new(input);
        let tok = lexer.get_next_token();
        assert_eq!(tok.token_type, TokenType::Number);
        assert_eq!(tok.value, b"12");
        let next = lexer.try_get_next_token();
        assert_eq!(next.is_ok(), next_ok);
        if let Ok(tok) = next {
            assert_eq!(tok.token_type, TokenType::Plus);
        }
    }

    let mut lexer3 = Lexer::new(b"\"hello \\\r\nworld\"");
    let tok_str = lexer3.get_next_token();
    assert_eq!(tok_str.token_type, TokenType::String);
    assert_eq!(tok_str.value, b"hello \\\r\nworld");
}

#[test]
fn test_lexer_string_backslash_newline() {
    let mut lexer = Lexer::new(b"\"hello \\\nworld\"");
    let tok = lexer.get_next_token();
    assert_eq!(tok.token_type, TokenType::String);
    assert_eq!(tok.value, b"hello \\\nworld");
}

#[test]
fn test_parser_arithmetic_precedence() {
    let lexer = Lexer::new(b"2 + 3 * 4");
    let mut parser = Parser::new(lexer);
    let prog = parser.parse_program();
    assert_eq!(prog.len(), 1);
    assert_eq!(
        prog[0],
        Stmt::Block(vec![Stmt::Expr(Expr::BinaryOp(
            BinOp::Add,
            Box::new(Expr::Number("2".to_string())),
            Box::new(Expr::BinaryOp(
                BinOp::Mul,
                Box::new(Expr::Number("3".to_string())),
                Box::new(Expr::Number("4".to_string()))
            ))
        ))])
    );
}

#[test]
#[should_panic(expected = "syntax error")]
fn test_lexer_unterminated_comment() {
    let mut lexer = Lexer::new(b"/* unterminated");
    let _ = lexer.get_next_token();
}

fn parse_err(src: &str) -> BcError {
    Parser::try_new(Lexer::new(src.as_bytes()))
        .and_then(|mut p| p.try_parse_tree())
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
    let empty = Parser::new(Lexer::new(b"define f() {\nreturn ()\n}\n")).parse_program();
    assert!(matches!(&empty[0], Stmt::FunctionDef(f) if f.body == vec![Stmt::Return(None)]));
    // Allowed: break in a loop inside a function, return inside a loop in a function.
    let ok = "define f() { while (1) { break }; for (i = 0; 1; i++) return (1) }\n";
    assert!(
        Parser::try_new(Lexer::new(ok.as_bytes()))
            .and_then(|mut p| p.try_parse_tree())
            .is_ok()
    );
}

#[test]
fn test_assignment_binds_to_preceding_named_expression() {
    let parse = |src: &str| {
        let stmts = Parser::new(Lexer::new(src.as_bytes())).parse_program();
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
            BinOp::Add,
            var("a"),
            Box::new(Expr::AssignOp(AssignOp::Assign, var("b"), num("3")))
        )
    );
    assert_eq!(
        parse("-a = 5\n"),
        Expr::Negate(Box::new(Expr::AssignOp(
            AssignOp::Assign,
            var("a"),
            num("5")
        )))
    );
    assert_eq!(
        parse("(a = 5)\n"),
        Expr::Paren(Box::new(Expr::AssignOp(
            AssignOp::Assign,
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
    let _ = Parser::new(Lexer::new(b"quit\n")).parse_program();
}

#[test]
fn test_lexer_nul_and_control_characters_are_illegal_not_eof() {
    let syntax_message = |src: &[u8]| {
        let mut lexer = Lexer::new(src);
        loop {
            match lexer.try_get_next_token() {
                Ok(tok) if tok.token_type == TokenType::Eof => return None,
                Ok(_) => {}
                Err(BcError::Syntax { line, message, .. }) => return Some((line, message)),
                Err(e) => panic!("{e:?}"),
            }
        }
    };
    assert_eq!(
        syntax_message(b"3\x004\n"),
        Some((1, "illegal character: ^@".to_string()))
    );
    assert_eq!(
        syntax_message(b"\x01"),
        Some((1, "illegal character: ^A".to_string()))
    );
    assert_eq!(
        syntax_message(b"\x7f"),
        Some((1, "illegal character: \\177".to_string()))
    );
    assert_eq!(
        syntax_message("\u{e9}".as_bytes()),
        Some((1, "illegal character: \\303\\251".to_string()))
    );
    // A byte that does not start a well-formed UTF-8 sequence is a character of its own.
    for (src, shown) in [
        (&b"\xff"[..], "\\377"),
        (b"\x80", "\\200"),
        (b"\xc0\x80", "\\300"),
        (b"\xed\xa0\x80", "\\355"),
        (b"\xe2\x82", "\\342"),
        (b"\xf4\x90\x80\x80", "\\364"),
    ] {
        assert_eq!(
            syntax_message(src),
            Some((1, format!("illegal character: {shown}")))
        );
    }
    assert_eq!(
        syntax_message("\u{20ac}\u{1f600}".as_bytes()),
        Some((1, "illegal character: \\342\\202\\254".to_string()))
    );
    assert_eq!(
        syntax_message("\u{1f600}".as_bytes()),
        Some((1, "illegal character: \\360\\237\\230\\200".to_string()))
    );
    // Bytes that are not UTF-8 are kept in a string and skipped in a comment.
    let mut lexer = Lexer::new(b"\"a\xff\xed\xa0\x80\" /* \xff */");
    assert_eq!(lexer.get_next_token().value, b"a\xff\xed\xa0\x80");
    assert_eq!(lexer.get_next_token().token_type, TokenType::Eof);
    // A NUL inside a string or a comment does not end it.
    assert_eq!(syntax_message(b"\"a\0b\" /* \0 */ 1\n"), None);
    // An unterminated string is reported at the line where it starts.
    assert_eq!(
        syntax_message(b"1\n\"abc\nd\n"),
        Some((2, "illegal character: \"".to_string()))
    );
}

#[test]
#[should_panic(expected = "illegal character")]
fn test_lexer_unterminated_string() {
    let mut lexer = Lexer::new(b"\"unterminated");
    let _ = lexer.get_next_token();
}

#[test]
#[should_panic(expected = "illegal character: @")]
fn test_lexer_unexpected_char() {
    let mut lexer = Lexer::new(b"@");
    let _ = lexer.get_next_token();
}

#[test]
#[should_panic(expected = "illegal character: !")]
fn test_lexer_unexpected_bang() {
    let mut lexer = Lexer::new(b"!3");
    let _ = lexer.get_next_token();
}

#[cfg(all(not(miri), target_pointer_width = "64"))]
#[test]
fn test_lexer_rejects_a_text_beyond_the_unit_limit() {
    // The zeroed allocation is lazy: the lexer must reject the text without reading it.
    let text = vec![0u8; crate::verified_kernels::BC_UNIT_MAX + 1];
    let expected = BcError::Syntax {
        line: 1,
        message: "input unit too long".to_string(),
    };
    assert_eq!(Lexer::new(&text).try_peek_token(0), Err(expected));
}

#[test]
fn test_lexer_advance_past_end() {
    let mut lexer = Lexer::new(b"abc");
    lexer.advance_char(10);
}

#[test]
fn test_lexer_peek_past_eof() {
    let mut lexer = Lexer::new(b"123");
    assert_eq!(lexer.try_peek_token(5), Ok(TokenType::Eof));
}

#[test]
#[should_panic(expected = "syntax error")]
fn test_parser_eat_mismatch() {
    let mut parser = Parser::new(Lexer::new(b"define f 123"));
    let _ = parser.parse_program();
}

#[test]
#[should_panic(expected = "syntax error")]
fn test_parser_expected_separator() {
    let mut parser = Parser::new(Lexer::new(b"{ a = 5 b = 10 }"));
    let _ = parser.parse_program();
}

#[test]
#[should_panic(expected = "syntax error")]
fn test_parser_expected_function_name() {
    let mut parser = Parser::new(Lexer::new(b"define 123() {}"));
    let _ = parser.parse_program();
}

#[test]
#[should_panic(expected = "syntax error")]
fn test_parser_expected_parameter_name() {
    let mut parser = Parser::new(Lexer::new(b"define f(123) {}"));
    let _ = parser.parse_program();
}

#[test]
#[should_panic(expected = "syntax error")]
fn test_parser_expected_auto_separator() {
    let mut parser = Parser::new(Lexer::new(b"define f() { auto a 123; }"));
    let _ = parser.parse_program();
}

#[test]
fn test_lexer_and_parser_mutant_edge_cases() {
    // 1. CRLF line tracking across comments and multi-line strings
    let mut lexer = Lexer::new(b"/* line 1\r\n line 2 */\r\n123");
    let tok1 = lexer.get_next_token();
    assert_eq!(tok1.token_type, TokenType::Newline);
    let tok2 = lexer.get_next_token();
    assert_eq!(tok2.token_type, TokenType::Number);
    assert_eq!(tok2.line, 3);

    // 2. Semicolons and empty statement list parsing
    let mut parser = Parser::new(Lexer::new(b"; ; a = 1; ; b = 2; ;"));
    let prog = parser.parse_program();
    assert!(!prog.is_empty());

    // 3. Complex argument list with expressions and array parameters
    let mut parser2 = Parser::new(Lexer::new(b"f(1 + 2, a[])"));
    let prog2 = parser2.parse_program();
    assert_eq!(prog2.len(), 1);

    // 4. Tokenizer operator coverage
    let ops = "+= -= *= /= %= ^= == != <= >= ++ --";
    let mut lexer_ops = Lexer::new(ops.as_bytes());
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
    let mut lexer_lf = Lexer::new(b"\"hello \\\nworld\"");
    let tok_lf = lexer_lf.get_next_token();
    assert_eq!(tok_lf.token_type, TokenType::String);

    let mut lexer_crlf = Lexer::new(b"\"hello \\\r\nworld\"");
    let tok_crlf = lexer_crlf.get_next_token();
    assert_eq!(tok_crlf.token_type, TokenType::String);

    // Number token with backslash-newline continuation inside digits
    let mut lexer_num = Lexer::new(b"123\\\n456");
    let tok_num = lexer_num.get_next_token();
    assert_eq!(tok_num.token_type, TokenType::Number);
    assert_eq!(tok_num.value, b"123456");

    let mut lexer_num_crlf = Lexer::new(b"123\\\r\n456");
    let tok_num_crlf = lexer_num_crlf.get_next_token();
    assert_eq!(tok_num_crlf.token_type, TokenType::Number);
    assert_eq!(tok_num_crlf.value, b"123456");
}

#[test]
fn test_parser_precedence_associativity_and_bare_return() {
    // 1. Right-associativity of exponentiation operator '^'
    let mut parser_pow = Parser::new(Lexer::new(b"2^3^2"));
    let stmts_pow = parser_pow.parse_program();
    assert_eq!(stmts_pow.len(), 1);
    let target_stmt = match &stmts_pow[0] {
        Stmt::Block(inner) => &inner[0],
        other => other,
    };
    if let Stmt::Expr(Expr::BinaryOp(op1, left1, right1)) = target_stmt {
        assert_eq!(*op1, BinOp::Pow);
        assert_eq!(**left1, Expr::Number("2".to_string()));
        if let Expr::BinaryOp(op2, left2, right2) = &**right1 {
            assert_eq!(*op2, BinOp::Pow);
            assert_eq!(**left2, Expr::Number("3".to_string()));
            assert_eq!(**right2, Expr::Number("2".to_string()));
        } else {
            panic!("Expected right-associative nested exponentiation");
        }
    } else {
        panic!("Expected BinaryOp statement");
    }

    // 2. Bare GNU return statement parsing
    let mut parser_ret = Parser::new(Lexer::new(b"define f() { return }"));
    let stmts_ret = parser_ret.parse_program();
    assert_eq!(stmts_ret.len(), 1);
    if let Stmt::FunctionDef(fdef) = &stmts_ret[0] {
        assert_eq!(fdef.body.len(), 1);
        assert_eq!(fdef.body[0], Stmt::Return(None));
    } else {
        panic!("Expected FunctionDef statement");
    }

    // 3. Multi-argument call with array and expression arguments
    let mut parser_call = Parser::new(Lexer::new(b"f(1, a[], 3)"));
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
    let mut lexer_comment = Lexer::new(b"/* comment */ x = 5");
    let tok1 = lexer_comment.get_next_token();
    assert_eq!(tok1.token_type, TokenType::Letter);
    assert_eq!(tok1.value, b"x");

    // 2. Minus operator vs negative numbers
    let mut lexer_minus = Lexer::new(b"x - 5");
    let _ = lexer_minus.get_next_token(); // x
    let tok_op = lexer_minus.get_next_token(); // -
    assert_eq!(tok_op.token_type, TokenType::Minus);

    // 3. Argument list parsing with multiple expressions
    let mut parser_args = Parser::new(Lexer::new(b"f(1 + 2, 3 * 4)"));
    let stmts_args = parser_args.parse_program();
    assert_eq!(stmts_args.len(), 1);
}

#[test]
fn test_multi_array_parameter_call_parsing() {
    let mut parser_arrays = Parser::new(Lexer::new(b"f(x[], y[], z[])"));
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
    let mut lexer_nl = Lexer::new(b"a\n");
    let _ = lexer_nl.get_next_token(); // a
    let tok_nl = lexer_nl.get_next_token(); // \n
    assert_eq!(tok_nl.token_type, TokenType::Newline);
    assert_eq!(tok_nl.line, 2);

    // 2. String token with CRLF backslash continuation
    let mut lexer_str = Lexer::new(b"\"hello \\\r\n world\"");
    let tok_str = lexer_str.get_next_token();
    assert_eq!(tok_str.token_type, TokenType::String);
    assert_eq!(tok_str.value, b"hello \\\r\n world");

    // 3. Number token with CRLF backslash continuation
    let mut lexer_num = Lexer::new(b"123\\\r\n456");
    let tok_num = lexer_num.get_next_token();
    assert_eq!(tok_num.token_type, TokenType::Number);
    assert_eq!(tok_num.value, b"123456");
}

#[test]
fn test_argument_list_invalid_syntax_error_message() {
    let panic_res =
        std::panic::catch_unwind(|| Parser::new(Lexer::new(b"f(a + ])")).parse_program());
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
    let mut lexer_comment = Lexer::new(b"/* a / b */ 42");
    let tok_comment = lexer_comment.get_next_token();
    assert_eq!(tok_comment.token_type, TokenType::Number);
    assert_eq!(tok_comment.value, b"42");

    // 2. Standalone dot without trailing digit panics with unexpected character
    let panic_dot = std::panic::catch_unwind(|| {
        let mut lexer_dot = Lexer::new(b". + 1");
        let _ = lexer_dot.get_next_token();
    });
    assert!(panic_dot.is_err());
}

#[test]
fn test_number_and_string_scan_token_crlf_short_circuit_precedence() {
    // Number token ending before newline: 123+\n
    let mut lexer_num = Lexer::new(b"123+\n");
    let tok_num = lexer_num.get_next_token();
    assert_eq!(tok_num.token_type, TokenType::Number);
    assert_eq!(tok_num.value, b"123");

    // String token with plus newline: "abc+\n"
    let mut lexer_str = Lexer::new(b"\"abc+\n\"");
    let tok_str = lexer_str.get_next_token();
    assert_eq!(tok_str.token_type, TokenType::String);
    assert_eq!(tok_str.value, b"abc+\n");

    // String token with unescaped CRLF (kills == vs != mutants on line 416)
    let mut lexer_raw_crlf = Lexer::new(b"\"a\r\nb\"");
    let tok_raw_crlf = lexer_raw_crlf.get_next_token();
    assert_eq!(tok_raw_crlf.token_type, TokenType::String);
    assert_eq!(tok_raw_crlf.value, b"a\r\nb");

    // Non-dot identifier followed by digit: x5 (kills == vs != on line 435)
    let mut lexer_x5 = Lexer::new(b"x5");
    let tok_x5 = lexer_x5.get_next_token();
    assert_eq!(tok_x5.token_type, TokenType::Letter);
    assert_eq!(tok_x5.value, b"x5");

    // Number token followed by space plus newline: 123 + \n (kills && vs || on line 449)
    let mut lexer_num_space = Lexer::new(b"123 + \n");
    let tok_num_space = lexer_num_space.get_next_token();
    assert_eq!(tok_num_space.token_type, TokenType::Number);
    assert_eq!(tok_num_space.value, b"123");

    // String token with backslash non-CRLF (kills line 416:59 and line 416:88)
    let mut lexer_str_bs_x = Lexer::new(b"\"a \\x\nb\"");
    let tok_str_bs_x = lexer_str_bs_x.get_next_token();
    assert_eq!(tok_str_bs_x.token_type, TokenType::String);
    assert_eq!(tok_str_bs_x.value, b"a \\x\nb");

    let mut lexer_str_bs_rx = Lexer::new(b"\"a \\\rxb\"");
    let tok_str_bs_rx = lexer_str_bs_rx.get_next_token();
    assert_eq!(tok_str_bs_rx.token_type, TokenType::String);
    assert_eq!(tok_str_bs_rx.value, b"a \\\rxb");

    // Number token followed by backslash x newline: 123 \x\n (kills line 449:38)
    let mut lexer_num_bs_x = Lexer::new(b"123 \\x\n");
    let tok_num_bs_x = lexer_num_bs_x.get_next_token();
    assert_eq!(tok_num_bs_x.token_type, TokenType::Number);
    assert_eq!(tok_num_bs_x.value, b"123");
}

#[test]
fn test_fallible_parser_and_lexer() {
    let mut lexer_err = Lexer::new(b"@");
    assert!(lexer_err.try_get_next_token().is_err());

    let mut lexer_peek_err = Lexer::new(b"1 @");
    assert!(lexer_peek_err.try_peek_token(1).is_err());

    assert!(Parser::try_new(Lexer::new(b"/* unterminated")).is_err());

    let mut parser_syntax = Parser::try_new(Lexer::new(b"1 + * 2\n")).unwrap();
    assert!(parser_syntax.try_parse_tree().is_err());

    let mut parser_quit = Parser::try_new(Lexer::new(b"quit\n")).unwrap();
    assert_eq!(parser_quit.try_parse_tree(), Err(BcError::Quit));

    // Verify statement & primary expression variants in try_parse_program
    let mut parser_variants = Parser::try_new(Lexer::new(
        b"\"hello\"\nwhile (0) break\nif (1) x = 2\nlength(123)\nscale(1.23)\nobase = 16\nscale = 4\n",
    ))
    .unwrap();
    let stmts = parser_variants.try_parse_tree().unwrap();
    assert_eq!(stmts.len(), 7);
    assert_eq!(
        stmts[0],
        Stmt::Block(vec![Stmt::StringLiteral(b"hello".to_vec())])
    );
    assert!(
        matches!(&stmts[1], Stmt::Block(v) if matches!(&v[0], Stmt::While(_, body) if **body == Stmt::Break))
    );
    assert!(matches!(&stmts[2], Stmt::Block(v) if matches!(&v[0], Stmt::If(_, _))));
    assert!(
        matches!(&stmts[3], Stmt::Block(v) if matches!(&v[0], Stmt::Expr(Expr::LengthCall(_))))
    );
    assert!(matches!(&stmts[4], Stmt::Block(v) if matches!(&v[0], Stmt::Expr(Expr::ScaleCall(_)))));
    assert!(
        matches!(&stmts[5], Stmt::Block(v) if matches!(&v[0], Stmt::Expr(Expr::AssignOp(_, t, _)) if **t == Expr::RegisterAccess(Register::Obase)))
    );
    assert!(
        matches!(&stmts[6], Stmt::Block(v) if matches!(&v[0], Stmt::Expr(Expr::AssignOp(_, t, _)) if **t == Expr::RegisterAccess(Register::Scale)))
    );
}
