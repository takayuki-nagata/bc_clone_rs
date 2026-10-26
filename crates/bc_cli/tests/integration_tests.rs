// SPDX-License-Identifier: MIT

//! Differential E2E integration tests comparing the bc_clone binary to the system bc utility.

mod common;

use common::{check_differential, expected_exit_code, normalize_gnu_stderr, run_command};
use std::process::{Command, Stdio};

#[test]
fn test_basic_arithmetic() {
    let programs = [
        "1 + 2",
        "5 - 3",
        "4 * 3",
        "10 / 3",
        "10 % 3",
        "-5 + 3",
        "3 * -2",
        "2^3",
        "2^0",
        "2.5^2",
        "2.5^0",
        "2.5^-2",
        "1.2345 + 5.6789",
        "10.000 - 0.001",
        "0.1234 * 0.5678",
        "1 / 7",
        "1.0 / 7",
        "3.2 % 1",
        "0 % 5",
        "2^-3",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_precedence_and_associativity() {
    let programs = [
        "2 + 3 * 4",
        "2 * 3 + 4",
        "10 - 4 - 3",
        "2 ^ 3 ^ 2",
        "(2 + 3) * 4",
        "2 * (3 + 4)",
        "2 + 3 * 4 ^ 2",
        "2 * 3 ^ 2 + 4",
        "a = 3; b = 4; a + b",
        "a = b = 5; a * b",
        "a = 2; b = 3; c = 4; a += b *= c; a; b; c",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_incr_decr() {
    let programs = [
        "a = 5; ++a",
        "a = 5; a++",
        "a = 5; --a",
        "a = 5; a--",
        "a = 5; b = ++a; a; b",
        "a = 5; b = a++; a; b",
        "a = 5; b = --a; a; b",
        "a = 5; b = a--; a; b",
        "a = 5; ++a + a++",
        "a = 5; a[0] = 10; ++a[0]; a[0]++",
        "scale = 5; a = 2.5; ++a; a++",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_scale_propagation() {
    let programs = [
        "scale = 5; 3 / 2",
        "scale = 0; 3 / 2",
        "scale = 10; 1 / 3",
        "scale = 2; a = 1.23; b = 4.567; a + b",
        "scale = 2; a = 1.23; b = 4.567; a - b",
        "scale = 2; a = 1.23; b = 4.567; a * b",
        "scale = 2; a = 1.23; b = 4.567; a / b",
        "scale = 2; a = 1.23; b = 4.567; a % b",
        "scale = 5; 2.5 ^ 3",
        "scale = 5; 2.5 ^ -3",
        "scale = 2; scale",
        "scale = 3; a = scale = 5; scale; a",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_builtin_functions() {
    let programs = [
        "length(123.45)",
        "length(0.0012)",
        "length(0)",
        "length(-12.34)",
        "length(001.20)",
        "length(0.000)",
        "length(100.00)",
        "scale(123.45)",
        "scale(0.0012)",
        "scale(0)",
        "scale(-12.34)",
        "scale(001.20)",
        "sqrt(2)",
        "scale = 5; sqrt(2)",
        "scale = 2; sqrt(0.04)",
        "scale = 1; sqrt(0.04)",
        "sqrt(0)",
        "sqrt(100)",
        "length(sqrt(2))",
        "scale(sqrt(2))",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_builtin_errors() {
    check_differential("sqrt(-2)", &[]);
    check_differential("1 / 0", &[]);
    check_differential("1 % 0", &[]);
    check_differential("a = 1; a /= 0", &[]);
    check_differential("a = 1; a %= 0", &[]);
}

#[test]
fn test_variables_and_arrays() {
    let programs = [
        "a = 5; a",
        "z = 10; z",
        "a[0] = 5; a[0]",
        "a[10] = 20; a[10]",
        "a[1.9] = 15; a[1]",
        "a[0]; a[1]; a[100]",
        "scale = 2; a[5.5] = 2.5; a[5]; scale(a[5])",
        "a = 2; a[2] = 5; a; a[2]",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_bases() {
    let programs = [
        "ibase = 8; 10",
        "ibase = 16; A",
        "ibase = 16; FF",
        "ibase = 16; 1A.8",
        "obase = 2; 10",
        "obase = 8; 10",
        "obase = 16; 255",
        "obase = 25; 1024",
        "obase = 125; 1024",
        "scale = 2; obase = 8; 0.15",
        "scale = 2; obase = 16; 0.5/1",
        "scale = 2; obase = 25; 1.04",
        "scale = 2; obase = 25; 0.00",
        "scale = 2; obase = 25; 0.04",
        "scale = 2; obase = 25; -0.04",
        "ibase = 8; obase = 12; 10",
        "ibase = A; obase = A; 10",
        "ibase = 16; a = FF; obase = 10; a",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_line_wrapping() {
    let programs = [
        "2^300",
        "obase=25; 2^150",
        "\"12345678901234567890123456789012345678901234567890123456789012345678901234567890\"",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_control_flow() {
    let programs = [
        "if (1 == 1) 5",
        "if (1 == 0) 5",
        "if (1 < 2) 10",
        "a = 0; while (a < 5) a = a + 1; a",
        "a = 0; for (i = 0; i < 5; ++i) a = a + i; a; i",
        "a = 0; while (1) { a = a + 1; if (a == 3) break; }; a",
        "a = 0; for (i = 0; 1; ++i) { a = a + i; if (i == 4) break; }; a; i",
        "1; quit; 2",
        "if (1 == 1) { 10; 20; }",
        "a = 1; if (a) 5",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_functions_and_scoping() {
    let programs = [
        "define f(x) { return (x * 2); }; f(5)",
        "define f() { a = 10; }; f()",
        "a = 100;\ndefine f() { auto a; a = 5; g(); };\ndefine g() { a; };\nf(); a",
        "a[0] = 100;\ndefine f() { auto a[]; a[0] = 5; g(); };\ndefine g() { a[0]; };\nf(); a[0]",
        "define f(x[]) { x[0] = 99; return(x[0]); };\na[0] = 5;\nf(a[]); a[0]",
        "define f(x) { if (x <= 1) return(1); return (x * f(x-1)); }; f(5)",
        "define fib(n) { if (n <= 1) return(n); return (fib(n-1) + fib(n-2)); }; fib(8)",
        "define f() { return (1); }; f(); define f() { return (2); }; f()",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_math_library() {
    let flags = ["-l"];
    let programs = [
        "s(0)",
        "s(0.5)",
        "s(-0.5)",
        "s(4)",
        "s(-4)",
        "c(0)",
        "c(0.5)",
        "c(-0.5)",
        "c(4)",
        "c(-4)",
        "a(0)",
        "a(1)",
        "a(-1)",
        "a(0.5)",
        "l(1)",
        "l(2)",
        "l(0.5)",
        "e(0)",
        "e(1)",
        "e(-1)",
        "e(0.5)",
        "j(0, 0)",
        "j(0, 1.5)",
        "j(1, 2.0)",
        "j(2, 2.5)",
        "j(-2, 2.5)",
        "s(c(0.5))",
        "a(s(1)/c(1))",
        "scale = 25; s(1.0)",
        "scale = 10; e(1)",
    ];
    for prog in &programs {
        check_differential(prog, &flags);
    }
}

#[test]
fn test_math_library_errors() {
    let flags = ["-l"];
    check_differential("l(-1)", &flags);
    check_differential("l(0)", &flags);
}

#[test]
fn test_lexical_rules() {
    let programs = [
        "1 /* comment */ + 2",
        "1 /* multi-line\ncomment */ + 2",
        "a = 5\n b = 10\n a + b",
        "a = 5 + \\\n10; a",
        "\"hello world\"",
        "\"hello \\\nworld\"",
        "1.2\\\n34 + 1",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_e2e_complex_calculations() {
    let complex_program = "
    scale = 15
    define pi() {
        return (4 * a(1))
    }
    
    define taylor_sin(x, n) {
        auto sum, term, i
        sum = 0
        term = x
        for (i = 1; i <= n; ++i) {
            sum = sum + term
            term = -term * x * x / ((2*i) * (2*i + 1))
        }
        return (sum)
    }

    p = pi()
    p
    s(p/6)
    taylor_sin(p/6, 10)

    obase = 16
    \"pi in base 16: \"
    p
    
    obase = 10
    define test_scoping(n) {
        auto val[], i
        for (i = 0; i < n; ++i) {
            val[i] = i * i
        }
        return (sum_array(val[], n))
    }
    
    define sum_array(arr[], size) {
        auto i, s
        s = 0
        for (i = 0; i < size; ++i) {
            s = s + arr[i]
        }
        return (s)
    }
    
    test_scoping(10)
    
    a = 10
    b = 20
    if (a < b) {
        if (b > 15) {
            \"ok\"
        }
    }
    ";
    check_differential(complex_program, &["-l"]);
}

#[test]
fn test_parser_and_evaluator_edge_cases() {
    check_differential("a = 5; a ^= 2; a", &[]);
    check_differential("a = 5; a -= 2; a", &[]);
    check_differential("5 >= 2", &[]);
    check_differential("5 != 2", &[]);
    check_differential("{ 1 }", &[]);
    check_differential("define f() { return; }; f()", &[]);
    check_differential("a", &[]);
    check_differential("1.2 > 1.23", &[]);
    check_differential("1.23 > 1.2", &[]);
    check_differential("++a; a", &[]);
    check_differential("++a[0]; a[0]", &[]);
    check_differential("scale = 5; ++scale; scale", &[]);
    check_differential("ibase = 10; ++ibase; ibase", &[]);
    check_differential("obase = 10; ++obase; obase", &[]);
    check_differential("define f(x[]) { return(1); }; f(a[])", &[]);
    check_differential("define f() { while(1) { return(42); }; }; f()", &[]);
    check_differential(
        "define g() { for(i=0; i<10; ++i) { return(42); }; }; g()",
        &[],
    );

    check_differential("f(1)", &[]);
}

#[test]
fn test_ibase_warnings_direct() {
    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let (code1, stdout1, stderr1) = run_command(bin_path, &[], "ibase = 1; ibase\n");
    assert_eq!(code1, 0);
    assert_eq!(stdout1.trim(), "2");
    assert!(stderr1.contains("warning") || stderr1.contains("too small"));

    let (code2, stdout2, stderr2) = run_command(bin_path, &[], "ibase = 17; ibase\n");
    assert_eq!(code2, 0);
    assert_eq!(stdout2.trim(), "16");
    assert!(stderr2.contains("warning") || stderr2.contains("too large"));
}

#[test]
fn test_scale_register_preservation() {
    let programs = [
        "scale = 5; s(0.5); scale",
        "scale = 3; c(0.2); scale",
        "scale = 7; a(1); scale",
        "scale = 2; l(2); scale",
        "scale = 4; e(1); scale",
        "scale = 6; j(1, 2); scale",
    ];
    for prog in &programs {
        check_differential(prog, &["-l"]);
    }
}

#[test]
fn test_gnu_extension_return() {
    let programs = [
        "define f(x) { return x * 2; }; f(5)",
        "define f(x) { if (x == 0) return 0; return x + f(x-1); }; f(5)",
        "define f() { return; }; f()",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

#[test]
fn test_user_fib_sqrt_demo() {
    let demo_program = "
    scale = 5
    \"--- Complex Calculation Demo ---\\n\"
    \"1. Fibonacci Function\\n\"
    define fib(n) {
        auto a, b, c, i
        a = 0; b = 1
        if (n == 0) return a
        if (n == 1) return b
        for (i = 2; i <= n; ++i) {
            c = a + b
            a = b
            b = c
        }
        return b
    }
    \"fib(12) = \"
    fib(12)
    \"2. Square Root\\n\"
    \"sqrt(fib(12)) = \"
    sqrt(fib(12))
    \"3. Math Library (e^1)\\n\"
    \"e(1) = \"
    e(1)
    ";
    check_differential(demo_program, &["-l"]);
}

#[test]
fn test_clone_cli_invalid_option() {
    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let (code, _, stderr) = run_command(bin_path, &["-x"], "");
    assert_eq!(code, 1);
    assert!(stderr.contains("invalid option"));
}

#[test]
fn test_clone_cli_files() {
    let temp_dir = std::env::temp_dir();
    let file_path = temp_dir.join("test_file.bc");
    std::fs::write(&file_path, "3 * 5\n").unwrap();
    let file_path_str = file_path.to_str().unwrap();

    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let (code, stdout, _) = run_command(bin_path, &[file_path_str], "");
    assert_eq!(code, 0);
    assert_eq!(stdout.trim(), "15");

    let _ = std::fs::remove_file(file_path);

    let (code2, _, stderr2) = run_command(bin_path, &["non_existent_file.bc"], "");
    assert_eq!(code2, 1);
    assert!(stderr2.contains("cannot open file"));
}

#[test]
fn test_clone_cli_file_quit() {
    let temp_dir = std::env::temp_dir();
    let file_path = temp_dir.join("quit.bc");
    std::fs::write(&file_path, "1\nquit\n2\n").unwrap();
    let file_path_str = file_path.to_str().unwrap();

    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let (code, stdout, _) = run_command(bin_path, &[file_path_str], "");
    assert_eq!(code, 0);
    assert_eq!(stdout.trim(), "1");

    let _ = std::fs::remove_file(file_path);
}

#[test]
fn test_clone_cli_multiple_files_and_stdin() {
    let temp_dir = std::env::temp_dir();
    let p1 = temp_dir.join("test1.bc");
    p1.write_to_file_content("a = 10\n");
    let p2 = temp_dir.join("test2.bc");
    p2.write_to_file_content("b = 20; a + b\n");

    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let (code, stdout, _) =
        run_command(bin_path, &[p1.to_str().unwrap(), p2.to_str().unwrap()], "");
    assert_eq!(code, 0);
    assert_eq!(stdout.trim(), "30");

    let _ = std::fs::remove_file(&p1);
    let _ = std::fs::remove_file(&p2);

    let p3 = temp_dir.join("test_stdin.bc");
    p3.write_to_file_content("scale = 5\n");
    let (code2, stdout2, _) = run_command(bin_path, &[p3.to_str().unwrap()], "1 / 3\n");
    assert_eq!(code2, 0);
    assert_eq!(stdout2.trim(), ".33333");

    let _ = std::fs::remove_file(&p3);
}

#[test]
fn test_clone_cli_math_scale() {
    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let (code, stdout, _) = run_command(bin_path, &["-l"], "scale\n");
    assert_eq!(code, 0);
    assert_eq!(stdout.trim(), "20");
}

trait WriteHelper {
    fn write_to_file_content(&self, content: &str);
}

impl WriteHelper for std::path::PathBuf {
    fn write_to_file_content(&self, content: &str) {
        std::fs::write(self, content).unwrap();
    }
}

#[test]
fn test_real_ctrlc_signal() {
    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let child = Command::new(bin_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn");

    // Wait a brief moment to ensure setup_ctrlc_handler has run
    std::thread::sleep(std::time::Duration::from_millis(1200));

    // Send SIGINT (2) using kill command
    let pid = child.id();
    let status = Command::new("kill")
        .args(["-2", &pid.to_string()])
        .status()
        .expect("failed to send SIGINT");
    assert!(status.success());

    let output = child.wait_with_output().expect("failed to wait");
    assert!(output.status.success());
    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(stderr_str.contains("(interrupt) Exiting bc."));
}

/// Error recovery per input unit, diagnostics, and exit status (`docs/COMPATIBILITY.md` §3).
#[test]
fn test_error_recovery_and_diagnostics() {
    let programs = [
        "1/0\n2+2",
        "1/0; 5\n7",
        "x = 5\n{ 1/0; x = 6 }\nx",
        "define f(x) { x = 99; return (1/0) }\nx = 5; f(1); x\nx",
        "define f() { return (sqrt(-1)) }\nf()",
        "define g() { return (1 % 0) }\ndefine f() { return (g()) }\nf()",
        "define f(x) { return (x) }\nf()\nf(1, 2)",
        "1\n2\n3 +\n4",
        "@\n1",
        "1 + * 2\n3",
        "1/0\nquit\n2",
        "scale = 3; x = 1/0; x",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

/// Syntax diagnostics name the file operand, and errors in an earlier file do not stop later
/// input from being processed.
#[test]
fn test_error_diagnostics_in_file_operands() {
    let path = std::env::temp_dir().join(format!("bc_clone_err_{}.bc", std::process::id()));
    std::fs::write(&path, "1\n1 + * 2\n1/0\n").unwrap();
    let path_str = path.to_str().unwrap();

    let (bc_code, bc_out, bc_err) = run_command("bc", &[path_str], "5\n");
    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let (clone_code, clone_out, clone_err) = run_command(bin_path, &[path_str], "5\n");
    let _ = std::fs::remove_file(&path);

    let expected_err = normalize_gnu_stderr(&bc_err);
    assert_eq!(clone_out, bc_out);
    assert_eq!(clone_err, expected_err);
    assert_eq!(clone_code, expected_exit_code(bc_code, &expected_err));
    assert_eq!(clone_code, 1);
}

/// Register clamping, array subscript bounds, exponent rules, and digits >= ibase
/// (`docs/COMPATIBILITY.md` §2, §3.3), where bc_clone and GNU bc agree.
#[test]
fn test_limits_matching_gnu() {
    let programs = [
        "scale = -0.5; scale",
        "scale = 2.7; scale",
        "ibase = -5; ibase",
        "ibase = 1; ibase",
        "obase = 1; obase",
        "obase = -3; obase",
        "obase = 99999999999; obase",
        "x = (scale = 2.7); x",
        "a[1.5] = 3; a[1]",
        "a[-0.5] = 4; a[0]",
        "a[16777215] = 1; a[16777215]",
        "a[16777216] = 2",
        "x = a[-1]",
        "define f(n) { return (a[n]) }\nf(-1)",
        "ibase = 2; 12",
        "ibase = 2; 3",
        "ibase = 2; 1.1",
        "2^2.0",
        "2^2.5",
        "x = 2; x ^= 0.5; x",
        "2^9223372036854775808",
        "2^-9223372036854775809",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
    check_differential("scale = 3; l(0)", &["-l"]);
    check_differential("scale = 0; l(-1)", &["-l"]);
}

/// Implementation-defined limits that differ from GNU bc (`docs/COMPATIBILITY.md` §2, §5).
#[test]
fn test_limits_specific_to_bc_clone() {
    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let cases: [(&str, &str, &str, i32); 6] = [
        (
            "scale = 99999999999999999999; scale\n",
            "1000000000\n",
            "Runtime warning (func=(main)): scale too large, set to 1000000000\n",
            0,
        ),
        (
            // Previously the scale was truncated to 32 bits and this printed 1.
            "scale = 4294967297; scale\n",
            "1000000000\n",
            "Runtime warning (func=(main)): scale too large, set to 1000000000\n",
            0,
        ),
        (
            "ibase = 20; ibase\n",
            "16\n",
            "Runtime warning (func=(main)): ibase too large, set to 16\n",
            0,
        ),
        (
            "0.5 ^ 2000000000\n1\n",
            "1\n",
            "Runtime error (func=(main)): scale too large\n",
            1,
        ),
        (
            "scale = 1000000000; 1 % 0.1\n2\n",
            "2\n",
            "Runtime error (func=(main)): scale too large\n",
            1,
        ),
        (
            "scale = 999999999; ++scale; ++scale; scale\n",
            "1000000000\n1000000000\n1000000000\n",
            "Runtime warning (func=(main)): scale too large, set to 1000000000\n",
            0,
        ),
    ];
    for (input, out, err, code) in cases {
        let (c, o, e) = run_command(bin_path, &[], input);
        assert_eq!(
            (o.as_str(), e.as_str(), c),
            (out, err, code),
            "input: {:?}",
            input
        );
    }
}

/// Checks a `-l` result against the exact value truncated toward zero
/// (`docs/COMPATIBILITY.md` §3.4).
///
/// The reference is GNU bc evaluated at `scale + 100` and then truncated; GNU's own argument
/// reduction loses digits for large arguments, hence the generous margin. Truncation is
/// ill-conditioned when the true value lies within the reference error of a multiple of
/// 10^-scale, so the truncations of the reference ± 10^-(scale+90) are accepted as well.
fn check_math_oracle(scale: usize, expr: &str) {
    let hi = scale + 100;
    let eps = scale + 90;
    let reference_prog =
        format!("scale={hi}; v={expr}; e=10^-{eps}; scale={scale}; v/1; (v+e)/1; (v-e)/1\n");
    let (_, reference, _) = run_command("bc", &["-l"], &reference_prog);
    let accepted: Vec<String> = reference
        .replace("\\\n", "")
        .lines()
        .map(str::to_string)
        .collect();

    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let (code, out, err) = run_command(bin_path, &["-l"], &format!("scale={scale}; {expr}\n"));
    let got = out.replace("\\\n", "");
    let got = got.trim_end();
    assert_eq!((code, err.as_str()), (0, ""), "scale={scale}; {expr}");
    assert!(
        accepted.iter().any(|a| a == got),
        "scale={scale}; {expr}\nexpected one of {accepted:?}\ngot {got:?}"
    );
}

#[test]
fn test_math_library_against_high_precision_oracle() {
    let exprs = [
        "s(0)",
        "s(1)",
        "s(-3.14159)",
        "s(1000000)",
        "s(-10^30)",
        "s(10^40)",
        "s(7^50)",
        "c(0)",
        "c(355)",
        "c(-12345.678)",
        "c(10^40)",
        "a(0.001)",
        "a(-1)",
        "a(10^30)",
        "l(0.000000000000000000000000000001)",
        "l(2)",
        "l(123456789.123)",
        "l(100000000000000000000000000000000000000000000000000)",
        "e(-100)",
        "e(0.0000001)",
        "e(230.5)",
        "j(0,100)",
        "j(-3,7)",
        "j(20,1)",
        "j(2,-30)",
    ];
    for scale in [0, 5, 20] {
        for expr in exprs {
            check_math_oracle(scale, expr);
        }
    }
}

/// Assignment targets, printing of assignment statements, and misplaced `break`/`return`.
#[test]
fn test_assignment_and_statement_placement() {
    let programs = [
        "A = 1; A",
        "1 = 2",
        "(a) = 2",
        "a[1] = 2 = 3",
        "a + b = 3; b",
        "-a = 5; a",
        "(a = 5)",
        "-(a = 5)",
        "x = (a = 3) + 1; x",
        "a = 1 + b = 2; a; b",
        "a = b = c = 4; a + b + c",
        "break\n1",
        "{ break }\n1",
        "define f() { break }\n1",
        "if (1) return\n1",
        "return (2)\n1",
        "define f() { while (1) { return (1) } }; f()",
        "for (i = 0; i < 3; i++) { if (i == 1) break }; i",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}

/// `-s` rejects and `-w` warns about the extensions in `docs/COMPATIBILITY.md` §4, with GNU bc's
/// diagnostics; POSIX programs are unaffected.
#[test]
fn test_extension_policy_flags() {
    let programs = [
        "abc = 1; abc",
        "1 < 2",
        "2 == 2; 3",
        "define f(x) {\nreturn x\n}\nf(2)",
        "define f(x) { return (x) }\nf(2)",
        "define f() {\nauto ab\nreturn (1)\n}",
        "define fn() {\nreturn (1)\n}",
        "define f(ab) {\nreturn (1)\n}",
        "define f(x[]) {\nreturn (1)\n}\nf(ab[])",
        "x = 1; if (x) 5",
        "define f(x[]) {\nreturn (x[0])\n}\na[0] = 7; f(a[])",
        "for (i = 0; i < 2; i++) i",
    ];
    for flag in ["-s", "-w"] {
        for prog in &programs {
            check_differential(prog, &[flag]);
        }
    }
}

/// A named expression is evaluated once, before the right-hand side (found by the differential
/// proptest: `a[i++] += 5` used to evaluate `i++` twice and `c += c++` added the new value).
#[test]
fn test_assignment_target_evaluated_once_first() {
    let programs = [
        "i = 0; a[i++] += 5; i; a[0]; a[1]",
        "i = 0; a[i++]++; i; a[0]; a[1]",
        "i = 0; ++a[i++]; i; a[0]",
        "i = 0; x = a[i++]--; i; x; a[0]",
        "c = 5; c += c++; c",
        "c = 5; c -= c--; c",
        "c = 5; c *= (c = 2); c",
        "i = 0; a[i++] = i; a[0]; a[1]",
        "i = 5; i = i++; i",
        "define f(p) {\nauto q\nq = p\nreturn (q)\n}\nf(1)\np = 2; q = 3; p + q",
    ];
    for prog in &programs {
        check_differential(prog, &[]);
    }
}
