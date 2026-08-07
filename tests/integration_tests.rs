// SPDX-License-Identifier: MIT

//! Differential E2E integration tests comparing the bc_clone binary to the system bc utility.

use std::io::Write;
use std::process::{Command, Stdio};

fn run_command(cmd_name: &str, args: &[&str], input: &str) -> (i32, String, String) {
    let mut child = Command::new(cmd_name)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn command");

    {
        let stdin = child.stdin.as_mut().expect("failed to get stdin");
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write to stdin");
    }

    let output = child.wait_with_output().expect("failed to wait for output");
    let exit_code = output.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    (exit_code, stdout, stderr)
}

fn check_differential(program: &str, flags: &[&str], match_stderr: bool) {
    let input = if program.ends_with('\n') {
        program.to_string()
    } else {
        format!("{}\n", program)
    };

    let (_bc_code, bc_out, bc_err) = run_command("bc", flags, &input);

    let bin_path = env!("CARGO_BIN_EXE_bc_clone");
    let (_clone_code, clone_out, clone_err) = run_command(bin_path, flags, &input);

    assert_eq!(
        clone_out, bc_out,
        "Stdout mismatch!\nProgram: {:?}\nExpected:\n{:?}\nGot:\n{:?}",
        program, bc_out, clone_out
    );

    if match_stderr {
        let has_bc_err = !bc_err.trim().is_empty();
        let has_clone_err = !clone_err.trim().is_empty();
        assert_eq!(
            has_clone_err, has_bc_err,
            "Stderr mismatch!\nExpected error: {} ({:?})\nGot: {} ({:?})",
            has_bc_err, bc_err, has_clone_err, clone_err
        );
    }
}

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
        check_differential(prog, &[], false);
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
        check_differential(prog, &[], false);
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
        check_differential(prog, &[], false);
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
        check_differential(prog, &[], false);
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
        check_differential(prog, &[], false);
    }
}

#[test]
fn test_builtin_errors() {
    check_differential("sqrt(-2)", &[], true);
    check_differential("1 / 0", &[], true);
    check_differential("1 % 0", &[], true);
    check_differential("a = 1; a /= 0", &[], true);
    check_differential("a = 1; a %= 0", &[], true);
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
        check_differential(prog, &[], false);
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
        check_differential(prog, &[], false);
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
        check_differential(prog, &[], false);
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
        check_differential(prog, &[], false);
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
        check_differential(prog, &[], false);
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
        check_differential(prog, &flags, false);
    }
}

#[test]
fn test_math_library_errors() {
    let flags = ["-l"];
    check_differential("l(-1)", &flags, true);
    check_differential("l(0)", &flags, true);
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
        check_differential(prog, &[], false);
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
    check_differential(complex_program, &["-l"], false);
}

#[test]
fn test_parser_and_evaluator_edge_cases() {
    check_differential("a = 5; a ^= 2; a", &[], false);
    check_differential("a = 5; a -= 2; a", &[], false);
    check_differential("5 >= 2", &[], false);
    check_differential("5 != 2", &[], false);
    check_differential("{ 1 }", &[], false);
    check_differential("define f() { return; }; f()", &[], false);
    check_differential("a", &[], false);
    check_differential("1.2 > 1.23", &[], false);
    check_differential("1.23 > 1.2", &[], false);
    check_differential("++a; a", &[], false);
    check_differential("++a[0]; a[0]", &[], false);
    check_differential("scale = 5; ++scale; scale", &[], false);
    check_differential("ibase = 10; ++ibase; ibase", &[], false);
    check_differential("obase = 10; ++obase; obase", &[], false);
    check_differential("define f(x[]) { return(1); }; f(a[])", &[], false);
    check_differential("define f() { while(1) { return(42); }; }; f()", &[], false);
    check_differential(
        "define g() { for(i=0; i<10; ++i) { return(42); }; }; g()",
        &[],
        false,
    );

    check_differential("f(1)", &[], true);
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
        check_differential(prog, &["-l"], false);
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
        check_differential(prog, &[], false);
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
    check_differential(demo_program, &["-l"], false);
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
    std::thread::sleep(std::time::Duration::from_millis(800));

    // Send SIGINT (2) using kill command
    let pid = child.id();
    let status = Command::new("kill")
        .args(&["-2", &pid.to_string()])
        .status()
        .expect("failed to send SIGINT");
    assert!(status.success());

    let output = child.wait_with_output().expect("failed to wait");
    assert!(output.status.success());
    let stderr_str = String::from_utf8_lossy(&output.stderr);
    assert!(stderr_str.contains("(interrupt) Exiting bc."));
}
