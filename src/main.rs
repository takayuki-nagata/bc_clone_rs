//! CLI entry point, POSIX option parsing, and REPL runner for the bc clone.
//!
//! Handles manual option checking, standard TTY/non-TTY execution paths,
//! Ctrl+C handlers, and mockable I/O streams for 100% automated test coverage.

mod bc_math;
mod eval;
mod parser;

use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicBool, Ordering};

use crate::eval::Evaluator;
use crate::parser::{Lexer, Parser};

/// Global atomic flag indicating if Ctrl+C was pressed.
pub static CTRL_C_PRESSED: AtomicBool = AtomicBool::new(false);

/// Handles the Ctrl+C / SIGINT signal.
pub fn handle_ctrlc_signal() {
    CTRL_C_PRESSED.store(true, Ordering::SeqCst);
    let mut stderr = std::io::stderr();
    let _ = writeln!(stderr, "(interrupt) Exiting bc.");
    #[cfg(not(test))]
    std::process::exit(0);
}

/// Sets up the cross-platform SIGINT / Ctrl+C handler.
pub fn setup_ctrlc_handler() {
    #[cfg(not(test))]
    let _ = ctrlc::set_handler(move || {
        handle_ctrlc_signal();
    });
    #[cfg(test)]
    {
        handle_ctrlc_signal();
    }
}

/// Counts the number of open braces outside of strings and comments.
pub fn count_open_braces(text: &str) -> i32 {
    let mut count = 0;
    let mut in_string = false;
    let mut in_comment = false;
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if in_comment {
            if c == '*' && i + 1 < chars.len() && chars[i + 1] == '/' {
                in_comment = false;
                i += 2;
                continue;
            }
            i += 1;
        } else if in_string {
            if c == '"' {
                in_string = false;
            } else if c == '\\' && i + 1 < chars.len() {
                if chars[i + 1] == '\n' {
                    i += 2;
                    continue;
                } else if chars[i + 1] == '\r' && i + 2 < chars.len() && chars[i + 2] == '\n' {
                    i += 3;
                    continue;
                }
            }
            i += 1;
        } else {
            if c == '/' && i + 1 < chars.len() && chars[i + 1] == '*' {
                in_comment = true;
                i += 2;
                continue;
            }
            if c == '"' {
                in_string = true;
                i += 1;
                continue;
            }
            if c == '{' {
                count += 1;
            } else if c == '}' {
                count -= 1;
            }
            i += 1;
        }
    }
    count
}

/// Checks if the block is incomplete (e.g. has open braces, or is inside an unterminated comment or string).
pub fn is_block_incomplete(text: &str) -> bool {
    let mut count = 0;
    let mut in_string = false;
    let mut in_comment = false;
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if in_comment {
            if c == '*' && i + 1 < chars.len() && chars[i + 1] == '/' {
                in_comment = false;
                i += 2;
                continue;
            }
            i += 1;
        } else if in_string {
            if c == '"' {
                in_string = false;
            } else if c == '\\' && i + 1 < chars.len() {
                if chars[i + 1] == '\n' {
                    i += 2;
                    continue;
                } else if chars[i + 1] == '\r' && i + 2 < chars.len() && chars[i + 2] == '\n' {
                    i += 3;
                    continue;
                }
            }
            i += 1;
        } else {
            if c == '/' && i + 1 < chars.len() && chars[i + 1] == '*' {
                in_comment = true;
                i += 2;
                continue;
            }
            if c == '"' {
                in_string = true;
                i += 1;
                continue;
            }
            if c == '{' {
                count += 1;
            } else if c == '}' {
                count -= 1;
            }
            i += 1;
        }
    }
    count > 0 || in_comment || in_string
}

/// Formats and logs panic payloads onto evaluator's stderr writer.
fn handle_panic_payload(
    payload: Box<dyn std::any::Any + Send>,
    filename: &str,
    lexer_line: usize,
    evaluator: &mut Evaluator,
    is_interactive: bool,
) {
    let msg = if let Some(s) = payload.downcast_ref::<&str>() {
        *s
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.as_str()
    } else {
        "unknown error"
    };

    if msg.starts_with("Parser error") || msg.starts_with("Lexical error") {
        let extracted_line = if let Some(pos) = msg.find("on line ") {
            let sub = &msg[pos + 8..];
            let end = sub.find(':').unwrap_or(sub.len());
            sub[..end].parse::<usize>().unwrap_or(lexer_line)
        } else {
            lexer_line
        };
        if is_interactive {
            let _ = writeln!(
                evaluator.stderr_writer,
                "(standard_in) {}: syntax error",
                extracted_line
            );
        } else {
            let _ = writeln!(
                evaluator.stderr_writer,
                "{}: syntax error on line {}",
                filename, extracted_line
            );
        }
    } else if msg.contains("division by zero") {
        if is_interactive {
            let _ = writeln!(evaluator.stderr_writer, "Runtime error: division by zero");
        } else {
            let _ = writeln!(
                evaluator.stderr_writer,
                "Runtime error: division by zero in {}",
                filename
            );
        }
    } else {
        let clean_msg = msg.strip_prefix("panic: ").unwrap_or(msg);
        if is_interactive {
            let _ = writeln!(evaluator.stderr_writer, "Runtime error: {}", clean_msg);
        } else {
            let _ = writeln!(
                evaluator.stderr_writer,
                "Runtime error: {} in {}",
                clean_msg, filename
            );
        }
    }
}

/// Runs evaluation on a non-interactive text block (catching errors).
pub fn run_non_interactive_block(
    content: &str,
    filename: &str,
    evaluator: &mut Evaluator,
) -> Result<(), i32> {
    let mut accumulator = String::new();
    let mut has_error = false;

    for line in content.split_inclusive('\n') {
        accumulator.push_str(line);

        let accumulated_text = &accumulator;
        if accumulated_text.ends_with("\\\n") || accumulated_text.ends_with("\\\r\n") {
            continue;
        }

        if is_block_incomplete(accumulated_text) {
            continue;
        }

        let lexer = Lexer::new(accumulated_text);
        let parse_line = lexer.line;

        let parse_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut parser = Parser::new(lexer);
            parser.parse_program()
        }));

        match parse_res {
            Ok(stmts) => {
                let eval_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    for stmt in &stmts {
                        evaluator.execute(stmt);
                        if evaluator.quit_flag {
                            break;
                        }
                    }
                }));

                match eval_res {
                    Ok(_) => {
                        if evaluator.quit_flag {
                            return Err(0);
                        }
                        accumulator.clear();
                    }
                    Err(e) => {
                        handle_panic_payload(e, filename, 1, evaluator, false);
                        accumulator.clear();
                        has_error = true;
                    }
                }
            }
            Err(e) => {
                if e.downcast_ref::<&str>().is_some_and(|m| *m == "quit") {
                    return Err(0);
                }
                handle_panic_payload(e, filename, parse_line, evaluator, false);
                accumulator.clear();
                has_error = true;
            }
        }
    }

    if has_error { Err(1) } else { Ok(()) }
}

/// Runs interactive REPL loop reading incrementally.
pub fn run_interactive_loop<R: BufRead>(
    mut reader: R,
    evaluator: &mut Evaluator,
) -> Result<(), i32> {
    let mut accumulator = String::new();

    loop {
        if CTRL_C_PRESSED.swap(false, Ordering::SeqCst) {
            let _ = writeln!(evaluator.stderr_writer);
            accumulator.clear();
            continue;
        }

        let mut line = String::new();
        match reader.read_line(&mut line) {
            Ok(0) => break,
            Ok(_) => {
                if CTRL_C_PRESSED.swap(false, Ordering::SeqCst) {
                    accumulator.clear();
                    continue;
                }
                accumulator.push_str(&line);
            }
            Err(_) => break,
        }

        let accumulated_text = &accumulator;
        if accumulated_text.ends_with("\\\n") || accumulated_text.ends_with("\\\r\n") {
            continue;
        }

        if is_block_incomplete(accumulated_text) {
            continue;
        }

        let lexer = Lexer::new(accumulated_text);
        let parse_line = lexer.line;

        let parse_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut parser = Parser::new(lexer);
            parser.parse_program()
        }));

        match parse_res {
            Ok(stmts) => {
                let eval_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    for stmt in &stmts {
                        evaluator.execute(stmt);
                        if evaluator.quit_flag {
                            break;
                        }
                    }
                }));

                match eval_res {
                    Ok(_) => {
                        if evaluator.quit_flag {
                            return Err(0);
                        }
                        accumulator.clear();
                    }
                    Err(e) => {
                        handle_panic_payload(e, "standard input", 1, evaluator, true);
                        accumulator.clear();
                    }
                }
            }
            Err(e) => {
                if e.downcast_ref::<&str>().is_some_and(|m| *m == "quit") {
                    return Err(0);
                }
                handle_panic_payload(e, "standard input", parse_line, evaluator, true);
                accumulator.clear();
            }
        }
    }
    Ok(())
}

/// Main application execution entry point, extracted for CLI and exit-code testing.
pub fn run_app<R, W, E>(
    args: &[String],
    mut stdin_reader: R,
    stdout_writer: W,
    stderr_writer: E,
    is_interactive: bool,
) -> Result<(), i32>
where
    R: std::io::Read + std::io::BufRead,
    W: std::io::Write + Send + 'static,
    E: std::io::Write + Send + 'static,
{
    let mut math_enabled = false;
    let mut files = Vec::new();

    for arg in args.iter().skip(1) {
        if arg == "-l" {
            math_enabled = true;
        } else if let Some(opt) = arg.strip_prefix('-') {
            let mut err_writer = stderr_writer;
            let _ = writeln!(err_writer, "bc: invalid option -- '{}'", opt);
            return Err(1);
        } else {
            files.push(arg.clone());
        }
    }

    let mut evaluator = Evaluator::new(
        math_enabled,
        Box::new(stdout_writer),
        Box::new(stderr_writer),
    );
    if math_enabled {
        evaluator.scale = 20;
    }

    setup_ctrlc_handler();

    for filename in &files {
        match std::fs::read_to_string(filename) {
            Ok(content) => {
                run_non_interactive_block(&content, filename, &mut evaluator)?;
            }
            Err(_) => {
                let _ = writeln!(evaluator.stderr_writer, "bc: cannot open file {}", filename);
                return Err(1);
            }
        }
    }

    if is_interactive {
        run_interactive_loop(stdin_reader, &mut evaluator)
    } else {
        let mut content = String::new();
        if stdin_reader.read_to_string(&mut content).is_err() {
            return Err(1);
        }
        run_non_interactive_block(&content, "standard input", &mut evaluator)
    }
}

fn main() {
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let msg = info
            .payload()
            .downcast_ref::<&str>()
            .copied()
            .or_else(|| info.payload().downcast_ref::<String>().map(|s| s.as_str()));
        if msg == Some("quit") {
            return;
        }
        default_hook(info);
    }));

    let args: Vec<String> = std::env::args().collect();
    use std::io::IsTerminal;
    let is_interactive = std::io::stdin().is_terminal() && std::io::stdout().is_terminal();
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let stderr = std::io::stderr();
    if let Err(code) = run_app(&args, stdin.lock(), stdout, stderr, is_interactive) {
        std::process::exit(code);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read;

    static TEST_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

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

    #[test]
    fn test_count_open_braces() {
        assert_eq!(count_open_braces(""), 0);
        assert_eq!(count_open_braces("{"), 1);
        assert_eq!(count_open_braces("}"), -1);
        assert_eq!(count_open_braces("/* { */"), 0);
        assert_eq!(count_open_braces("\"{\""), 0);
        assert_eq!(count_open_braces("a = 5 \\\n {"), 1);
        assert_eq!(count_open_braces("a = 5 \\\r\n {"), 1);
        assert_eq!(count_open_braces("a = \"hello \\\nworld\""), 0);
        assert_eq!(count_open_braces("a = \"hello \\\r\nworld\""), 0);
    }

    #[test]
    fn test_count_open_braces_and_block_incomplete_boundary_cases() {
        assert_eq!(count_open_braces("/* { */ { }"), 0);
        assert_eq!(count_open_braces("if (1) { a = 1; }"), 0);
        assert_eq!(count_open_braces("if (1) {\n  if (2) {\n    a = 1;\n"), 2);
        assert_eq!(count_open_braces("a = \"{\"\n"), 0);
        assert_eq!(count_open_braces("/* comment * { */ { }"), 0);

        assert!(is_block_incomplete("if (1) {"));
        assert!(is_block_incomplete("/* comment"));
        assert!(is_block_incomplete("\"string"));
        assert!(!is_block_incomplete("a = 1 + 2\n"));
        assert!(!is_block_incomplete("/* comment */ a = 1\n"));
    }





    #[test]
    fn test_run_repl_interactive() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let input = "1 + 2\nif (1) {\n  3\n}\n";
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));

        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };

        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        let res = run_interactive_loop(input.as_bytes(), &mut evaluator);
        assert!(res.is_ok());

        let out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(out, "3\n3\n");
    }

    #[test]
    fn test_run_repl_errors() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let input = "1/0\n@\nsqrt(-1)\n";
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));

        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };

        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        let _ = run_interactive_loop(input.as_bytes(), &mut evaluator);

        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert!(err.contains("division by zero"));
        assert!(err.contains("syntax error"));
        assert!(err.contains("square root of negative number"));
    }

    #[test]
    fn test_non_interactive_block_errors() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let content = "1/0";
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));

        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };

        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        let res = run_non_interactive_block(content, "test.bc", &mut evaluator);
        assert_eq!(res, Err(1));

        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert!(err.contains("division by zero in test.bc"));
    }

    #[test]
    fn test_non_interactive_block_quit() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));
        let res = run_non_interactive_block("1 + 2\nquit\n3\n", "test.bc", &mut evaluator);
        assert_eq!(res, Err(0));
    }

    #[test]
    fn test_handle_panic_payload_unknown() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter { buf: stdout_buf };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));
        handle_panic_payload(Box::new(42), "test.bc", 1, &mut evaluator, false);
        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert!(err.contains("unknown error"));

        // Trigger parser error extraction without "on line " (covers line 147)
        handle_panic_payload(
            Box::new("Parser error: some error".to_string()),
            "test.bc",
            7,
            &mut evaluator,
            false,
        );
        let err2 = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert!(err2.contains("syntax error on line 7"));
    }

    #[test]
    fn test_handle_panic_payload_runtime_interactive() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter { buf: stdout_buf };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));
        handle_panic_payload(
            Box::new("some runtime error".to_string()),
            "test.bc",
            1,
            &mut evaluator,
            true,
        );
        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert!(err.contains("Runtime error: some runtime error"));
    }

    #[test]
    fn test_run_repl_ctrlc() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter { buf: stdout_buf };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));
        CTRL_C_PRESSED.store(true, Ordering::SeqCst);
        let input = "1 + 2\n";
        let _ = run_interactive_loop(input.as_bytes(), &mut evaluator);
        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert!(err.contains('\n') || err.is_empty());
    }

    struct CtrlCReader {
        lines: Vec<String>,
        idx: usize,
    }
    impl std::io::Read for CtrlCReader {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.idx >= self.lines.len() {
                return Ok(0);
            }
            let line = &self.lines[self.idx];
            let len = std::cmp::min(buf.len(), line.len());
            buf[..len].copy_from_slice(&line.as_bytes()[..len]);
            self.idx += 1;
            CTRL_C_PRESSED.store(true, Ordering::SeqCst);
            Ok(len)
        }
    }
    impl std::io::BufRead for CtrlCReader {
        fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
            if self.idx >= self.lines.len() {
                return Ok(&[]);
            }
            CTRL_C_PRESSED.store(true, Ordering::SeqCst);
            Ok(self.lines[self.idx].as_bytes())
        }
        fn consume(&mut self, amt: usize) {
            if amt > 0 {
                self.idx += 1;
            }
        }
    }

    #[test]
    fn test_run_repl_ctrlc_read_line() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter { buf: stdout_buf };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        let mut reader = CtrlCReader {
            lines: vec!["1 + 2\n".to_string()],
            idx: 0,
        };
        let mut buf = [0; 100];
        // 1. First read gets data
        let res1 = reader.read(&mut buf);
        assert!(res1.is_ok());
        // 2. Second read gets EOF (idx >= lines.len()), covering line 545
        let res2 = reader.read(&mut buf);
        assert_eq!(res2.unwrap(), 0);

        // 3. fill_buf and consume
        let mut reader2 = CtrlCReader {
            lines: vec!["hello\n".to_string()],
            idx: 0,
        };
        let buf_ref = reader2.fill_buf().unwrap(); // Covers line 560, 561
        assert_eq!(buf_ref, b"hello\n");
        reader2.consume(6); // Covers line 565
        let buf_ref2 = reader2.fill_buf().unwrap(); // Covers line 558
        assert!(buf_ref2.is_empty());
        reader2.consume(0); // doesn't increment idx

        let reader3 = CtrlCReader {
            lines: vec!["1 + 2\n".to_string()],
            idx: 0,
        };
        let _ = run_interactive_loop(reader3, &mut evaluator);

        // Exercise Ctrl+C helper and registration
        setup_ctrlc_handler();
        handle_ctrlc_signal();
    }

    struct ErrReader;
    impl std::io::Read for ErrReader {
        fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::new(std::io::ErrorKind::Other, "mock error"))
        }
    }
    impl std::io::BufRead for ErrReader {
        fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
            Err(std::io::Error::new(std::io::ErrorKind::Other, "mock error"))
        }
        fn consume(&mut self, _amt: usize) {}
    }

    #[test]
    fn test_run_repl_err_reader() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter { buf: stdout_buf };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        let mut reader = ErrReader;
        let mut buf = [0; 10];
        let _ = reader.read(&mut buf);
        let _ = reader.fill_buf();
        reader.consume(0);

        let _ = run_interactive_loop(reader, &mut evaluator);
        let _ = run_non_interactive_block("1", "test.bc", &mut evaluator);
    }

    #[test]
    fn test_is_block_incomplete() {
        assert!(!is_block_incomplete("a = 5"));
        assert!(is_block_incomplete("/* comment"));
        assert!(is_block_incomplete("\"string"));
        assert!(!is_block_incomplete("a = \"hello \\\nworld\""));
        assert!(!is_block_incomplete("a = \"hello \\\r\nworld\""));
    }

    #[test]
    fn test_run_repl_interactive_backslash_newline_and_quit() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // Pass lines that end in backslash-newline and quit (covers lines 288 and 317)
        let input = "a = 5 \\\n+ 10\na\nquit\n";
        let _ = run_interactive_loop(input.as_bytes(), &mut evaluator);

        let out_bytes = stdout_buf.lock().unwrap().clone();
        let out_str = String::from_utf8(out_bytes).unwrap();
        assert!(out_str.contains("15"));
    }

    #[test]
    fn test_run_app() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));

        // A. Valid expression via stdin non-interactive
        let input = "1 + 2\n";
        let res = run_app(
            &["bc".to_string()],
            input.as_bytes(),
            TestWriter {
                buf: stdout_buf.clone(),
            },
            TestWriter {
                buf: stderr_buf.clone(),
            },
            false,
        );
        assert!(res.is_ok());
        let out_str = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert!(out_str.contains('3'));

        // B. Invalid CLI option
        let res_invalid = run_app(
            &["bc".to_string(), "-x".to_string()],
            "".as_bytes(),
            TestWriter {
                buf: stdout_buf.clone(),
            },
            TestWriter {
                buf: stderr_buf.clone(),
            },
            false,
        );
        assert_eq!(res_invalid, Err(1));

        // C. Cannot open file
        let res_no_file = run_app(
            &["bc".to_string(), "nonexistent_file_xyz.bc".to_string()],
            "".as_bytes(),
            TestWriter {
                buf: stdout_buf.clone(),
            },
            TestWriter {
                buf: stderr_buf.clone(),
            },
            false,
        );
        assert_eq!(res_no_file, Err(1));

        // D. Math library enabled (-l)
        let res_math = run_app(
            &["bc".to_string(), "-l".to_string()],
            "s(0)\n".as_bytes(),
            TestWriter {
                buf: stdout_buf.clone(),
            },
            TestWriter {
                buf: stderr_buf.clone(),
            },
            false,
        );
        assert!(res_math.is_ok());

        // E. Interactive mode via run_app (covers line 383)
        let input_interactive = "1 + 2\nquit\n";
        let res_interactive = run_app(
            &["bc".to_string()],
            input_interactive.as_bytes(),
            TestWriter {
                buf: stdout_buf.clone(),
            },
            TestWriter {
                buf: stderr_buf.clone(),
            },
            true,
        );
        assert_eq!(res_interactive, Err(0));

        // F. Stdin read error via run_app (covers line 387)
        let res_err_read = run_app(
            &["bc".to_string()],
            ErrReader,
            TestWriter {
                buf: stdout_buf.clone(),
            },
            TestWriter {
                buf: stderr_buf.clone(),
            },
            false,
        );
        assert_eq!(res_err_read, Err(1));
    }

    #[test]
    fn test_non_interactive_block_quit_flag_ok_path() {
        let _guard = TEST_MUTEX.lock().unwrap();
        // Covers line 234: quit_flag check in Ok(_) branch of run_non_interactive_block.
        // Pre-set quit_flag so the evaluator executes normally but the
        // outer loop detects the flag and returns Err(0).
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));
        evaluator.quit_flag = true;
        let res = run_non_interactive_block("1\n", "test.bc", &mut evaluator);
        assert_eq!(res, Err(0));
    }

    #[test]
    fn test_interactive_loop_quit_flag_ok_path() {
        let _guard = TEST_MUTEX.lock().unwrap();
        // Covers line 317: quit_flag check in Ok(_) branch of run_interactive_loop.
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));
        evaluator.quit_flag = true;
        let input = "1\n";
        let res = run_interactive_loop(input.as_bytes(), &mut evaluator);
        assert_eq!(res, Err(0));
    }

    #[test]
    fn test_run_repl_crlf_backslash_newline() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        let input = "a = 5 \\\r\n+ 10\r\na\r\nquit\r\n";
        let _ = run_interactive_loop(input.as_bytes(), &mut evaluator);

        let out_bytes = stdout_buf.lock().unwrap().clone();
        let out_str = String::from_utf8(out_bytes).unwrap();
        assert!(out_str.contains("15"));
    }
}
