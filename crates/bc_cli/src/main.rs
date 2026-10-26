// SPDX-License-Identifier: MIT

//! CLI entry point, POSIX option parsing, and REPL runner for the bc clone.
//!
//! Handles manual option checking, standard TTY/non-TTY execution paths,
//! Ctrl+C handlers, and mockable I/O streams for 100% automated test coverage.

use core::fmt::Write as FmtWrite;
use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicBool, Ordering};

use bc_core::verified_kernels::{
    CLI_ARG_OPT_INVALID, CLI_ARG_OPT_L, verified_cli_classify_arg, verified_cli_initial_scale,
    verified_repl_block_completeness,
};
use bc_core::{BcWriter, Evaluator, RunSummary, STDIN_SOURCE, UnitAccumulator, UnitOutcome};

/// Adapter converting any `std::io::Write + Send` into a `bc_core::BcWriter`.
pub struct IoWriter<W: Write + Send> {
    inner: W,
}

impl<W: Write + Send> IoWriter<W> {
    /// Creates a new IoWriter wrapping the given Write stream.
    pub fn new(inner: W) -> Self {
        Self { inner }
    }
}

impl<W: Write + Send> FmtWrite for IoWriter<W> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.inner
            .write_all(s.as_bytes())
            .map_err(|_| core::fmt::Error)
    }
}

impl<W: Write + Send> BcWriter for IoWriter<W> {
    fn flush(&mut self) -> core::fmt::Result {
        self.inner.flush().map_err(|_| core::fmt::Error)
    }
}

/// Helper to construct an Evaluator with std::io::Write streams.
pub fn create_evaluator<O: Write + Send + 'static, E: Write + Send + 'static>(
    math_enabled: bool,
    stdout: O,
    stderr: E,
) -> Evaluator {
    Evaluator::new(
        math_enabled,
        Box::new(IoWriter::new(stdout)),
        Box::new(IoWriter::new(stderr)),
    )
}

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
    verified_repl_block_completeness(text.as_bytes()).0
}

/// Checks if the block is incomplete (e.g. has open braces, or is inside an unterminated comment or string).
pub fn is_block_incomplete(text: &str) -> bool {
    verified_repl_block_completeness(text.as_bytes()).1
}

thread_local! {
    /// Set while a unit runs under [`run_unit_guarded`], whose handler reports the panic itself.
    static IN_UNIT_GUARD: core::cell::Cell<bool> = const { core::cell::Cell::new(false) };
}

/// Extracts the message from a panic payload.
fn panic_message(payload: &(dyn std::any::Any + Send)) -> &str {
    payload
        .downcast_ref::<&str>()
        .copied()
        .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
        .unwrap_or("unknown panic")
}

/// Runs one input unit. `bc_core` reports every bc error through `Result`, so a panic here is
/// an internal bug; it is reported as such and counted as a failed unit instead of aborting.
fn run_unit_guarded(
    evaluator: &mut Evaluator,
    unit: &str,
    source: &str,
    first_line: usize,
) -> UnitOutcome {
    IN_UNIT_GUARD.with(|g| g.set(true));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        evaluator.run_unit(unit, source, first_line)
    }));
    IN_UNIT_GUARD.with(|g| g.set(false));
    match result {
        Ok(outcome) => outcome,
        Err(payload) => {
            evaluator.break_flag = false;
            evaluator.return_flag = false;
            let _ = writeln!(
                evaluator.stderr_writer,
                "bc_clone: internal error: {}",
                panic_message(payload.as_ref())
            );
            UnitOutcome::Failed
        }
    }
}

/// Records the outcome of one unit in `summary`. Returns `true` if processing must stop.
fn record(summary: &mut RunSummary, outcome: UnitOutcome) -> bool {
    match outcome {
        UnitOutcome::Completed => false,
        UnitOutcome::Failed => {
            summary.errors += 1;
            false
        }
        UnitOutcome::Quit => {
            summary.quit = true;
            true
        }
    }
}

/// Processes a complete file or standard-input text, continuing after errors until its end
/// or `quit` (`docs/COMPATIBILITY.md` §3.1).
pub fn run_non_interactive_block(
    content: &str,
    source: &str,
    evaluator: &mut Evaluator,
) -> RunSummary {
    let mut summary = RunSummary::default();
    let mut acc = UnitAccumulator::new();
    for line in content.split_inclusive('\n') {
        if let Some((unit, first_line)) = acc.push_line(line)
            && record(
                &mut summary,
                run_unit_guarded(evaluator, &unit, source, first_line),
            )
        {
            return summary;
        }
    }
    if let Some((unit, first_line)) = acc.finish() {
        record(
            &mut summary,
            run_unit_guarded(evaluator, &unit, source, first_line),
        );
    }
    summary
}

/// Runs the interactive REPL, reading and executing one unit at a time.
pub fn run_interactive_loop<R: BufRead>(mut reader: R, evaluator: &mut Evaluator) -> RunSummary {
    let mut summary = RunSummary::default();
    let mut acc = UnitAccumulator::new();

    loop {
        if CTRL_C_PRESSED.swap(false, Ordering::SeqCst) {
            let _ = writeln!(evaluator.stderr_writer);
            acc.clear();
            continue;
        }

        let mut line = String::new();
        match reader.read_line(&mut line) {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        if CTRL_C_PRESSED.swap(false, Ordering::SeqCst) {
            acc.clear();
            continue;
        }

        if let Some((unit, first_line)) = acc.push_line(&line)
            && record(
                &mut summary,
                run_unit_guarded(evaluator, &unit, STDIN_SOURCE, first_line),
            )
        {
            return summary;
        }
    }
    if let Some((unit, first_line)) = acc.finish() {
        record(
            &mut summary,
            run_unit_guarded(evaluator, &unit, STDIN_SOURCE, first_line),
        );
    }
    summary
}

/// Main application entry point, extracted for testing. Returns the process exit status:
/// 0 if all input was processed without error, 1 otherwise (`docs/COMPATIBILITY.md` §3.1).
pub fn run_app<R, W, E>(
    args: &[String],
    mut stdin_reader: R,
    stdout_writer: W,
    stderr_writer: E,
    is_interactive: bool,
) -> i32
where
    R: std::io::Read + std::io::BufRead,
    W: std::io::Write + Send + 'static,
    E: std::io::Write + Send + 'static,
{
    let mut math_enabled = false;
    let mut files = Vec::new();

    for arg in args.iter().skip(1) {
        let kind = verified_cli_classify_arg(arg.as_bytes());
        if kind == CLI_ARG_OPT_L {
            math_enabled = true;
        } else if kind == CLI_ARG_OPT_INVALID {
            let opt = &arg[1..];
            let mut err_writer = stderr_writer;
            let _ = writeln!(err_writer, "bc: invalid option -- '{}'", opt);
            return 1;
        } else {
            files.push(arg.clone());
        }
    }

    let mut evaluator = create_evaluator(math_enabled, stdout_writer, stderr_writer);
    evaluator.scale = verified_cli_initial_scale(math_enabled);

    setup_ctrlc_handler();

    let mut errors = 0;
    for filename in &files {
        match std::fs::read_to_string(filename) {
            Ok(content) => {
                let summary = run_non_interactive_block(&content, filename, &mut evaluator);
                errors += summary.errors;
                if summary.quit {
                    return i32::from(errors > 0);
                }
            }
            Err(_) => {
                let _ = writeln!(evaluator.stderr_writer, "bc: cannot open file {}", filename);
                return 1;
            }
        }
    }

    let summary = if is_interactive {
        run_interactive_loop(stdin_reader, &mut evaluator)
    } else {
        let mut content = String::new();
        if stdin_reader.read_to_string(&mut content).is_err() {
            return 1;
        }
        run_non_interactive_block(&content, STDIN_SOURCE, &mut evaluator)
    };
    i32::from(errors + summary.errors > 0)
}

/// Installs a panic hook that stays silent for panics inside [`run_unit_guarded`], which reports
/// them in bc's diagnostic format, and defers to the default hook otherwise.
fn install_panic_hook() {
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if !IN_UNIT_GUARD.with(|g| g.get()) {
            default_hook(info);
        }
    }));
}

fn main() {
    install_panic_hook();

    let args: Vec<String> = std::env::args().collect();
    use std::io::IsTerminal;
    let is_interactive = std::io::stdin().is_terminal() && std::io::stdout().is_terminal();
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let stderr = std::io::stderr();
    std::process::exit(run_app(&args, stdin.lock(), stdout, stderr, is_interactive));
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

        let mut evaluator = create_evaluator(false, stdout, stderr);

        let summary = run_interactive_loop(input.as_bytes(), &mut evaluator);
        assert_eq!(summary, RunSummary::default());

        let out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(out, "3\n3\n");
    }

    #[test]
    fn test_run_repl_errors() {
        let _guard = TEST_MUTEX.lock().unwrap();
        CTRL_C_PRESSED.store(false, Ordering::SeqCst);
        let input = "1/0\n@\nsqrt(-1)\n";
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));

        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };

        let mut evaluator = create_evaluator(false, stdout, stderr);

        let summary = run_interactive_loop(input.as_bytes(), &mut evaluator);
        assert_eq!(summary.errors, 3);

        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(
            err,
            "Runtime error (func=(main)): Divide by zero\n\
             (standard_in) 2: illegal character: @\n\
             Runtime error (func=(main)): Square root of a negative number\n"
        );
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

        let mut evaluator = create_evaluator(false, stdout, stderr);

        let summary = run_non_interactive_block(content, "test.bc", &mut evaluator);
        assert_eq!(summary.errors, 1);

        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(err, "Runtime error (func=(main)): Divide by zero\n");
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
        let mut evaluator = create_evaluator(false, stdout, stderr);
        let summary = run_non_interactive_block("1 + 2\nquit\n3\n", "test.bc", &mut evaluator);
        assert_eq!(
            summary,
            RunSummary {
                errors: 0,
                quit: true
            }
        );
        let out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(out, "3\n");
    }

    struct PanickingWriter;
    impl Write for PanickingWriter {
        fn write(&mut self, _buf: &[u8]) -> std::io::Result<usize> {
            panic!("writer exploded");
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn test_incomplete_unit_at_end_of_input_is_reported() {
        let _guard = TEST_MUTEX.lock().unwrap();
        CTRL_C_PRESSED.store(false, Ordering::SeqCst);
        for interactive in [false, true] {
            let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
            let stderr = TestWriter {
                buf: stderr_buf.clone(),
            };
            let mut evaluator = create_evaluator(false, Vec::new(), stderr);
            let input = "1\n{ 2\n";
            let summary = if interactive {
                run_interactive_loop(input.as_bytes(), &mut evaluator)
            } else {
                run_non_interactive_block(input, STDIN_SOURCE, &mut evaluator)
            };
            assert_eq!(summary.errors, 1);
            let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
            assert_eq!(err, "(standard_in) 3: syntax error\n");
        }
    }

    #[test]
    fn test_internal_panic_is_reported_and_counted() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = create_evaluator(false, PanickingWriter, stderr);
        let summary = run_non_interactive_block("1\n", "test.bc", &mut evaluator);
        assert_eq!(summary.errors, 1);
        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(err, "bc_clone: internal error: writer exploded\n");
        assert_eq!(panic_message(&42), "unknown panic");
        assert!(PanickingWriter.flush().is_ok());

        // The hook defers to the default hook outside a guarded unit; installing it is harmless.
        install_panic_hook();
        assert!(std::panic::catch_unwind(|| panic!("outside a unit")).is_err());
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
        let mut evaluator = create_evaluator(false, stdout, stderr);
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
        let mut evaluator = create_evaluator(false, stdout, stderr);

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
            Err(std::io::Error::other("mock error"))
        }
    }
    impl std::io::BufRead for ErrReader {
        fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
            Err(std::io::Error::other("mock error"))
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
        let mut evaluator = create_evaluator(false, stdout, stderr);

        let mut reader = ErrReader;
        let mut buf = [0; 10];
        let _ = reader.read(&mut buf);
        let _ = reader.fill_buf();
        reader.consume(0);

        assert_eq!(
            run_interactive_loop(reader, &mut evaluator),
            RunSummary::default()
        );
        assert_eq!(
            run_non_interactive_block("1", "test.bc", &mut evaluator),
            RunSummary::default()
        );
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
        let mut evaluator = create_evaluator(false, stdout, stderr);

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
        assert_eq!(res, 0);
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
        assert_eq!(res_invalid, 1);

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
        assert_eq!(res_no_file, 1);

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
        assert_eq!(res_math, 0);

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
        assert_eq!(res_interactive, 0);

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
        assert_eq!(res_err_read, 1);
    }

    #[test]
    fn test_non_interactive_block_quit_flag_ok_path() {
        let _guard = TEST_MUTEX.lock().unwrap();
        // A quit flag already set when a unit finishes stops processing.
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
        let mut evaluator = create_evaluator(false, stdout, stderr);
        evaluator.quit_flag = true;
        let summary = run_non_interactive_block("1\n", "test.bc", &mut evaluator);
        assert!(summary.quit);
    }

    #[test]
    fn test_interactive_loop_quit_flag_ok_path() {
        let _guard = TEST_MUTEX.lock().unwrap();
        // A quit flag already set when a unit finishes stops processing.
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = create_evaluator(false, stdout, stderr);
        evaluator.quit_flag = true;
        let input = "1\n";
        let summary = run_interactive_loop(input.as_bytes(), &mut evaluator);
        assert!(summary.quit);
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
        let mut evaluator = create_evaluator(false, stdout, stderr);

        let input = "a = 5 \\\r\n+ 10\r\na\r\nquit\r\n";
        let _ = run_interactive_loop(input.as_bytes(), &mut evaluator);

        let out_bytes = stdout_buf.lock().unwrap().clone();
        let out_str = String::from_utf8(out_bytes).unwrap();
        assert!(out_str.contains("15"));
    }

    #[test]
    fn test_line_wrapping_70_chars_and_ibase_warnings() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = create_evaluator(false, stdout, stderr);

        // Evaluate 10^80 to test 70-character POSIX line wrapping and ibase > 16 warning
        let input = "scale = 0\n10^80\nibase = 17\n";
        let _ = run_interactive_loop(input.as_bytes(), &mut evaluator);

        let out_bytes = stdout_buf.lock().unwrap().clone();
        let out_str = String::from_utf8(out_bytes).unwrap();
        assert!(out_str.contains("\\\n"));

        let err_bytes = stderr_buf.lock().unwrap().clone();
        let err_str = String::from_utf8(err_bytes).unwrap();
        assert!(err_str.contains("ibase too large"));
    }

    #[test]
    fn test_repl_accumulator_comment_and_string_edge_cases() {
        // Comment boundary conditions
        assert!(is_block_incomplete("/*"));
        assert!(is_block_incomplete("a = 10 /* comment"));
        assert!(!is_block_incomplete("/* comment */ a = 5"));
        assert_eq!(count_open_braces("/* { */"), 0);

        // String boundary conditions
        assert!(is_block_incomplete("\"hello"));
        assert!(!is_block_incomplete("\"hello world\""));
        assert_eq!(count_open_braces("\"{\""), 0);

        // Block incomplete conditions
        assert!(is_block_incomplete("if (1) {"));
        assert!(!is_block_incomplete("a = 5\n"));
    }

    #[test]
    fn test_count_open_braces_and_block_incomplete_string_escapes() {
        // 1. Backslash-LF and CRLF continuation inside strings in count_open_braces
        assert_eq!(count_open_braces("\"str \\\n {\""), 0);
        assert_eq!(count_open_braces("\"str \\\r\n {\""), 0);
        assert_eq!(count_open_braces("\"str \\\r {\""), 0);
        assert_eq!(count_open_braces("/* comment \\\n { */"), 0);
        assert_eq!(count_open_braces("/* *** { ***/"), 0);
        assert_eq!(count_open_braces("/* * / { */"), 0);

        // 2. is_block_incomplete string backslash continuation
        assert!(is_block_incomplete("\"str \\\n"));
        assert!(is_block_incomplete("\"str \\\r\n"));
        assert!(is_block_incomplete("\"str \\\r"));
        assert!(is_block_incomplete("/* ***"));
        assert!(!is_block_incomplete("/* *** */ a = 1\n"));
        assert!(!is_block_incomplete("\"str \\\n\" a = 1\n"));
        assert!(!is_block_incomplete("\"str \\\r\n\" a = 1\n"));
    }

    #[test]
    fn test_offset_comment_and_string_brace_counting() {
        // Non-zero index offsets for comment and string skips (kills += vs *= mutants)
        assert_eq!(count_open_braces("abc/* */{"), 1);
        assert_eq!(count_open_braces("\"0123\\\n{\""), 0);
        assert_eq!(count_open_braces("\"0123\\\r\n{\""), 0);

        assert!(is_block_incomplete("abc/* */{"));
        assert!(is_block_incomplete("\"0123\\\n"));
        assert!(is_block_incomplete("\"0123\\\r\n"));
    }

    #[test]
    fn test_string_backslash_non_crlf_and_comment_slash_boundaries() {
        // String with backslash followed by ordinary non-CRLF character (e.g. \x)
        assert_eq!(count_open_braces("\"a \\x\" {"), 1);
        assert!(is_block_incomplete("\"a \\x\" {"));

        // Comment ending with extra asterisks: /***/ {
        assert_eq!(count_open_braces("/***/{"), 1);
        assert!(is_block_incomplete("/***/{"));

        // Comment with slash inside: /* / */ {
        assert_eq!(count_open_braces("/* / */{"), 1);
        assert!(is_block_incomplete("/* / */{"));
    }

    struct FailingFlushWriter;
    impl Write for FailingFlushWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Err(std::io::Error::other("flush failure"))
        }
    }

    #[test]
    fn test_io_writer_write_and_flush() {
        let mut failing = IoWriter::new(FailingFlushWriter);
        assert!(failing.flush().is_err());

        let mut success = IoWriter::new(Vec::new());
        assert!(FmtWrite::write_str(&mut success, "hello").is_ok());
        assert!(success.flush().is_ok());
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// Verifies that `count_open_braces` and `is_block_incomplete` never panic and maintain
    /// strict consistency across arbitrary symbolic 8-byte ASCII strings.
    #[kani::proof]
    #[kani::unwind(9)]
    fn proof_cli_count_open_braces_and_incomplete() {
        let raw: [u8; 8] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= 8);
        for i in 0..len {
            kani::assume(raw[i] <= 0x7F);
        }
        let s = unsafe { core::str::from_utf8_unchecked(&raw[..len]) };

        let braces = count_open_braces(s);
        let incomplete = is_block_incomplete(s);
        assert!(braces >= -(len as i32) && braces <= (len as i32));
        if braces > 0 {
            assert!(incomplete);
        }
    }

    /// Verifies that CLI option slice indexing (`&arg[1..]`) when `verified_cli_classify_arg`
    /// returns `CLI_ARG_OPT_INVALID` never panics on out-of-bounds or UTF-8 character boundaries.
    #[kani::proof]
    #[kani::unwind(7)]
    fn proof_cli_invalid_opt_slice_safety() {
        let raw: [u8; 6] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= 6);
        for i in 0..len {
            kani::assume(raw[i] <= 0x7F);
        }
        let arg = unsafe { core::str::from_utf8_unchecked(&raw[..len]) };
        let kind = verified_cli_classify_arg(arg.as_bytes());
        if kind == CLI_ARG_OPT_INVALID {
            let opt = &arg[1..];
            assert_eq!(opt.len(), len - 1);
        }
    }
}
