// SPDX-License-Identifier: MIT

//! CLI entry point, POSIX option parsing, and REPL runner for the bc clone.
//!
//! Handles manual option checking, standard TTY/non-TTY execution paths,
//! Ctrl+C handlers, and mockable I/O streams for 100% automated test coverage.

use core::fmt::Write as FmtWrite;
use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

#[cfg(any(test, kani))]
use bc_core::verified_kernels::verified_repl_block_completeness;
use bc_core::verified_kernels::{
    CLI_ARG_END_OF_OPTIONS, CLI_ARG_FILE, CLI_ARG_OPT_CLUSTER, CLI_PARSE_ERROR, CLI_PARSE_VERSION,
    CLI_POLICY_REJECT, CLI_POLICY_WARN, verified_cli_classify_arg,
    verified_cli_classify_option_char, verified_cli_initial_scale, verified_cli_parse_options,
};
use bc_core::{
    BcWriter, DEFAULT_MAX_DEPTH, Evaluator, ExtensionPolicy, RunSummary, STDIN_SOURCE, SourceUnits,
    UnitAccumulator, UnitOutcome,
};

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
    fn write_bytes(&mut self, b: &[u8]) -> core::fmt::Result {
        self.inner.write_all(b).map_err(|_| core::fmt::Error)
    }

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
#[cfg(any(test, kani))]
pub fn count_open_braces(text: &[u8]) -> i32 {
    verified_repl_block_completeness(text).0
}

/// Checks if the block is incomplete (e.g. has open braces, or is inside an unterminated comment or string).
#[cfg(any(test, kani))]
pub fn is_block_incomplete(text: &[u8]) -> bool {
    verified_repl_block_completeness(text).1
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

/// Runs one input unit with `run`. `bc_core` reports every bc error through `Result`, so a
/// panic here is an internal bug; it is reported as such and counted as a failed unit instead of
/// aborting.
fn run_unit_guarded<T>(
    evaluator: &mut Evaluator,
    run: impl FnOnce(&mut Evaluator) -> T,
    failed: T,
) -> T {
    IN_UNIT_GUARD.with(|g| g.set(true));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(evaluator)));
    IN_UNIT_GUARD.with(|g| g.set(false));
    match result {
        Ok(outcome) => outcome,
        Err(payload) => {
            evaluator.reset_control_flags();
            let _ = writeln!(
                evaluator.stderr_writer(),
                "bc_clone: internal error: {}",
                panic_message(payload.as_ref())
            );
            failed
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
/// or `quit` (`docs/COMPATIBILITY.md` §3.1). Each unit is run by the proved
/// `Evaluator::run_next_unit`, the step of `Evaluator::run_source`, guarded on its own.
pub fn run_non_interactive_block(
    content: Vec<u8>,
    source: &str,
    evaluator: &mut Evaluator,
) -> RunSummary {
    let mut summary = RunSummary::default();
    let mut units = SourceUnits::new(content);
    while let Some(outcome) = run_unit_guarded(
        evaluator,
        |ev| ev.run_next_unit(&mut units, source),
        Some(UnitOutcome::Failed),
    ) {
        if record(&mut summary, outcome) {
            break;
        }
    }
    summary
}

/// Runs the interactive REPL, reading and executing one unit at a time.
pub fn run_interactive_loop<R: BufRead>(mut reader: R, evaluator: &mut Evaluator) -> RunSummary {
    let mut summary = RunSummary::default();
    let mut acc = UnitAccumulator::new();

    loop {
        if CTRL_C_PRESSED.swap(false, Ordering::SeqCst) {
            let _ = writeln!(evaluator.stderr_writer());
            acc.clear();
            continue;
        }

        let mut bytes = Vec::new();
        match reader.read_until(b'\n', &mut bytes) {
            Ok(0) | Err(_) => break,
            Ok(_) => {}
        }
        if CTRL_C_PRESSED.swap(false, Ordering::SeqCst) {
            acc.clear();
            continue;
        }

        if let Some((unit, first_line)) = acc.push_line(&bytes)
            && record(
                &mut summary,
                run_unit_guarded(
                    evaluator,
                    |ev| ev.run_unit(&unit, STDIN_SOURCE, first_line),
                    UnitOutcome::Failed,
                ),
            )
        {
            return summary;
        }
    }
    if let Some((unit, first_line)) = acc.finish() {
        record(
            &mut summary,
            run_unit_guarded(
                evaluator,
                |ev| ev.run_unit(&unit, STDIN_SOURCE, first_line),
                UnitOutcome::Failed,
            ),
        );
    }
    summary
}

/// Where an entry of the classified command line came from (`run_app`).
enum ArgSource<'a> {
    /// An option letter of a group such as `-ls`.
    Letter(char),
    /// A whole argument: a file, `--`, or a long option.
    Arg(&'a String),
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
    // Classify the arguments: one entry of `kinds` per option letter and per other argument,
    // with the text it came from in `sources` for the diagnostics and the file names. The
    // verified `verified_cli_parse_options` then reads the options from left to right.
    let mut kinds = Vec::new();
    let mut sources = Vec::new();
    let mut options_ended = false;
    for arg in args.iter().skip(1) {
        let kind = verified_cli_classify_arg(arg.as_bytes(), options_ended);
        if kind == CLI_ARG_OPT_CLUSTER {
            for c in arg.chars().skip(1) {
                kinds.push(verified_cli_classify_option_char(u32::from(c)));
                sources.push(ArgSource::Letter(c));
            }
        } else {
            if kind == CLI_ARG_END_OF_OPTIONS {
                options_ended = true;
            }
            kinds.push(kind);
            sources.push(ArgSource::Arg(arg));
        }
    }
    let (outcome, stop, math_enabled, policy) = verified_cli_parse_options(&kinds);
    if outcome == CLI_PARSE_ERROR {
        let mut err_writer = stderr_writer;
        let _ = match sources.get(stop) {
            Some(ArgSource::Letter(c)) => writeln!(err_writer, "bc: invalid option -- '{}'", c),
            Some(ArgSource::Arg(arg)) => writeln!(err_writer, "bc: unrecognized option '{}'", arg),
            None => Ok(()),
        };
        return 1;
    }
    if outcome == CLI_PARSE_VERSION {
        let mut out_writer = stdout_writer;
        return if writeln!(out_writer, "{}", bc_build_info::VERSION_LINE)
            .and_then(|()| out_writer.flush())
            .is_ok()
        {
            0
        } else {
            1
        };
    }
    let extension_policy = if policy == CLI_POLICY_REJECT {
        ExtensionPolicy::Reject
    } else if policy == CLI_POLICY_WARN {
        ExtensionPolicy::Warn
    } else {
        ExtensionPolicy::Allow
    };
    let files: Vec<&String> = kinds
        .iter()
        .zip(&sources)
        .filter_map(|(&kind, source)| match source {
            ArgSource::Arg(arg) if kind == CLI_ARG_FILE => Some(*arg),
            _ => None,
        })
        .collect();
    let mut evaluator = create_evaluator(math_enabled, stdout_writer, stderr_writer);
    evaluator.max_depth = MAX_DEPTH.load(Ordering::SeqCst);
    evaluator.max_eval_depth = MAX_EVAL_DEPTH.load(Ordering::SeqCst);
    evaluator.set_scale(verified_cli_initial_scale(math_enabled));
    evaluator.extension_policy = extension_policy;

    setup_ctrlc_handler();

    let mut errors = 0;
    for filename in files {
        match std::fs::read(filename) {
            Ok(bytes) => {
                let summary = run_non_interactive_block(bytes, filename, &mut evaluator);
                errors += summary.errors;
                if summary.quit {
                    return i32::from(errors > 0);
                }
            }
            Err(_) => {
                let _ = writeln!(
                    evaluator.stderr_writer(),
                    "bc: cannot open file {}",
                    filename
                );
                return 1;
            }
        }
    }

    let summary = if is_interactive {
        run_interactive_loop(stdin_reader, &mut evaluator)
    } else {
        let mut bytes = Vec::new();
        if let Err(e) = stdin_reader.read_to_end(&mut bytes) {
            let _ = writeln!(
                evaluator.stderr_writer(),
                "bc: cannot read standard input: {}",
                e
            );
            return 1;
        }
        run_non_interactive_block(bytes, STDIN_SOURCE, &mut evaluator)
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

/// Stack reserved for the thread that parses and evaluates the input. Only the pages actually
/// used are committed.
const ENGINE_STACK_SIZE: usize = 512 << 20;

/// Nesting limit on that stack (`docs/COMPATIBILITY.md` §2). One level takes at most about
/// 1.9 KB of stack in release builds and 16 KB in debug builds (measured on x86-64), so the
/// limit uses less than 40% (release) or 65% (debug) of `ENGINE_STACK_SIZE`.
const ENGINE_MAX_DEPTH: usize = if cfg!(debug_assertions) {
    20_000
} else {
    100_000
};

/// Nesting limit that [`run_app`] gives its evaluator: [`DEFAULT_MAX_DEPTH`] unless the input
/// runs on the large engine thread.
static MAX_DEPTH: AtomicUsize = AtomicUsize::new(DEFAULT_MAX_DEPTH);

/// Nesting limit of evaluation (`docs/COMPATIBILITY.md` §2). Evaluation runs on the heap, so it
/// does not depend on the thread's stack; it bounds the memory of runaway recursion.
const ENGINE_MAX_EVAL_DEPTH: usize = 2_000_000;

/// Evaluation limit that [`run_app`] gives its evaluator.
static MAX_EVAL_DEPTH: AtomicUsize = AtomicUsize::new(ENGINE_MAX_EVAL_DEPTH);

/// Runs [`run_app`] on the process's standard streams.
fn run_on_stdio(args: &[String], is_interactive: bool) -> i32 {
    let stdin = std::io::stdin();
    run_app(
        args,
        stdin.lock(),
        std::io::stdout(),
        std::io::stderr(),
        is_interactive,
    )
}

fn main() {
    install_panic_hook();

    let args: Vec<String> = std::env::args().collect();
    use std::io::IsTerminal;
    let is_interactive = std::io::stdin().is_terminal() && std::io::stdout().is_terminal();
    MAX_DEPTH.store(ENGINE_MAX_DEPTH, Ordering::SeqCst);
    let engine_args = args.clone();
    let status = match std::thread::Builder::new()
        .name(String::from("bc"))
        .stack_size(ENGINE_STACK_SIZE)
        .spawn(move || run_on_stdio(&engine_args, is_interactive))
    {
        Ok(engine) => engine.join().unwrap_or(1),
        Err(_) => {
            // The large stack could not be reserved: run on this thread's default stack.
            MAX_DEPTH.store(DEFAULT_MAX_DEPTH, Ordering::SeqCst);
            run_on_stdio(&args, is_interactive)
        }
    };
    std::process::exit(status);
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
        assert_eq!(count_open_braces(b""), 0);
        assert_eq!(count_open_braces(b"{"), 1);
        assert_eq!(count_open_braces(b"}"), -1);
        assert_eq!(count_open_braces(b"/* { */"), 0);
        assert_eq!(count_open_braces(b"\"{\""), 0);
        assert_eq!(count_open_braces(b"a = 5 \\\n {"), 1);
        assert_eq!(count_open_braces(b"a = 5 \\\r\n {"), 1);
        assert_eq!(count_open_braces(b"a = \"hello \\\nworld\""), 0);
        assert_eq!(count_open_braces(b"a = \"hello \\\r\nworld\""), 0);
    }

    #[test]
    fn test_count_open_braces_and_block_incomplete_boundary_cases() {
        assert_eq!(count_open_braces(b"/* { */ { }"), 0);
        assert_eq!(count_open_braces(b"if (1) { a = 1; }"), 0);
        assert_eq!(count_open_braces(b"if (1) {\n  if (2) {\n    a = 1;\n"), 2);
        assert_eq!(count_open_braces(b"a = \"{\"\n"), 0);
        assert_eq!(count_open_braces(b"/* comment * { */ { }"), 0);

        assert!(is_block_incomplete(b"if (1) {"));
        assert!(is_block_incomplete(b"/* comment"));
        assert!(is_block_incomplete(b"\"string"));
        assert!(!is_block_incomplete(b"a = 1 + 2\n"));
        assert!(!is_block_incomplete(b"/* comment */ a = 1\n"));
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

        let summary =
            run_non_interactive_block(content.as_bytes().to_vec(), "test.bc", &mut evaluator);
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
        let summary =
            run_non_interactive_block(b"1 + 2\nquit\n3\n".to_vec(), "test.bc", &mut evaluator);
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

    /// Panics on the write of `2`.
    struct PanicOnTwo(std::sync::Arc<std::sync::Mutex<Vec<u8>>>);
    impl Write for PanicOnTwo {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            assert!(!buf.starts_with(b"2"), "writer exploded");
            self.0.lock().unwrap().write(buf)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn test_internal_panic_skips_only_its_own_unit() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = create_evaluator(false, PanicOnTwo(stdout_buf.clone()), stderr);
        let summary = run_non_interactive_block(b"1\n2\n3\n".to_vec(), "test.bc", &mut evaluator);
        assert_eq!(summary.errors, 1);
        assert!(!summary.quit);
        assert_eq!(stdout_buf.lock().unwrap().as_slice(), b"1\n3\n");
        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(err, "bc_clone: internal error: writer exploded\n");
    }

    #[test]
    fn test_quit_in_a_file_after_an_error_exits_with_status_1() {
        let _guard = TEST_MUTEX.lock().unwrap();
        CTRL_C_PRESSED.store(false, Ordering::SeqCst);
        let path = std::env::temp_dir().join(format!("bc_clone_quit_{}.bc", std::process::id()));
        std::fs::write(&path, "1/0\nquit\n").unwrap();
        let args = ["bc".to_string(), path.to_str().unwrap().to_string()];
        let status = run_app(&args, "2\n".as_bytes(), Vec::new(), Vec::new(), false);
        let clean = ["bc".to_string(), path.to_str().unwrap().to_string()];
        std::fs::write(&path, "1\nquit\n").unwrap();
        let clean_status = run_app(&clean, "2\n".as_bytes(), Vec::new(), Vec::new(), false);
        let _ = std::fs::remove_file(&path);
        assert_eq!((status, clean_status), (1, 0));
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
                run_non_interactive_block(input.as_bytes().to_vec(), STDIN_SOURCE, &mut evaluator)
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
        let summary = run_non_interactive_block(b"1\n".to_vec(), "test.bc", &mut evaluator);
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
            run_non_interactive_block(b"1".to_vec(), "test.bc", &mut evaluator),
            RunSummary::default()
        );
    }

    #[test]
    fn test_is_block_incomplete() {
        assert!(!is_block_incomplete(b"a = 5"));
        assert!(is_block_incomplete(b"/* comment"));
        assert!(is_block_incomplete(b"\"string"));
        assert!(!is_block_incomplete(b"a = \"hello \\\nworld\""));
        assert!(!is_block_incomplete(b"a = \"hello \\\r\nworld\""));
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
    fn test_option_syntax_follows_xbd_12_2() {
        let _guard = TEST_MUTEX.lock().unwrap();
        let file = std::env::temp_dir().join(format!("bc_clone_opts_{}.bc", std::process::id()));
        std::fs::write(&file, "a = 7\n").unwrap();
        let file_name = file.to_string_lossy().into_owned();
        let run = |args: &[&str], stdin: &str| {
            let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
            let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
            let mut argv = vec!["bc".to_string()];
            argv.extend(args.iter().map(|a| a.to_string()));
            let status = run_app(
                &argv,
                stdin.as_bytes(),
                TestWriter {
                    buf: stdout_buf.clone(),
                },
                TestWriter {
                    buf: stderr_buf.clone(),
                },
                false,
            );
            let out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
            let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
            (status, out, err)
        };

        // Grouped options (Guideline 5), in any order, and repeated letters.
        for group in ["-ls", "-sl", "-lw", "-ll"] {
            assert_eq!(
                run(&[group], "scale\n"),
                (0, "20\n".to_string(), String::new())
            );
        }
        // "--" ends the options (Guideline 10): a later "-l" is a file operand.
        assert_eq!(
            run(&["-l", "--", &file_name], "a\nscale\n"),
            (0, "7\n20\n".to_string(), String::new())
        );
        assert_eq!(
            run(&["--", "-l"], ""),
            (1, String::new(), "bc: cannot open file -l\n".to_string())
        );
        // "-" is an operand, not an option.
        assert_eq!(
            run(&["-"], ""),
            (1, String::new(), "bc: cannot open file -\n".to_string())
        );
        // The first invalid letter of a group is reported.
        assert_eq!(
            run(&["-lzq"], ""),
            (1, String::new(), "bc: invalid option -- 'z'\n".to_string())
        );
        assert_eq!(
            run(&["--mathlib"], ""),
            (
                1,
                String::new(),
                "bc: unrecognized option '--mathlib'\n".to_string()
            )
        );

        // `-v` and `--version` display the version and read nothing else: neither the files
        // nor standard input. Options are read from left to right, so an invalid option before
        // them is reported and anything after them is not read.
        let version = (
            0,
            format!("{}\n", bc_build_info::VERSION_LINE),
            String::new(),
        );
        for args in [
            &["-v"][..],
            &["--version"],
            &["-lv"],
            &["-s", "-v"],
            &["-v", "-z"],
            &["-v", "--mathlib"],
            &[&file_name, "-v"],
            &["-v", "/nonexistent/file.bc"],
        ] {
            assert_eq!(run(args, "1\n"), version, "{args:?}");
        }
        assert_eq!(
            run(&["-zv"], "1\n"),
            (1, String::new(), "bc: invalid option -- 'z'\n".to_string())
        );
        assert_eq!(
            run(&["--versio", "-v"], ""),
            (
                1,
                String::new(),
                "bc: unrecognized option '--versio'\n".to_string()
            )
        );
        // After "--", `-v` is a file operand.
        assert_eq!(
            run(&["--", "-v"], ""),
            (1, String::new(), "bc: cannot open file -v\n".to_string())
        );
        // `-s` rejects extensions of the language, not this option.
        assert_eq!(run(&["-sw", "--version"], ""), version);
        std::fs::remove_file(&file).unwrap();
    }

    #[test]
    fn test_invalid_utf8_input_is_read_as_bytes() {
        let _guard = TEST_MUTEX.lock().unwrap();
        CTRL_C_PRESSED.store(false, Ordering::SeqCst);
        // An invalid byte outside a string is an illegal character; inside a string it is printed
        // unchanged.
        let input: &[u8] = b"1\n\xff\n\"a\xffb\"\n2\n";
        let file =
            std::env::temp_dir().join(format!("bc_clone_invalid_utf8_{}.bc", std::process::id()));
        std::fs::write(&file, input).unwrap();
        let file_name = file.to_string_lossy().into_owned();

        let cases: [(Vec<String>, &[u8], bool, String); 3] = [
            (
                vec!["bc".to_string()],
                input,
                false,
                "(standard_in)".to_string(),
            ),
            (
                vec!["bc".to_string()],
                input,
                true,
                "(standard_in)".to_string(),
            ),
            (
                vec!["bc".to_string(), file_name.clone()],
                b"",
                false,
                file_name.clone(),
            ),
        ];
        for (args, stdin, interactive, source) in cases {
            let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
            let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
            let status = run_app(
                &args,
                stdin,
                TestWriter {
                    buf: stdout_buf.clone(),
                },
                TestWriter {
                    buf: stderr_buf.clone(),
                },
                interactive,
            );
            assert_eq!(status, 1);
            assert_eq!(*stdout_buf.lock().unwrap(), b"1\na\xffb2\n");
            let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
            // Under `cfg(test)`, `setup_ctrlc_handler` simulates one Ctrl-C, which the REPL
            // acknowledges with a newline.
            let ctrlc_echo = if interactive { "\n" } else { "" };
            assert_eq!(
                err,
                format!("{ctrlc_echo}{source} 2: illegal character: \\377\n")
            );
        }
        std::fs::remove_file(&file).unwrap();
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
        evaluator.request_quit();
        let summary = run_non_interactive_block(b"1\n".to_vec(), "test.bc", &mut evaluator);
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
        evaluator.request_quit();
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
        // `run_interactive_loop` consumes `CTRL_C_PRESSED`, which other tests set.
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
        assert!(is_block_incomplete(b"/*"));
        assert!(is_block_incomplete(b"a = 10 /* comment"));
        assert!(!is_block_incomplete(b"/* comment */ a = 5"));
        assert_eq!(count_open_braces(b"/* { */"), 0);

        // String boundary conditions
        assert!(is_block_incomplete(b"\"hello"));
        assert!(!is_block_incomplete(b"\"hello world\""));
        assert_eq!(count_open_braces(b"\"{\""), 0);

        // Block incomplete conditions
        assert!(is_block_incomplete(b"if (1) {"));
        assert!(!is_block_incomplete(b"a = 5\n"));
    }

    #[test]
    fn test_count_open_braces_and_block_incomplete_string_escapes() {
        // 1. Backslash-LF and CRLF continuation inside strings in count_open_braces
        assert_eq!(count_open_braces(b"\"str \\\n {\""), 0);
        assert_eq!(count_open_braces(b"\"str \\\r\n {\""), 0);
        assert_eq!(count_open_braces(b"\"str \\\r {\""), 0);
        assert_eq!(count_open_braces(b"/* comment \\\n { */"), 0);
        assert_eq!(count_open_braces(b"/* *** { ***/"), 0);
        assert_eq!(count_open_braces(b"/* * / { */"), 0);

        // 2. is_block_incomplete string backslash continuation
        assert!(is_block_incomplete(b"\"str \\\n"));
        assert!(is_block_incomplete(b"\"str \\\r\n"));
        assert!(is_block_incomplete(b"\"str \\\r"));
        assert!(is_block_incomplete(b"/* ***"));
        assert!(!is_block_incomplete(b"/* *** */ a = 1\n"));
        assert!(!is_block_incomplete(b"\"str \\\n\" a = 1\n"));
        assert!(!is_block_incomplete(b"\"str \\\r\n\" a = 1\n"));
    }

    #[test]
    fn test_offset_comment_and_string_brace_counting() {
        // Non-zero index offsets for comment and string skips (kills += vs *= mutants)
        assert_eq!(count_open_braces(b"abc/* */{"), 1);
        assert_eq!(count_open_braces(b"\"0123\\\n{\""), 0);
        assert_eq!(count_open_braces(b"\"0123\\\r\n{\""), 0);

        assert!(is_block_incomplete(b"abc/* */{"));
        assert!(is_block_incomplete(b"\"0123\\\n"));
        assert!(is_block_incomplete(b"\"0123\\\r\n"));
    }

    #[test]
    fn test_string_backslash_non_crlf_and_comment_slash_boundaries() {
        // String with backslash followed by ordinary non-CRLF character (e.g. \x)
        assert_eq!(count_open_braces(b"\"a \\x\" {"), 1);
        assert!(is_block_incomplete(b"\"a \\x\" {"));

        // Comment ending with extra asterisks: /***/ {
        assert_eq!(count_open_braces(b"/***/{"), 1);
        assert!(is_block_incomplete(b"/***/{"));

        // Comment with slash inside: /* / */ {
        assert_eq!(count_open_braces(b"/* / */{"), 1);
        assert!(is_block_incomplete(b"/* / */{"));
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
        assert!(BcWriter::write_bytes(&mut success, b" \xff").is_ok());
        assert!(success.flush().is_ok());
        assert_eq!(success.inner, b"hello \xff");
    }

    #[test]
    fn test_version_that_cannot_be_written_exits_with_status_1() {
        let args = ["bc".to_string(), "-v".to_string()];
        assert_eq!(
            run_app(&args, &b""[..], FailingFlushWriter, Vec::new(), false),
            1
        );
        assert_eq!(run_app(&args, &b""[..], Vec::new(), Vec::new(), false), 0);
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// Verifies that `count_open_braces` and `is_block_incomplete` never panic and maintain
    /// strict consistency across arbitrary symbolic byte strings of up to 8 bytes.
    #[kani::proof]
    #[kani::unwind(9)]
    fn proof_cli_count_open_braces_and_incomplete() {
        let raw: [u8; 8] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= 8);
        let s = &raw[..len];

        let braces = count_open_braces(s);
        let incomplete = is_block_incomplete(s);
        assert!(braces >= -(len as i32) && braces <= (len as i32));
        if braces > 0 {
            assert!(incomplete);
        }
    }
}
