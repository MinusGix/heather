//! `--kernel-workers` and `HEATHER_KERNEL_WORKERS` on the primary command
//! (`docs/parallel-kernel-gate-design.md` §4).
//!
//! A subprocess is what carries an environment variable here: a test binary
//! that mutated its own would be racing every other test in it.

use std::process::{Command, Output};

fn fixtures() -> std::path::PathBuf {
    std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures"))
}

fn heather(args: &[&str], env: Option<(&str, &str)>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_heather"));
    command.current_dir(fixtures()).args(args);
    match env {
        Some((k, v)) => command.env(k, v),
        // Inherited on purpose otherwise, so a developer running the suite
        // with the variable set does not silently test a different width than
        // the one this case names.
        None => command.env_remove("HEATHER_KERNEL_WORKERS"),
    };
    command.output().expect("run heather")
}

fn assert_code(result: &Output, code: i32, what: &str) {
    assert_eq!(
        result.status.code(),
        Some(code),
        "{what}\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr),
    );
}

/// A good module checks the same at every width. The deferred gate is a
/// scheduling decision; the verdict is not.
#[test]
fn a_good_module_checks_at_every_width() {
    for width in ["1", "2", "4", "8"] {
        let result = heather(&["check", "--kernel-workers", width, "good.hthr"], None);
        assert_code(&result, 0, &format!("--kernel-workers {width} refused a good module"));
    }
}

/// And a bad one is refused at every width, naming the same declaration.
#[test]
fn a_bad_module_is_refused_at_every_width() {
    for width in ["1", "4"] {
        let result = heather(&["check", "--kernel-workers", width, "bad.hthr"], None);
        assert_code(&result, 1, &format!("--kernel-workers {width} accepted a bad module"));
    }
}

/// The environment names the width when no flag does.
#[test]
fn the_environment_names_the_width() {
    let result = heather(&["check", "good.hthr"], Some(("HEATHER_KERNEL_WORKERS", "4")));
    assert_code(&result, 0, "HEATHER_KERNEL_WORKERS=4 refused a good module");
    // Nonsense is ignored rather than refused: a measurement knob must never
    // be the reason a check fails.
    let result = heather(&["check", "good.hthr"], Some(("HEATHER_KERNEL_WORKERS", "lots")));
    assert_code(&result, 0, "an unparseable width is ignored");
}

/// A width of zero is a usage error, not a silent reinterpretation.
#[test]
fn a_zero_width_is_a_usage_error() {
    let result = heather(&["check", "--kernel-workers", "0", "good.hthr"], None);
    assert_code(&result, 2, "`--kernel-workers 0` should be refused");
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("positive integer"),
        "stderr: {}",
        String::from_utf8_lossy(&result.stderr),
    );
}
