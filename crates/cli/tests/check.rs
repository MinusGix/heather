//! Drive the built `heather` binary over the fixture files: exit codes,
//! stream discipline (diagnostics on stderr, ok-lines on stdout), and the
//! diagnostic shapes the elab-side tests pin in detail.

use std::process::{Command, Output};

fn heather(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures"))
        .args(args)
        .output()
        .expect("run heather")
}

#[test]
fn good_file_is_ok_exit_zero() {
    let out = heather(&["check", "good.hthr"]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "good.hthr: ok\n");
    assert!(out.stderr.is_empty(), "{}", String::from_utf8_lossy(&out.stderr));
}

#[test]
fn bad_file_prints_all_diagnostics_exit_one() {
    let out = heather(&["check", "bad.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stdout.is_empty(), "{}", String::from_utf8_lossy(&out.stdout));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("error: the kernel rejected `broken`"), "{err}");
    assert!(err.contains("--> bad.hthr:3:1"), "{err}");
    assert!(err.contains("unsolved goals in `open_goal`"), "{err}");
    assert!(err.contains("bad.hthr: 2 errors"), "{err}");
}

#[test]
fn several_files_check_independently() {
    // The bad file must not stop the good one from being checked, and the
    // good one must not mask the failing exit code.
    let out = heather(&["check", "bad.hthr", "good.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "good.hthr: ok\n");
}

#[test]
fn missing_file_is_a_run_failure() {
    let out = heather(&["check", "no-such.hthr"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("cannot read"), "");
}

#[test]
fn usage_errors_exit_two() {
    for args in [&[][..], &["check"][..], &["frobnicate", "good.hthr"][..]] {
        let out = heather(args);
        assert_eq!(out.status.code(), Some(2), "args: {args:?}");
        assert!(String::from_utf8_lossy(&out.stderr).contains("usage:"), "args: {args:?}");
    }
}
