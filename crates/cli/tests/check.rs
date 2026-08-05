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

// ---------------------------------------------------------------------------
// Modules (docs/modules-design.md §3): the loader — search paths, dedup,
// cycles — and multi-file diagnostics. The *name regime* is tested at the
// elaborator (crates/elab/tests/modules.rs); what only the CLI can test is
// the walk over the file system.

#[test]
fn a_root_checks_its_imports_and_reports_only_itself() {
    // `helper.hthr` sits beside `root.hthr`, which is the first place an
    // import is looked for. One ok-line: the closure is one check.
    let out = heather(&["check", "root.hthr"]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "root.hthr: ok\n");
}

#[test]
fn an_import_cycle_is_an_error_that_prints_the_cycle() {
    let out = heather(&["check", "cyc_a.hthr"]);
    assert_eq!(out.status.code(), Some(2));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("import cycle"), "{err}");
    assert!(err.contains("cyc_a -> cyc_b -> cyc_a"), "the cycle itself must be printed: {err}");
}

#[test]
fn a_search_directory_resolves_an_import() {
    let out = heather(&["check", "-L", "ldir", "uses_shared.hthr"]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "uses_shared.hthr: ok\n");
}

#[test]
fn an_unresolvable_import_is_a_run_failure() {
    // The negative control for the search path: without `-L` the same file
    // cannot find its module at all.
    let out = heather(&["check", "uses_shared.hthr"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("cannot find module `shared`"));
}

#[test]
fn a_module_in_two_search_directories_is_an_error_not_a_precedence() {
    let out = heather(&["check", "-L", "ldir", "-L", "ldir2", "uses_shared.hthr"]);
    assert_eq!(out.status.code(), Some(2));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("two search directories"), "{err}");
}

#[test]
fn an_error_in_an_imported_module_is_reported_against_that_file() {
    let out = heather(&["check", "uses_broken.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("broken_dep.hthr"), "the failing file must be named: {err}");
    assert!(!err.contains("uses_broken.hthr:"), "the importer did not fail: {err}");
    // …and the importer is not reported as ok either, since its closure did
    // not check.
    assert!(out.stdout.is_empty(), "{}", String::from_utf8_lossy(&out.stdout));
}
