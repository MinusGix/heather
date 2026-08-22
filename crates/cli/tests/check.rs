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
fn a_directory_checks_each_module_as_one_deduplicated_closure() {
    // Both roots import `base`. Loading them as independent files into one
    // elaborator would redeclare it; loading the directory as one closure
    // checks it exactly once and prints one result for the requested target.
    let out = heather(&["check", "stdset"]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "stdset: ok\n");
    assert!(out.stderr.is_empty(), "{}", String::from_utf8_lossy(&out.stderr));
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

// ---------------------------------------------------------------------------
// The declaration cache (docs/cache-v1-design.md). What is pinned here is the
// *surface*: the flag, and the shape of the line it prints. The cache's own
// behaviour is `crates/cache/tests`.

fn cache_dir(tag: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("heather-cli-cache-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    d
}

/// Without the flag, nothing about the run changes — byte for byte. This is
/// the property that keeps the merge gate and `scripts/bench-frontend`
/// measuring what they always measured.
#[test]
fn without_the_flag_the_output_is_unchanged() {
    let out = heather(&["check", "good.hthr"]);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "good.hthr: ok\n");
    assert!(!std::path::Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/.heather"
    ))
    .exists());
}

/// With the flag, the result line says what it trusted — and is never the bare
/// `ok` a full check prints. The Coq `vos` scar, imported deliberately.
#[test]
fn a_cached_run_says_so_and_counts_what_it_trusted() {
    let dir = cache_dir("says-so");
    let arg = dir.display().to_string();

    let cold = heather(&["check", "--cache-dir", &arg, "good.hthr"]);
    assert_eq!(cold.status.code(), Some(0), "{}", String::from_utf8_lossy(&cold.stderr));
    let cold_out = String::from_utf8_lossy(&cold.stdout).to_string();
    assert!(cold_out.starts_with("good.hthr: ok (cache) — "), "{cold_out}");
    assert!(cold_out.contains("0 accepted from cache"), "a cold run trusts nothing: {cold_out}");
    assert_ne!(cold_out, "good.hthr: ok\n", "a cached run must not look like a full one");

    let warm = heather(&["check", "--cache", "--cache-dir", &arg, "good.hthr"]);
    assert_eq!(warm.status.code(), Some(0));
    let warm_out = String::from_utf8_lossy(&warm.stdout).to_string();
    assert!(warm_out.contains("0 declarations kernel-checked"), "{warm_out}");
    assert!(!warm_out.contains("0 accepted from cache"), "{warm_out}");

    let _ = std::fs::remove_dir_all(&dir);
}

/// A cache written by a different kernel is discarded out loud, and the run
/// that follows is a full check that says it checked everything.
#[test]
fn a_stale_cache_is_discarded_out_loud() {
    let dir = cache_dir("stale");
    let arg = dir.display().to_string();
    assert_eq!(heather(&["check", "--cache-dir", &arg, "good.hthr"]).status.code(), Some(0));

    let path = dir.join("entries-v1.tsv");
    let text = std::fs::read_to_string(&path).expect("the cache was written");
    let doctored: String = text
        .lines()
        .map(|l| {
            if l.starts_with("kernel-semantics\t") {
                format!("kernel-semantics\t{}\n", "0".repeat(64))
            } else {
                format!("{l}\n")
            }
        })
        .collect();
    std::fs::write(&path, doctored).unwrap();

    let out = heather(&["check", "--cache-dir", &arg, "good.hthr"]);
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("kernel semantics changed"), "{err}");
    assert!(err.contains("full check"), "{err}");
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("0 accepted from cache"),
        "{}",
        String::from_utf8_lossy(&out.stdout)
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// -- `heather obligations` (docs/obligation-records-design.md §6) ------------

#[test]
fn obligations_lists_state_provenance_and_statement() {
    let out = heather(&["obligations", "obligations.hthr"]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("owner"), "{text}");
    // An omitted repr law is `defaulted` with no provenance…
    assert!(text.contains("datarepr ListTok"), "{text}");
    assert!(text.contains("defaulted"), "{text}");
    // …and a written `refines` is `supplied`, `inline`, with its statement.
    assert!(text.contains("impl length for ListTok"), "{text}");
    assert!(text.contains("supplied"), "{text}");
    assert!(text.contains("inline"), "{text}");
    // The statement is printed in the DESIGNED spelling, which is the point:
    // what the listing prints is what an author can write
    // (docs/repr-access-spellings-design.md §7).
    assert!(text.contains("Impl(length, ListTok)::body(l) = length("), "{text}");
    assert!(!text.contains("Impl_ListTok_length"), "{text}");
}

#[test]
fn obligations_json_is_one_object_per_row() {
    let out = heather(&["obligations", "--json", "obligations.hthr"]);
    assert_eq!(out.status.code(), Some(0));
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.starts_with("[\n"), "{text}");
    assert!(text.trim_end().ends_with("]"), "{text}");
    assert!(text.contains("\"path\": \"Impl(length, ListTok)::refines\""), "{text}");
    assert!(text.contains("\"provenance\": \"inline\""), "{text}");
    assert!(text.contains("\"provenance\": null"), "{text}");
}

/// A `?` is a failure, so there is nothing to list: inline-first means a listed
/// file is a certified file (§6).
#[test]
fn obligations_of_an_unchecked_file_lists_nothing() {
    let out = heather(&["obligations", "obligations_hole.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stdout.is_empty(), "{}", String::from_utf8_lossy(&out.stdout));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("Impl(length, ListTok)::refines"), "{err}");
    assert!(err.contains("nothing to list"), "{err}");
}
