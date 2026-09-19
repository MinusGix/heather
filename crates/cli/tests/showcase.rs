//! The release-CLI half of the showcase gate.
//!
//! A showcase that no test checks is documentation, not a checked artifact,
//! and `docs/showcase/calc_text.hthr` — the largest and most advanced of them
//! — was exactly that until this file existed (`issues/showcase-harness.md`).
//! It cannot join the in-process prefix of
//! `crates/elab/tests/showcase_calculator.rs`: that harness replays semantic
//! images, and this module's image is refused as over budget
//! (`issues/check-only-no-stored-image.md`), so there is nothing to replay and
//! the cost would be a full re-elaboration inside a test process.
//!
//! What runs here instead is the CLI, over the manifest. The dev profile
//! builds the kernel, elaborator and syntax crates at `opt-level = 3`
//! (workspace `Cargo.toml`), so `CARGO_BIN_EXE_heather` checks at
//! release-grade speed and a separate release build is not needed.

use std::path::Path;
use std::process::Command;

use heather_cli::showcase::{self, Tier};

fn root() -> std::path::PathBuf {
    showcase::repo_root()
}

/// One capped `heather check` of a manifest row, returning its output.
fn check(row: &showcase::Showcase) -> (bool, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
    cmd.current_dir(root()).arg("check");
    for dir in &row.search {
        cmd.arg("-L").arg(dir);
    }
    // Width one, as `scripts/test` runs every child: the runner already
    // budgets two CPUs per target, and eight kernel workers underneath that
    // measures contention rather than the check (see CLAUDE.md).
    cmd.env("HEATHER_KERNEL_WORKERS", "1").arg(&row.path);
    let out = cmd.output().expect("run heather check");
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), text)
}

fn check_all(tier: Tier) {
    let rows = showcase::at_tier(tier);
    assert!(!rows.is_empty(), "no showcase at tier {tier:?}; the manifest lost a row");
    for row in &rows {
        let (ok, output) = check(row);
        assert!(ok, "{} did not check:\n{output}", row.path.display());
        assert!(
            output.contains(&format!("{}: ok", row.path.display())),
            "{} checked without the ok line:\n{output}",
            row.path.display()
        );
    }
}

/// Every `.hthr` under `docs/showcase/` declares its tier in the manifest.
///
/// This is the rule that keeps the manifest a source of truth rather than a
/// snapshot: a new showcase file fails here until it says how it is checked,
/// which is the question that went unasked for `calc_text` for a month.
#[test]
fn every_showcase_file_has_a_manifest_row() {
    let dir = root().join("docs/showcase");
    let mut on_disk: Vec<String> = std::fs::read_dir(&dir)
        .expect("read docs/showcase")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("hthr"))
        .map(|p| p.file_stem().expect("stem").to_string_lossy().into_owned())
        .collect();
    on_disk.sort();

    let mut in_manifest: Vec<String> = showcase::manifest().iter().map(|s| s.name.clone()).collect();
    in_manifest.sort();

    let missing: Vec<&String> = on_disk.iter().filter(|n| !in_manifest.contains(n)).collect();
    let phantom: Vec<&String> = in_manifest.iter().filter(|n| !on_disk.contains(n)).collect();
    assert!(
        missing.is_empty() && phantom.is_empty(),
        "docs/showcase/showcases.tsv is out of step with the directory:\n  \
         no row for: {missing:?}\n  row without a file: {phantom:?}"
    );
}

/// The manifest's `-L` sets are claims about the loader, so check they parse
/// as directories that exist. A wrong one otherwise surfaces as a confusing
/// "cannot find module" the first time someone runs that row.
#[test]
fn every_search_directory_exists_and_is_not_the_showcase_directory() {
    let root = root();
    for row in showcase::manifest() {
        assert!(
            root.join(&row.path).is_file(),
            "{}: the manifest names a file that does not exist",
            row.name
        );
        for dir in &row.search {
            assert!(
                root.join(dir).is_dir(),
                "{}: `-L {}` is not a directory",
                row.name,
                dir.display()
            );
            assert_ne!(
                dir.as_path(),
                Path::new("docs/showcase"),
                "{}: `-L docs/showcase` puts this directory's `parser_core` against \
                 `lib/std/parser`'s, which the loader refuses as an ambiguity rather than \
                 resolving by precedence. The importing file's own directory is already \
                 searched first, so a sibling import needs no `-L` at all.",
                row.name
            );
        }
    }
}

/// The cheap CLI tier: the checked-in generator outputs, which nothing
/// regenerates, so the gate is that they still check.
#[test]
fn cli_tier_showcases_check() {
    check_all(Tier::Cli);
}

// The `cli-slow` tier — `docs/showcase/calc_text.hthr` — is deliberately *not*
// a test here. Measured at width one on 2026-09-19: 343 s wall, 334 CPU-s,
// 9.8 GiB peak. The test runner's per-child rails are 300 CPU-s and 6 GiB
// (`LIMIT_KIB`/`CPU_RAIL_SECONDS` in scripts/run-test-targets.mjs), so it
// would be SIGKILLed on both, and raising a rail for one target would hand
// every other target the same licence on a box whose parallelism is planned
// against a 3 GiB working set. It is gated by `showcase_gate` in scripts/test
// instead: serial, full lane only, with rails sized for this one file.
// issues/showcase-harness.md records the measurement.
