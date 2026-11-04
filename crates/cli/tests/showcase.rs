//! The release-CLI half of the showcase gate.
//!
//! A showcase that no test checks is documentation, not a checked artifact,
//! and `docs/showcase/calc_text.hthr` — the largest and most advanced of them
//! — was exactly that until this file existed (`issues/showcase-harness.md`).
//!
//! What runs here is the CLI, over the manifest. The dev profile
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
    cmd.env("HEATHER_KERNEL_WORKERS", "1");
    // Through the semantic session, like the native certificates: a run at
    // an unchanged compiler replays the row's image (its kernel verdicts
    // vouched for by the store), and a changed compiler or source checks
    // from source again. One store for every row and for the whole-library
    // gate (`tests/library.rs`), which share the library prefix: rows run
    // side by side, and the store's single-flight build makes a second
    // asker wait for the first's image rather than elaborate it again. The
    // fast lane's trade (`HEATHER_SEMANTIC_IMAGES=accept-stale`, set by
    // scripts/test) replays an image an earlier build wrote, as
    // crates/elab/tests/support does.
    cmd.arg("--cache").arg("--cache-dir").arg(showcase::cli_check_images());
    // Every library module is keyed by its own closure
    // (`docs/module-dag-design.md`), so the row's closure replays the gate's
    // images and only the row's own module is elaborated.
    if std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() == Ok("accept-stale") {
        cmd.arg("--accept-stale-images");
    }
    cmd.arg(&row.path);
    let out = cmd.output().expect("run heather check");
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), text)
}

/// The CLI tier's rows, one test each (below) so libtest checks them side by
/// side: as one loop they were the fast lane's critical path.
/// [`cli_tier_rows_each_have_a_test`] keeps this list and the manifest equal,
/// so a new CLI row fails until it has its own test.
const CLI_ROWS: &[&str] = &["calc_text", "contextual_rewrite_generated", "relational_generator_generated",
    "result_parser", "relational_contexts", "rat_client", "creal_client", "ordered_field_client", "semiring_client",
    "itree_client", "itree_refinement_client", "memory_client"];

fn check_row(name: &str) {
    check_row_at(Tier::Cli, name);
}

fn check_row_at(tier: Tier, name: &str) {
    let rows = showcase::at_tier(tier);
    let row = rows.iter().find(|r| r.name == name)
        .unwrap_or_else(|| panic!("no {tier:?}-tier showcase `{name}`; the manifest lost a row"));
    let (ok, output) = check(row);
    assert!(ok, "{} did not check:\n{output}", row.path.display());
    assert!(
        output.contains(&format!("{}: ok", row.path.display())),
        "{} checked without the ok line:\n{output}",
        row.path.display()
    );
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

/// The CLI tier: the checked-in generator outputs, which nothing regenerates,
/// so the gate is that they still check — and `calc_text`, which was a
/// separate serial gate in `scripts/test` while it cost 334 CPU-s and 9.8 GiB
/// and is an ordinary row since `docs/app-by-head-type-design.md` (16 s,
/// 0.3 GiB at width one, 2026-09-22).
/// The result parser and relational contexts also run here so their standalone
/// module paths stay covered alongside their in-process tests. The library
/// clients run here and nowhere else: their modules' probes are `lib/_tests`
/// theorems and their refusals Rust tests, so a client is only a client
/// (docs/test-value-audit.md §3.1).
#[test]
fn cli_tier_rows_each_have_a_test() {
    let mut manifest: Vec<String> = showcase::at_tier(Tier::Cli).into_iter().map(|r| r.name).collect();
    manifest.sort();
    let mut tested: Vec<String> = CLI_ROWS.iter().map(|s| s.to_string()).collect();
    tested.sort();
    assert_eq!(manifest, tested, "the CLI tier and CLI_ROWS disagree: give a new row its own test");
}

#[test]
fn cli_showcase_calc_text() {
    check_row("calc_text");
}

#[test]
fn cli_showcase_contextual_rewrite_generated() {
    check_row("contextual_rewrite_generated");
}

#[test]
fn cli_showcase_relational_generator_generated() {
    check_row("relational_generator_generated");
}

#[test]
fn cli_showcase_result_parser() {
    check_row("result_parser");
}

#[test]
fn cli_showcase_relational_contexts() {
    check_row("relational_contexts");
}

#[test]
fn cli_showcase_rat_client() {
    check_row("rat_client");
}

#[test]
fn cli_showcase_creal_client() {
    check_row("creal_client");
}

#[test]
fn cli_showcase_ordered_field_client() {
    check_row("ordered_field_client");
}

#[test]
fn cli_showcase_semiring_client() {
    check_row("semiring_client");
}

#[test]
fn cli_showcase_itree_client() {
    check_row("itree_client");
}

#[test]
fn cli_showcase_itree_refinement_client() {
    check_row("itree_refinement_client");
}

#[test]
fn cli_showcase_memory_client() {
    check_row("memory_client");
}

/// The in-process rows (tiers `suite` and `test`), checked once more as
/// `heather check` sees them. Their in-process tests feed hand-built closures
/// to an elaborator, so nothing the loader adds reaches them — the common
/// prelude above all — and `calc_parser` was refused by the CLI for a day
/// while its in-process test stayed green
/// (issues/showcase-calc-parser-refused-since-prelude.md). Under the exact
/// image lane a changed compiler elaborates each of these from source.
const IN_PROCESS_ROWS: &[(Tier, &str)] = &[
    (Tier::Suite, "calc"), (Tier::Suite, "calc_parser"),
    (Tier::Test, "parser_core"), (Tier::Test, "relational_generator_input"), (Tier::Test, "relational_proof"),
    (Tier::Test, "mergeable"), (Tier::Test, "element_transport"), (Tier::Test, "lift_positive"),
    (Tier::Test, "positive_subtype"), (Tier::Test, "positive_omega"), (Tier::Test, "witness_subtype"),
    (Tier::Test, "finite_set_client"), (Tier::Test, "finite_set_list_client"), (Tier::Test, "finite_set_tree_client"),
    (Tier::Test, "finite_set_backend_transfer"), (Tier::Test, "derive_set_functions"),
    (Tier::Test, "derive_set_function_clients"), (Tier::Test, "linux_spec_client"),
];

#[test]
fn in_process_rows_each_have_a_cli_test() {
    let mut manifest: Vec<String> = [Tier::Suite, Tier::Test]
        .into_iter()
        .flat_map(|t| showcase::at_tier(t).into_iter().map(|r| r.name))
        .collect();
    manifest.sort();
    let mut tested: Vec<String> = IN_PROCESS_ROWS.iter().map(|(_, n)| n.to_string()).collect();
    tested.sort();
    assert_eq!(manifest, tested, "the suite/test tiers and IN_PROCESS_ROWS disagree: give a new row its CLI test");
}

macro_rules! cli_check_of_in_process_rows {
    ($($test:ident => $name:literal),* $(,)?) => {$(
        #[test]
        fn $test() {
            let (tier, _) = IN_PROCESS_ROWS.iter().find(|(_, n)| *n == $name).expect("listed");
            check_row_at(*tier, $name);
        }
    )*};
}

cli_check_of_in_process_rows! {
    cli_check_calc => "calc",
    cli_check_calc_parser => "calc_parser",
    cli_check_parser_core => "parser_core",
    cli_check_relational_generator_input => "relational_generator_input",
    cli_check_relational_proof => "relational_proof",
    cli_check_mergeable => "mergeable",
    cli_check_element_transport => "element_transport",
    cli_check_lift_positive => "lift_positive",
    cli_check_positive_subtype => "positive_subtype",
    cli_check_positive_omega => "positive_omega",
    cli_check_witness_subtype => "witness_subtype",
    cli_check_finite_set_client => "finite_set_client",
    cli_check_finite_set_list_client => "finite_set_list_client",
    cli_check_finite_set_tree_client => "finite_set_tree_client",
    cli_check_finite_set_backend_transfer => "finite_set_backend_transfer",
    cli_check_derive_set_functions => "derive_set_functions",
    cli_check_derive_set_function_clients => "derive_set_function_clients",
    cli_check_linux_spec_client => "linux_spec_client",
}
