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
    // A false `refl` keeps the kernel's verdict and is pointed at the `refl`,
    // with both sides (`issues/elab-refl-accepts-match-eta-kernel-rejects.md`) …
    assert!(err.contains("error: the kernel rejected `broken`: NotConvertible"), "{err}");
    assert!(
        err.contains("`refl` needs both sides to be definitionally equal"),
        "{err}"
    );
    assert!(err.contains("--> bad.hthr:6:5"), "{err}");
    // … while a refusal checking holds no note about stays at its declaration.
    assert!(err.contains("error: the kernel rejected `levels`: LevelMismatch"), "{err}");
    assert!(err.contains("--> bad.hthr:11:1"), "{err}");
    assert!(err.contains("unsolved goals in `open_goal`"), "{err}");
    assert!(err.contains("bad.hthr: 3 errors"), "{err}");
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
fn a_directory_exposes_descendant_module_directories_to_its_closure() {
    // The roots remain the immediate files (`base` and the `facade`), while
    // the facade can keep its implementation below the public module set.
    // The nested implementation can in turn import a module from the target
    // directory without requiring either directory to be repeated as `-L`;
    // `shadow/base.hthr` proves a descendant cannot conflict with that public
    // module merely because it has the same flat name.
    let out = heather(&["check", "nestedset"]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "nestedset: ok\n");
    assert!(out.stderr.is_empty(), "{}", String::from_utf8_lossy(&out.stderr));
}

#[test]
fn a_directory_checks_the_modules_kept_in_its_folders() {
    // `foldered` has no file of its own: its modules live in `a/` and `b/`.
    // Each nested module is a root, so `orphan`, which nothing imports, is
    // checked too, and its refusal fails the directory.
    let out = heather(&["check", "foldered"]);
    assert_eq!(out.status.code(), Some(1), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("orphan"), "{err}");
    assert!(!String::from_utf8_lossy(&out.stdout).contains("foldered: ok"));
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
fn a_search_directory_exposes_the_modules_below_it() {
    // A file target gets the directory-target rule for its `-L` dirs: the
    // facade's `child` lives in `nestedset/components`, and `child`'s own
    // `import base` still finds the public `nestedset/base.hthr` rather than
    // colliding with `nestedset/shadow/base.hthr`; and `nestedset/.copy`'s
    // `child` is not a second hit, since dot-directories are not searched.
    let out = heather(&["check", "-L", "nestedset", "nestedset/facade.hthr"]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "nestedset/facade.hthr: ok\n");
    // The negative control: the importing file's own directory is not
    // searched below.
    let out = heather(&["check", "nestedset/facade.hthr"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("cannot find module `child`"));
}

#[test]
fn a_provided_name_covers_a_missing_module_but_not_an_ambiguous_one() {
    // The native builder's bundled names (`loader::load_providing`): a name no
    // file answers is left to the caller, but a name two search directories
    // answer is refused, not silently replaced by the caller's copy.
    let fixtures = std::path::Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures"));
    let root = fixtures.join("uses_shared.hthr");
    let modules = heather_cli::loader::load_providing(&root, &[], &["shared"])
        .unwrap_or_else(|e| panic!("{}", e.msg));
    assert_eq!(modules.iter().map(|m| m.name.as_str()).collect::<Vec<_>>(), ["uses_shared"]);
    let search = [fixtures.join("ldir"), fixtures.join("ldir2")];
    let err = heather_cli::loader::load_providing(&root, &search, &["shared"]).err().expect("ambiguous");
    assert!(err.msg.contains("two search directories"), "{}", err.msg);
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
    assert!(warm_out.contains("1 semantic module replayed"), "{warm_out}");

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_corrupt_semantic_module_is_reported_and_rebuilt() {
    let dir = cache_dir("module-corrupt");
    let arg = dir.display().to_string();
    assert_eq!(heather(&["check", "--cache-dir", &arg, "good.hthr"]).status.code(), Some(0));
    let modules = dir.join("modules-v1");
    let artifact = std::fs::read_dir(&modules)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        // The store also holds a `.latest` pointer per module (the
        // slice-replay commit); corrupting *that* leaves the image
        // valid and proves nothing. Take the image itself.
        .find(|path| path.extension().is_some_and(|ext| ext == "hmi"))
        .expect("one cached module");
    std::fs::write(artifact, b"not an image").unwrap();

    let warm = heather(&["check", "--cache-dir", &arg, "good.hthr"]);
    assert_eq!(warm.status.code(), Some(0), "{}", String::from_utf8_lossy(&warm.stderr));
    let err = String::from_utf8_lossy(&warm.stderr);
    assert!(err.contains("stored module `good` is unusable"), "{err}");
    assert!(err.contains("rebuilding"), "{err}");
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn warning_producing_modules_replay_the_same_diagnostics() {
    let dir = cache_dir("module-warning");
    let arg = dir.display().to_string();
    let mut cold_diagnostics = None;
    for run in 0..2 {
        let out = heather(&["check", "--cache-dir", &arg, "warning.hthr"]);
        assert_eq!(out.status.code(), Some(0), "{}", String::from_utf8_lossy(&out.stderr));
        assert!(String::from_utf8_lossy(&out.stderr).contains("warning:"));
        if let Some(cold) = &cold_diagnostics {
            assert_eq!(&out.stderr, cold, "cached diagnostics must be byte-identical");
        } else {
            cold_diagnostics = Some(out.stderr.clone());
        }
        let expected = if run == 0 { 0 } else { 1 };
        assert!(String::from_utf8_lossy(&out.stdout).contains(&format!(
            "{expected} semantic module{} replayed",
            if expected == 1 { "" } else { "s" }
        )));
    }
    assert!(dir.join("modules-v1").exists());
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn opaque_proof_edits_do_not_invalidate_dependent_module_images() {
    let dir = cache_dir("module-interface");
    let sources = dir.join("sources");
    let cache = dir.join("cache");
    std::fs::create_dir_all(&sources).unwrap();
    let dependency = sources.join("dependency.hthr");
    let consumer = sources.join("consumer.hthr");
    std::fs::write(
        &dependency,
        "theorem stable(n: Nat): n = n { refl }\nfn visible() -> Nat { 0 }\n",
    )
    .unwrap();
    std::fs::write(
        &consumer,
        "import dependency;\ntheorem uses_stable(n: Nat): n = n { stable(n) }\n",
    )
    .unwrap();
    let cache_arg = cache.display().to_string();
    let consumer_arg = consumer.display().to_string();
    assert_eq!(
        heather(&["check", "--cache-dir", &cache_arg, &consumer_arg])
            .status
            .code(),
        Some(0)
    );

    std::fs::write(
        &dependency,
        "theorem stable(n: Nat): n = n { let p: (n = n) = refl; p }\nfn visible() -> Nat { 0 }\n",
    )
    .unwrap();
    let proof_edit = heather(&["check", "--cache-dir", &cache_arg, &consumer_arg]);
    assert_eq!(proof_edit.status.code(), Some(0));
    assert!(
        String::from_utf8_lossy(&proof_edit.stdout)
            .contains("1 semantic module replayed"),
        "the changed dependency rebuilds, but its unchanged consumer should replay: {}",
        String::from_utf8_lossy(&proof_edit.stdout)
    );

    std::fs::write(
        &dependency,
        "theorem stable(n: Nat): n = n { let p: (n = n) = refl; p }\nfn visible() -> Nat { 1 }\n",
    )
    .unwrap();
    let definition_edit = heather(&["check", "--cache-dir", &cache_arg, &consumer_arg]);
    assert_eq!(definition_edit.status.code(), Some(0));
    assert!(
        String::from_utf8_lossy(&definition_edit.stdout)
            .contains("0 semantic modules replayed"),
        "a transparent dependency edit invalidates its exact-prefix consumer: {}",
        String::from_utf8_lossy(&definition_edit.stdout)
    );
    let _ = std::fs::remove_dir_all(dir);
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

#[test]
fn obligations_can_replay_safe_semantic_module_images() {
    let dir = cache_dir("obligations-inspection");
    let arg = dir.display().to_string();
    let args = ["obligations", "--cache-dir", &arg, "obligations.hthr"];
    let cold = heather(&args);
    assert_eq!(cold.status.code(), Some(0), "{}", String::from_utf8_lossy(&cold.stderr));

    let warm = heather(&args);
    assert_eq!(warm.status.code(), Some(0), "{}", String::from_utf8_lossy(&warm.stderr));
    assert_eq!(warm.stdout, cold.stdout, "replay preserves the inspection result");

    let _ = std::fs::remove_dir_all(dir);
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

// -- explicit axiom provenance ---------------------------------------------

#[test]
fn axioms_lists_a_deterministic_path() {
    let out = heather(&["axioms", "indirect", "axioms.hthr"]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("axioms::seed (user)"), "{text}");
    assert!(
        text.contains("axioms::indirect -> axioms::direct -> axioms::seed"),
        "{text}"
    );
}

#[test]
fn axioms_json_exposes_direct_edges_and_paths() {
    let out = heather(&["axioms", "indirect", "--json", "axioms.hthr"]);
    assert_eq!(out.status.code(), Some(0));
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("\"direct\": [\"axioms::direct\"]"), "{text}");
    assert!(text.contains("\"kind\": \"user\""), "{text}");
    assert!(text.contains("\"path\": [\"axioms::indirect\", \"axioms::direct\", \"axioms::seed\"]"), "{text}");
}

#[test]
fn axioms_loads_and_rebuilds_semantic_module_images() {
    let dir = cache_dir("axioms-inspection");
    let arg = dir.display().to_string();
    let args = ["axioms", "indirect", "--cache-dir", &arg, "axioms.hthr"];
    let cold = heather(&args);
    assert_eq!(cold.status.code(), Some(0), "{}", String::from_utf8_lossy(&cold.stderr));

    let modules = dir.join("modules-v1");
    let artifact = std::fs::read_dir(&modules)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        // The store also holds a `.latest` pointer per module (the
        // slice-replay commit); corrupting *that* leaves the image
        // valid and proves nothing. Take the image itself.
        .find(|path| path.extension().is_some_and(|ext| ext == "hmi"))
        .expect("one cached module");
    std::fs::write(artifact, b"not an image").unwrap();
    let rebuilt = heather(&args);
    assert_eq!(rebuilt.status.code(), Some(0));
    assert_eq!(rebuilt.stdout, cold.stdout, "rebuild preserves the axiom report");
    let err = String::from_utf8_lossy(&rebuilt.stderr);
    assert!(err.contains("stored module `axioms` is unusable"), "{err}");
    assert!(err.contains("rebuilding"), "{err}");

    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn deny_axioms_is_a_check_policy() {
    let out = heather(&["check", "--deny-axioms", "axioms.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stdout.is_empty(), "{}", String::from_utf8_lossy(&out.stdout));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("axioms::direct"), "{err}");
    assert!(err.contains("axioms::indirect"), "{err}");
    assert!(!err.contains("axioms::clean"), "{err}");
}

/// After an edit, the module's unchanged declarations are reproduced from
/// its previous image and the `(cache)` line says how many
/// (`docs/declaration-slice-replay-design.md`).
#[test]
fn an_edited_module_replays_its_unchanged_declarations_from_the_previous_image() {
    let dir = cache_dir("slice-replay");
    let arg = dir.display().to_string();
    // The edited copy lives outside the repository: a source written and
    // deleted under `crates/` races the corpus scans that list the tree
    // (issues/corpus-scan-vanishing-file.md).
    let sources = cache_dir("slice-replay-sources");
    std::fs::create_dir_all(&sources).unwrap();
    let edited = sources.join("slice_edit.hthr");
    let edited_arg = edited.display().to_string();
    let fixtures = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures");
    let original = std::fs::read_to_string(std::path::Path::new(fixtures).join("good.hthr")).unwrap();
    std::fs::write(&edited, &original).unwrap();

    let cold = heather(&["check", "--cache-dir", &arg, &edited_arg]);
    assert_eq!(cold.status.code(), Some(0), "{}", String::from_utf8_lossy(&cold.stderr));
    let cold_out = String::from_utf8_lossy(&cold.stdout).to_string();
    assert!(cold_out.contains("0 declarations replayed after an edit"), "{cold_out}");

    std::fs::write(&edited, format!("{original}\nfn one_more() -> Nat {{ double(1) }}\n")).unwrap();
    let edit = heather(&["check", "--cache-dir", &arg, &edited_arg]);
    assert_eq!(edit.status.code(), Some(0), "{}", String::from_utf8_lossy(&edit.stderr));
    let edit_out = String::from_utf8_lossy(&edit.stdout).to_string();
    let items = original.matches("\nfn ").count() + original.matches("\ntheorem ").count();
    assert!(
        edit_out.contains(&format!("{items} declarations replayed after an edit")),
        "{items} unchanged declarations replay: {edit_out}"
    );
    assert!(edit_out.contains("1 declaration kernel-checked"), "the appended one faces the kernel: {edit_out}");

    let _ = std::fs::remove_dir_all(sources);
    let _ = std::fs::remove_dir_all(dir);
}

/// `heather check --only` (`docs/check-only-design.md`): needs `--cache` and a
/// previous image; elaborates the named declarations over a replayed
/// prefix, prints the reserved `(only)` line, labels the timings run row,
/// leaves the verdict store's counts alone, and names an unknown item.
#[test]
fn only_elaborates_the_named_declarations_over_a_replayed_prefix() {
    let out = heather(&["check", "--only", "double", "good.hthr"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("`--only` replays the rest"), "{}", String::from_utf8_lossy(&out.stderr));

    let dir = cache_dir("only");
    let arg = dir.display().to_string();
    let out = heather(&["check", "--cache-dir", &arg, "--only", "double", "good.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("no stored image of module `good`"), "{err}");
    // Both ways to get here are named. A module whose image the store refused
    // as over budget is re-elaborated on every warm run, so the `--cache`
    // advice alone is unfollowable for it and a reader loops
    // (`issues/check-only-no-stored-image.md`).
    assert!(err.contains("run `heather check --cache` on the file once first"), "{err}");
    assert!(err.contains("refused as too large to store"), "{err}");

    // Populate, then probe. The `(only)` line is reserved, like `(cache)`.
    // The second run replays and records the whole-replay verdict, so the
    // baseline is the third: one that already finds it (`docs/module-dag-design.md` §13).
    assert_eq!(heather(&["check", "--cache-dir", &arg, "good.hthr"]).status.code(), Some(0));
    assert_eq!(heather(&["check", "--cache-dir", &arg, "good.hthr"]).status.code(), Some(0));
    let cold = heather(&["check", "--cache-dir", &arg, "good.hthr"]);
    let baseline = String::from_utf8_lossy(&cold.stdout).to_string();
    let tsv = dir.join("only.tsv");
    let tsv_arg = tsv.display().to_string();
    let out = heather(&["check", "--cache-dir", &arg, "--only", "double", "--timings", &tsv_arg, "good.hthr"]);
    assert_eq!(out.status.code(), Some(0), "{}", String::from_utf8_lossy(&out.stderr));
    let line = String::from_utf8_lossy(&out.stdout);
    assert!(line.contains("good.hthr: ok (only) — 1 declaration elaborated for --only, "), "{line}");
    assert!(!line.contains("(cache)"), "{line}");
    let table = std::fs::read_to_string(&tsv).unwrap();
    let run_row = table.lines().find(|l| l.starts_with("run\t")).expect("a run row");
    assert!(run_row.split('\t').nth(2) == Some("only=double"), "{run_row}");
    // The store is as it was: a `--only` run vouches for nothing, and the
    // next cached run reports exactly what it reported before.
    let again = heather(&["check", "--cache-dir", &arg, "good.hthr"]);
    assert_eq!(String::from_utf8_lossy(&again.stdout), baseline);

    let out = heather(&["check", "--cache-dir", &arg, "--only", "double,nope", "good.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("--only named `good::nope` that no module of the closure declares"), "{err}");
    let _ = std::fs::remove_dir_all(dir);
}

/// An `--only` name may carry `::` itself: a member's owner is not a module.
/// The module is the first segment, and only when the closure has one by
/// that name; otherwise the whole name is the root's.
#[test]
fn only_reads_owner_qualified_names() {
    let dir = cache_dir("only-owned");
    let arg = dir.display().to_string();
    assert_eq!(heather(&["check", "--cache-dir", &arg, "owned.hthr"]).status.code(), Some(0));
    for name in ["Nat::twice_zero", "owned::Nat::twice_zero"] {
        let out = heather(&["check", "--cache-dir", &arg, "--only", name, "owned.hthr"]);
        assert_eq!(out.status.code(), Some(0), "{name}: {}", String::from_utf8_lossy(&out.stderr));
        let line = String::from_utf8_lossy(&out.stdout);
        assert!(line.contains("owned.hthr: ok (only) — 1 declaration elaborated for --only, "), "{name}: {line}");
    }
    let out = heather(&["check", "--cache-dir", &arg, "--only", "Nat::nope", "owned.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("--only named `owned::Nat::nope` that no module of the closure declares"), "{err}");
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn expectations_turn_named_refusals_into_a_green_check() {
    let out = heather(&["check", "--expectations", "expect/met.hthr"]);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", String::from_utf8_lossy(&out.stderr));
    // The green line counts what it leaned on, so it never reads like a file
    // where every declaration checked.
    assert_eq!(String::from_utf8_lossy(&out.stdout), "expect/met.hthr: ok — 4 expected refusals matched\n");
}

#[test]
fn without_expectations_a_refusal_file_fails_and_says_why() {
    let out = heather(&["check", "expect/met.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(out.stdout.is_empty(), "{}", String::from_utf8_lossy(&out.stdout));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("expect/met.hthr: 4 errors"), "{err}");
    assert!(
        err.contains("5 `// expect-error` directives here; `heather check --expectations` reads them"),
        "{err}"
    );
}

#[test]
fn every_unmet_expectation_is_an_error_where_it_is() {
    let out = heather(&["check", "--expectations", "expect/unmet.hthr"]);
    assert_eq!(out.status.code(), Some(1));
    let err = String::from_utf8_lossy(&out.stderr);
    for (said, at) in [
        ("this declaration checks, but `expect-error(kernel)` says it is refused", "unmet.hthr:3:1"),
        ("not as `expect-error: something else entirely` says; the refusal was:", "unmet.hthr:6:45"),
        ("(an incidental slip satisfies a directive only when a fragment names it)", "unmet.hthr:9:22"),
        ("an expectation names its reason", "unmet.hthr:11:1"),
        ("`typo` is not a refusal kind", "unmet.hthr:14:1"),
        ("the kernel rejected `unmarked`", "unmet.hthr:17:41"),
        ("not inside it", "unmet.hthr:20:5"),
        ("no declaration follows this expectation", "unmet.hthr:24:1"),
    ] {
        let found = err.find(said).unwrap_or_else(|| panic!("missing `{said}`:\n{err}"));
        // The first location after a message is its own.
        let loc = err[found..].split("--> ").nth(1).unwrap_or("");
        assert!(loc.starts_with(&format!("expect/{at}\n")), "`{said}` not at {at}:\n{err}");
    }
    assert!(err.contains("expect/unmet.hthr: 8 errors"), "{err}");
}
