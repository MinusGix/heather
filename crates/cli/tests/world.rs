//! A module checked by two processes shares one image whatever else either
//! process loads (`docs/infrastructure/module-dag-design.md`): it is checked over its own
//! import closure, keyed by that closure, under its own lint profile.
//! `--world`, which made the prefixes equal instead
//! (`docs/archive/library-world-design.md`), is accepted and changes nothing.

use std::path::{Path, PathBuf};
use std::process::Command;

/// A scratch library under a fresh directory, `files` as (path, source).
fn library(tag: &str, files: &[(&str, &str)]) -> PathBuf {
    let root = std::env::temp_dir().join(format!("heather-world-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    for (path, src) in files {
        let path = root.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, src).unwrap();
    }
    root
}

/// `heather check --cache-dir <root>/images <args>` from `root`, which must
/// pass; its stdout.
fn check(root: &Path, args: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(root)
        .arg("check")
        .arg("--cache-dir")
        .arg(root.join("images"))
        .args(args)
        .output()
        .expect("run heather");
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(out.status.success(), "{stdout}{}", String::from_utf8_lossy(&out.stderr));
    stdout
}

fn replayed(stdout: &str) -> usize {
    let (before, _) = stdout.split_once(" semantic module").unwrap_or_else(|| panic!("no replay count: {stdout}"));
    before.rsplit(' ').next().unwrap().parse().unwrap()
}

fn accepted(stdout: &str) -> usize {
    let (before, _) = stdout.split_once(" accepted from cache").unwrap_or_else(|| panic!("no cache count: {stdout}"));
    before.rsplit(' ').next().unwrap().parse().unwrap()
}

/// `user` imports `colour` before `base`, so `lib/c`'s load order puts
/// `colour` under `base` where `lib/b`'s holds no `colour` at all, and
/// `colour`'s inductive came before `base`'s in one process and not in the
/// other.
const LIB: &[(&str, &str)] = &[
    ("lib/a/colour.hthr", "inductive Colour { Red, Green }\n"),
    ("lib/a/shade.hthr", "import colour;\nfn shade(c: Colour) → Colour { c }\n"),
    ("lib/b/base.hthr", "inductive Base { One, Two }\nfn base_one() → Base { One }\n"),
    ("lib/b/top.hthr", "import base;\nfn top() → Base { base_one() }\n"),
    ("lib/c/user.hthr", "import colour;\nimport base;\nfn user() → Base { base_one() }\n"),
];

#[test]
fn folders_share_their_shared_modules_whatever_their_load_orders() {
    let root = library("shared", LIB);
    check(&root, &["lib/b"]);
    check(&root, &["lib/a"]);
    // `colour` and `base`, built by two other processes over other loads.
    assert_eq!(replayed(&check(&root, &["lib/c"])), 2);
    let _ = std::fs::remove_dir_all(&root);
}

/// A root loads its closure and nothing else: `lib/a` needs only `colour`
/// of what `lib/c` built.
#[test]
fn a_root_loads_only_its_closure() {
    let root = library("prefix", LIB);
    check(&root, &["lib/c"]);
    let out = check(&root, &["lib/a"]);
    assert_eq!(replayed(&out), 1, "{out}");
    let _ = std::fs::remove_dir_all(&root);
}

/// `--world` is accepted for the callers that pass it, and changes nothing.
#[test]
fn the_world_flag_changes_nothing() {
    let root = library("flag", LIB);
    check(&root, &["lib/c"]);
    assert_eq!(replayed(&check(&root, &["--world", "lib", "lib/c"])), 3);
    let _ = std::fs::remove_dir_all(&root);
}

/// The lint profile is the module's: a `lib/std` module keeps its image key
/// whichever root pulls it in, so a check from outside `std` replays what a
/// check of `std` built.
#[test]
fn a_library_module_keeps_its_profile_under_any_root() {
    let root = library("profile", &[
        ("lib/std/core/base.hthr", "inductive Base { One, Two }\nfn base_one() → Base { One }\n"),
        ("lib/native/top.hthr", "import base;\nfn top() → Base { base_one() }\n"),
    ]);
    check(&root, &["lib/std/core"]);
    assert_eq!(replayed(&check(&root, &["lib/native"])), 1);
    let _ = std::fs::remove_dir_all(&root);
}

/// `--build-jobs` elaborates every module without an image, one process
/// each, before the check, which then replays all of them; with every image
/// present it builds nothing (`docs/infrastructure/module-dag-design.md` §12).
#[test]
fn build_jobs_build_every_missing_module_ahead() {
    let root = library("build", LIB);
    let built = |out: &std::process::Output| String::from_utf8_lossy(&out.stderr).lines().find(|l| l.contains("built ahead")).map(str::to_string);
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_heather"))
            .current_dir(&root)
            .arg("check")
            .arg("--cache-dir")
            .arg(root.join("images"))
            .args(args)
            .output()
            .expect("run heather")
    };
    let out = run(&["--build-jobs", "2", "--build-only", "lib/c"]);
    assert!(out.status.success());
    assert_eq!(built(&out).as_deref(), Some("build: 3 modules built ahead, 0 failed"), "{}", String::from_utf8_lossy(&out.stderr));
    assert!(out.stdout.is_empty(), "`--build-only` reports no module");
    assert_eq!(replayed(&check(&root, &["lib/c"])), 3);
    let out = run(&["--build-jobs", "2", "lib/c"]);
    assert_eq!(built(&out).as_deref(), Some("build: 0 modules built ahead, 0 failed"));
    assert_eq!(replayed(&String::from_utf8_lossy(&out.stdout)), 3);
    let _ = std::fs::remove_dir_all(&root);
}

/// `--unbuilt` names the modules of a load that have no image, in the
/// loader's order, and exits 1 while there are any; it builds nothing. The
/// test runner asks it before starting a target that reads the gate's store.
#[test]
fn unbuilt_names_the_modules_without_an_image() {
    let root = library("unbuilt", LIB);
    let unbuilt = || {
        let out = Command::new(env!("CARGO_BIN_EXE_heather"))
            .current_dir(&root)
            .arg("check")
            .arg("--cache-dir")
            .arg(root.join("images"))
            .args(["--unbuilt", "lib/c"])
            .output()
            .expect("run heather");
        (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned())
    };
    assert_eq!(unbuilt(), (Some(1), "colour\nbase\nuser\n".to_string()));
    assert_eq!(unbuilt().1, "colour\nbase\nuser\n", "asking builds nothing");
    check(&root, &["lib/a"]);
    assert_eq!(unbuilt(), (Some(1), "base\nuser\n".to_string()));
    check(&root, &["lib/c"]);
    assert_eq!(unbuilt(), (Some(0), String::new()));
    let _ = std::fs::remove_dir_all(&root);
}

/// A module that fails to build is reported, its dependents are left
/// unbuilt, and the check after the builds reports it as usual.
#[test]
fn a_module_that_fails_to_build_leaves_the_check_to_report_it() {
    let root = library("build-fails", &[
        ("lib/a/broken.hthr", "fn bad() → Nat { nope() }\n"),
        ("lib/a/above.hthr", "import broken;\nfn above() → Nat { 0 }\n"),
        ("lib/a/beside.hthr", "fn beside() → Nat { 0 }\n"),
    ]);
    let out = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["check", "--cache-dir"])
        .arg(root.join("images"))
        .args(["--build-jobs", "2", "lib/a"])
        .output()
        .expect("run heather");
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{err}");
    assert!(err.contains("build: broken ("), "{err}");
    assert!(err.contains("build: 1 module built ahead, 1 failed"), "{err}");
    assert!(err.contains("unbound name `nope`"), "{err}");
    let _ = std::fs::remove_dir_all(&root);
}

/// A replay that passed once is vouched for whole the next time over the
/// same worlds: none of its declarations is asked about
/// (`docs/infrastructure/module-dag-design.md` §13). That holds for an import moved into
/// another module's world as well as for one replayed over its own. An edit
/// below a module changes its world's identity, so its replay is rechecked
/// again.
#[test]
fn a_replay_that_passed_is_vouched_for_whole_next_time() {
    let root = library("vouched", LIB);
    let first = check(&root, &["lib/c"]);
    assert!(!first.contains("vouched"), "{first}");
    let second = check(&root, &["lib/c"]);
    assert_eq!(replayed(&second), 3);
    assert!(second.contains("0 declarations kernel-checked"), "{second}");
    // `colour` and `base` replay over the prelude alone the first warm time
    // and record it, and one of them again moved above the other, under
    // `user`; `user`'s world is theirs.
    let third = check(&root, &["lib/c"]);
    assert!(third.contains("0 declarations kernel-checked"), "{third}");
    assert!(third.contains("(4 vouched for whole)"), "{third}");
    // Nothing is asked about one declaration at a time, the moved import's
    // bindings included.
    assert_eq!(accepted(&third), 0, "{second}{third}");
    // An edit to `base` changes its image and every world above it.
    std::fs::write(root.join("lib/b/base.hthr"), "inductive Base { One, Two, Three }\nfn base_one() → Base { One }\n").unwrap();
    let edited = check(&root, &["lib/c"]);
    assert!(edited.contains("(1 vouched for whole)"), "only `colour` is unchanged: {edited}");
    let _ = std::fs::remove_dir_all(&root);
}
