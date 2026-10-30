//! A module checked by two processes shares one image whatever else either
//! process loads (`docs/module-dag-design.md`): it is checked over its own
//! import closure, keyed by that closure, under its own lint profile.
//! `--world`, which made the prefixes equal instead
//! (`docs/library-world-design.md`), is accepted and changes nothing.

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
