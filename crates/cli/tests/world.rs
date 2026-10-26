//! A module checked by two processes shares one image only when both gave it
//! the same prefix (`docs/library-world-design.md`): the lint profile is the
//! module's own, and `--world` loads the library's shared modules in one
//! order before each root's own.

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

/// `colour` sorts first and `user` imports it before `base`, so `lib/c`'s
/// own load order puts `colour` under `base` and `lib/b`'s does not: two
/// prefixes, so two elaborations of `base`, and `colour`'s inductive moves
/// `base`'s nominal tag besides.
const LIB: &[(&str, &str)] = &[
    ("lib/a/colour.hthr", "inductive Colour { Red, Green }\n"),
    ("lib/a/shade.hthr", "import colour;\nfn shade(c: Colour) → Colour { c }\n"),
    ("lib/b/base.hthr", "inductive Base { One, Two }\nfn base_one() → Base { One }\n"),
    ("lib/b/top.hthr", "import base;\nfn top() → Base { base_one() }\n"),
    ("lib/c/user.hthr", "import colour;\nimport base;\nfn user() → Base { base_one() }\n"),
];

#[test]
fn folders_over_one_world_share_their_shared_modules() {
    let root = library("shared", LIB);
    check(&root, &["--world", "lib", "lib/b"]);
    // `colour` and `base`, built by `lib/b`'s process over the same prefix.
    assert_eq!(replayed(&check(&root, &["--world", "lib", "lib/c"])), 2);
    let _ = std::fs::remove_dir_all(&root);
}

/// The control: without the world, `lib/c` replays nothing `lib/b` built.
#[test]
fn folders_over_their_own_load_orders_share_nothing() {
    let root = library("unshared", LIB);
    check(&root, &["lib/b"]);
    assert_eq!(replayed(&check(&root, &["lib/c"])), 0);
    let _ = std::fs::remove_dir_all(&root);
}

/// A root needing no shared module loads none, and a root needing an early
/// one loads only the world up to it: `lib/a` is checked over `colour` alone.
#[test]
fn a_root_loads_the_world_only_up_to_what_it_needs() {
    let root = library("prefix", LIB);
    check(&root, &["--world", "lib", "lib/c"]);
    let out = check(&root, &["--world", "lib", "lib/a"]);
    assert_eq!(replayed(&out), 1, "{out}");
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
