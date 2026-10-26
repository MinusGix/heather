//! The whole-library gate (`docs/test-value-audit.md` §4.1,
//! `issues/library-whole-check-gate.md`).
//!
//! Before this file the suite checked a `lib/` module only while some Rust
//! test happened to `include_str!` it, so every library PR wrote a Rust test
//! whose first job was to get its module checked at all, and a module whose
//! last test went (`elf64_load`, at #156) was checked by nothing. Here the
//! library is checked as a whole, through the CLI, and two lints keep the
//! tree honest: every module is reached from somewhere, and nothing outside
//! `lib/_tests` imports a test module (§4.5). Refusals live in `lib/_tests`
//! too, as declarations under `// expect-error` directives (§4.3).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use heather_cli::showcase;

fn root() -> PathBuf {
    showcase::repo_root()
}

/// The `lib/` folder that holds theorems which are tests rather than library
/// code: probes at specific values, contract restatements, refusals. It
/// mirrors `lib/`, and its stems end in `_tests` (module names are stems and
/// the loader searches every folder below `-L`, so a mirror of `arith` cannot
/// also be called `arith`).
const TESTS_DIR: &str = "lib/_tests";

/// Modules nothing imports that are kept on purpose, each with its reason.
/// A module lands here only when someone decides it should stay without a
/// consumer; the lint's message says to delete it or list it.
const KEPT_ROOTS: &[(&str, &str)] = &[
    // docs/native-program-logic-design.md §3 keeps the ELF modules for the
    // native rebuild; nothing has consumed them since B2 (#156) burned the
    // per-function path.
    ("elf64_load", "kept for the native rebuild (native-program-logic-design §3)"),
];

fn hthr_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    let mut paths: Vec<PathBuf> = entries.map(|e| e.expect("dir entry").path()).collect();
    paths.sort();
    for p in paths {
        let hidden = p.file_name().is_some_and(|n| n.to_string_lossy().starts_with('.'));
        if p.is_dir() && !hidden {
            hthr_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "hthr") {
            out.push(p);
        }
    }
}

fn stem(p: &Path) -> String {
    p.file_stem().expect("stem").to_string_lossy().into_owned()
}

/// The modules a Heather source imports, read off its `import` lines. The
/// loader parses for real; a lint over every file in the repository only
/// needs the names, and reading them textually also finds the imports inside
/// the Rust tests' source strings.
fn imports(src: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut rest = src;
    while let Some(i) = rest.find("import ") {
        let before = rest[..i].chars().next_back();
        rest = &rest[i + "import ".len()..];
        if before.is_some_and(|c| c.is_alphanumeric() || c == '_') {
            continue;
        }
        let name: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
        if !name.is_empty() {
            out.insert(name);
        }
    }
    out
}

/// Every file that may import a library module, with what it imports:
/// `lib/` itself, the showcases, and the test crates' fixtures and sources
/// (a Rust test's `MODULES` list names the file by path, so a path mention
/// counts as a use too).
fn importers() -> Vec<(PathBuf, String)> {
    let root = root();
    let mut files = Vec::new();
    hthr_files(&root.join("lib"), &mut files);
    hthr_files(&root.join("docs/showcase"), &mut files);
    for krate in std::fs::read_dir(root.join("crates")).expect("crates").map(|e| e.expect("entry").path()) {
        for sub in ["tests", "src", "benches"] {
            let mut stack = vec![krate.join(sub)];
            while let Some(dir) = stack.pop() {
                let Ok(entries) = std::fs::read_dir(&dir) else { continue };
                for p in entries.map(|e| e.expect("entry").path()) {
                    if p.is_dir() {
                        stack.push(p);
                    } else if p.extension().is_some_and(|x| x == "rs" || x == "hthr") {
                        files.push(p);
                    }
                }
            }
        }
    }
    files.into_iter().map(|p| {
        let src = std::fs::read_to_string(&p).unwrap_or_default();
        (p, src)
    }).collect()
}

/// Every module under `lib/` is reached: another file imports it, a test
/// names its file, it is a `lib/_tests` module (those are roots by design),
/// or it is listed in [`KEPT_ROOTS`] with a reason.
#[test]
fn every_library_module_is_reached() {
    let root = root();
    let mut lib = Vec::new();
    hthr_files(&root.join("lib"), &mut lib);
    let files = importers();
    let mut orphans = Vec::new();
    for module in &lib {
        if module.starts_with(root.join(TESTS_DIR)) {
            continue;
        }
        let name = stem(module);
        if KEPT_ROOTS.iter().any(|(kept, _)| *kept == name) {
            continue;
        }
        let file_name = format!("/{name}.hthr");
        let reached = files.iter().any(|(path, src)| {
            path != module && (imports(src).contains(&name) || (path.extension().is_some_and(|x| x == "rs") && src.contains(&file_name)))
        });
        if !reached {
            orphans.push(module.strip_prefix(&root).unwrap_or(module).display().to_string());
        }
    }
    assert!(
        orphans.is_empty(),
        "library modules nothing imports and no test names: {orphans:?}\n\
         Delete them, import them, or list them in KEPT_ROOTS with the reason they stay."
    );
    for (kept, why) in KEPT_ROOTS {
        assert!(
            lib.iter().any(|m| stem(m) == *kept),
            "KEPT_ROOTS lists `{kept}` ({why}), which is no longer in lib/: drop the row"
        );
    }
}

/// `lib/_tests` is a leaf: nothing outside it imports one of its modules, and
/// its stems end in `_tests` so they cannot collide with the modules they
/// mirror.
#[test]
fn nothing_outside_lib_tests_imports_a_test_module() {
    let root = root();
    let tests_root = root.join(TESTS_DIR);
    let mut test_modules = Vec::new();
    hthr_files(&tests_root, &mut test_modules);
    let names: BTreeMap<String, PathBuf> = test_modules.iter().map(|p| (stem(p), p.clone())).collect();
    let misnamed: Vec<&String> = names.keys().filter(|n| !n.ends_with("_tests")).collect();
    assert!(misnamed.is_empty(), "lib/_tests modules must be named `<subject>_tests`: {misnamed:?}");
    let mut leaks = Vec::new();
    for (path, src) in importers() {
        if path.starts_with(&tests_root) {
            continue;
        }
        for name in imports(&src) {
            if names.contains_key(&name) {
                leaks.push(format!("{} imports {name}", path.strip_prefix(&root).unwrap_or(&path).display()));
            }
        }
    }
    assert!(leaks.is_empty(), "only lib/_tests may import its own modules:\n  {}", leaks.join("\n  "));
}

/// The lint's reader, on the spellings the library uses.
#[test]
fn imports_are_read_by_name() {
    let src = "import nat;\nimport logic::{False};\n// reimport x;\nfn f() -> Nat { 0 }\n";
    let got: Vec<String> = imports(src).into_iter().collect();
    assert_eq!(got, ["logic", "nat"]);
}

/// The folders the gate checks, one `heather check` each: every folder of
/// `lib/std` and of its mirror `lib/_tests/std`, then every other folder of
/// `lib/` and of `lib/_tests`. One process for all of
/// `lib/` would be one elaboration of the whole library under a single CPU
/// rail, which a cold image store (a fresh box, a kernel edit) takes nearly
/// all of; a folder at a time keeps each child well inside it. A module file
/// directly in one of the split directories would belong to no folder, so
/// there are none.
fn gate_folders() -> Vec<PathBuf> {
    let root = root();
    let dirs = |dir: &Path| -> Vec<PathBuf> {
        let mut out: Vec<PathBuf> = std::fs::read_dir(dir)
            .expect("read lib")
            .map(|e| e.expect("entry").path())
            .filter(|p| p.is_dir() && !p.file_name().is_some_and(|n| n.to_string_lossy().starts_with('.')))
            .collect();
        out.sort();
        out
    };
    // `lib/_tests` mirrors `lib/`, and its closure is most of the library,
    // so it splits the same way: one cold process for all of it ran into the
    // rail on a fresh box (2026-10-25).
    let split = ["lib", "lib/std", TESTS_DIR, "lib/_tests/std"];
    for dir in split {
        let loose: Vec<PathBuf> = std::fs::read_dir(root.join(dir)).expect("read lib")
            .map(|e| e.expect("entry").path())
            .filter(|p| p.extension().is_some_and(|x| x == "hthr"))
            .collect();
        assert!(loose.is_empty(), "modules directly in {dir}: {loose:?}; give them a folder");
    }
    let mut folders = Vec::new();
    for dir in split {
        folders.extend(dirs(&root.join(dir)).into_iter().filter(|p| !split.iter().any(|s| p.ends_with(s))));
    }
    folders.into_iter().map(|p| p.strip_prefix(&root).expect("under the root").to_path_buf()).collect()
}

/// Every module under `lib/` checks, `lib/_tests` included: one `heather
/// check` per folder ([`gate_folders`]), three side by side, through one semantic
/// cache at width one as `scripts/test` runs every child. Folders share
/// modules, and every child loads them over one world (`--world lib`,
/// `docs/library-world-design.md`): the library's shared modules in one order,
/// up to the last its folder needs, so a shared module has one image key in
/// every child. Without it each folder's own load order gave the same module
/// a different prefix, and from a cold store every child rebuilt the part of
/// `std` it needed. The store is the showcase gate's too
/// ([`showcase::CLI_CHECK_IMAGES`]); its single-flight build makes the second
/// asker wait for the first's image rather than elaborate it again. Warm, every
/// module replays; a changed module or compiler re-elaborates what changed.
/// The fast lane's trade (`HEATHER_SEMANTIC_IMAGES=accept-stale`) replays
/// images an earlier build wrote, as the showcase gate does.
///
/// The check reads `// expect-error` directives (`--expectations`,
/// `crates/cli/src/expect.rs`): a refusal in `lib/_tests` must be refused for
/// the reason its directive names, and anything a directive does not mark
/// must check. A module with no directives is checked exactly as without
/// the flag.
#[test]
fn every_library_module_checks() {
    let root = root();
    let stale = std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() == Ok("accept-stale");
    // Three at a time, as the suite runner runs targets: each child may
    // hold a library prefix in memory.
    // In the order the world placed the folders' modules: a child then finds
    // the shared modules before its own built by the children before it,
    // rather than elaborating the world's front under its own rail.
    let world = heather_cli::world::World::of(&root.join("lib"), &[root.join("lib/std"), root.join("lib")]).unwrap_or_else(|e| panic!("the library's world: {}", e.msg));
    let mut folders = gate_folders();
    folders.sort_by_key(|f| world.folders().iter().position(|w| w.starts_with(root.join(f))).unwrap_or(usize::MAX));
    let queue = std::sync::Mutex::new(std::collections::VecDeque::from(folders));
    let failures = std::sync::Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..3 {
            scope.spawn(|| loop {
                let Some(folder) = queue.lock().expect("queue").pop_front() else { break };
                let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
                cmd.current_dir(&root).arg("check");
                cmd.env("HEATHER_KERNEL_WORKERS", "1");
                cmd.arg("--cache").arg("--cache-dir").arg(showcase::CLI_CHECK_IMAGES);
                cmd.arg("--expectations").arg("--world").arg("lib");
                if stale {
                    cmd.arg("--accept-stale-images");
                }
                cmd.arg(&folder);
                let out = cmd.output().expect("run heather check");
                let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
                text.push_str(&String::from_utf8_lossy(&out.stderr));
                let ok_line = format!("{}: ok", folder.display());
                if !out.status.success() || !text.contains(&ok_line) {
                    failures.lock().expect("failures").push(format!("== {} ({})\n{text}", folder.display(), out.status));
                }
            });
        }
    });
    let failures = failures.into_inner().expect("failures");
    assert!(failures.is_empty(), "the library does not check:\n{}", failures.join("\n"));
}
