//! The module lists marked `// lib-closure:` are the loader's closures
//! (`scripts/lib-closures`, `issues/grind-closure-cost.md`).
//!
//! The script writes each marked list from the roots on its marker, reading
//! imports with a line pattern. This checks every marked list in the tree
//! against the CLI's own loader instead: the same modules, in the same order,
//! each entry's `include_str!` naming that module's file. A list goes stale
//! when a module it holds gains an import; the failure says to run the
//! script, not which list to hand-edit.

use std::path::{Path, PathBuf};

use heather_cli::loader;
use heather_cli::showcase;

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    let mut entries: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "rs") {
            out.push(path);
        }
    }
}

fn hthr_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if !entry.file_name().to_string_lossy().starts_with('.') {
                hthr_files(&path, out);
            }
        } else if path.extension().is_some_and(|x| x == "hthr") {
            out.push(path);
        }
    }
}

/// The loader's closure of `roots`, less the closure of `minus`, without the
/// common prelude the loader adds to modules outside its own closure.
fn closure(lib: &Path, files: &[PathBuf], roots: &[&str], minus: &[&str]) -> Vec<(String, PathBuf)> {
    let path_of = |name: &str| -> PathBuf {
        let hits: Vec<&PathBuf> = files.iter().filter(|p| p.file_stem().is_some_and(|s| s == name)).collect();
        assert_eq!(hits.len(), 1, "module `{name}` names {} files under lib/", hits.len());
        hits[0].clone()
    };
    let load = |names: &[&str]| -> Vec<loader::Module> {
        if names.is_empty() {
            return Vec::new();
        }
        let paths: Vec<PathBuf> = names.iter().map(|n| path_of(n)).collect();
        let refs: Vec<&Path> = paths.iter().map(|p| p.as_path()).collect();
        loader::load_many(&refs, &[lib.to_path_buf()]).unwrap_or_else(|e| panic!("{}", e.msg))
    };
    let skip: Vec<String> = load(minus).into_iter().map(|m| m.name).collect();
    load(roots)
        .into_iter()
        .filter(|m| m.name != heather_elab::COMMON_MODULE && !skip.contains(&m.name))
        .map(|m| (m.name, m.path))
        .collect()
}

#[test]
fn marked_lists_are_the_loaders_closures() {
    let root = showcase::repo_root();
    let lib = root.join("lib");
    let mut lib_files = Vec::new();
    hthr_files(&lib, &mut lib_files);
    let mut sources = Vec::new();
    rust_files(&root.join("crates"), &mut sources);
    let mut marked = 0;
    let mut stale = Vec::new();
    for file in &sources {
        let text = std::fs::read_to_string(file).unwrap();
        if !text.contains("// lib-closure:") {
            continue;
        }
        let lines: Vec<&str> = text.lines().collect();
        for (i, line) in lines.iter().enumerate() {
            let Some(spec) = line.trim().strip_prefix("// lib-closure:") else { continue };
            marked += 1;
            let words: Vec<&str> = spec.split_whitespace().collect();
            let (roots, minus) = match words.iter().position(|w| *w == "minus") {
                Some(k) => (&words[..k], &words[k + 1..]),
                None => (&words[..], &[][..]),
            };
            let want = closure(&lib, &lib_files, roots, minus);
            // The entries: `("name", include_str!("rel")),`, one a line.
            let mut have = Vec::new();
            for entry in lines[i + 2..].iter().take_while(|l| l.trim() != "];") {
                let entry = entry.trim();
                let name = entry.split('"').nth(1).unwrap_or_default().to_string();
                let rel = entry.split("include_str!(\"").nth(1).and_then(|r| r.split('"').next()).unwrap_or_default();
                let path = file.parent().unwrap().join(rel).canonicalize().ok();
                have.push((name, path));
            }
            let want: Vec<(String, Option<PathBuf>)> =
                want.into_iter().map(|(n, p)| (n, p.canonicalize().ok())).collect();
            if have != want {
                let names = |v: &[(String, Option<PathBuf>)]| v.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join(" ");
                stale.push(format!(
                    "{}:{}: `// lib-closure: {}`\n  listed: {}\n  loader: {}",
                    file.strip_prefix(&root).unwrap_or(file).display(),
                    i + 1,
                    spec.trim(),
                    names(&have),
                    names(&want),
                ));
            }
        }
    }
    assert!(marked > 0, "no `// lib-closure:` list found under crates/");
    assert!(
        stale.is_empty(),
        "{} marked module list(s) differ from the loader's closure; run `scripts/lib-closures --fix`:\n{}",
        stale.len(),
        stale.join("\n")
    );
}
