//! `heather` — the CLI face of the checker (issues/cli-check-diagnostics.md).
//!
//! `heather check [-L <dir>]… <file.hthr>…` elaborates each root file **and
//! everything it imports** against a fresh prelude'd elaborator, and prints
//! diagnostics. Exit codes: 0 every file checked, 1 some file had
//! diagnostics, 2 the run itself failed (usage, unreadable file, an import
//! that does not resolve, a cycle, a prelude that does not check).
//!
//! The import closure is one elaboration into one shared Ψ
//! (docs/modules-design.md §3.2): the loader orders the modules, this file
//! feeds them in that order, and each module's diagnostics are rendered
//! against its *own* source.
//!
//! Argument parsing is by hand: the interface is one subcommand, and the
//! workspace above the kernel stays dependency-light until the policy round
//! (issues/dependency-policy.md) says otherwise.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use heather_elab::Elaborator;

mod loader;

/// Where the standard library lives when nobody says otherwise
/// (docs/modules-design.md §3.2). Defaulted only if it exists, so a run from
/// a directory without one behaves exactly as it did before modules.
const DEFAULT_LIB: &str = "lib/std";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.split_first() {
        Some((cmd, rest)) if cmd == "check" => match parse_check_args(rest) {
            Ok((search, files)) if !files.is_empty() => check(&search, &files),
            Ok(_) => usage(),
            Err(msg) => {
                eprintln!("error: {msg}");
                eprintln!("usage: heather check [-L <dir>]... <file.hthr>...");
                ExitCode::from(2)
            }
        },
        _ => usage(),
    }
}

fn usage() -> ExitCode {
    eprintln!("usage: heather check [-L <dir>]... <file.hthr>...");
    ExitCode::from(2)
}

/// `-L <dir>` (repeatable) before, after or between the files; everything
/// else is a root file.
fn parse_check_args(args: &[String]) -> Result<(Vec<PathBuf>, Vec<String>), String> {
    let mut search = Vec::new();
    let mut files = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if let Some(dir) = a.strip_prefix("-L") {
            let dir = if dir.is_empty() {
                it.next().ok_or("`-L` needs a directory")?.clone()
            } else {
                dir.to_string()
            };
            search.push(PathBuf::from(dir));
            continue;
        }
        if a.starts_with('-') {
            return Err(format!("unknown option `{a}`"));
        }
        files.push(a.clone());
    }
    if search.is_empty() && Path::new(DEFAULT_LIB).is_dir() {
        search.push(PathBuf::from(DEFAULT_LIB));
    }
    Ok((search, files))
}

fn check(search: &[PathBuf], files: &[String]) -> ExitCode {
    let mut failed = false;
    for path in files {
        // A fresh elaborator per **root**: two roots re-elaborate a shared
        // import, which at prelude sizes costs milliseconds (caching is
        // docs/modules-design.md §8's round, not this one).
        let mut elab = match Elaborator::with_prelude() {
            Ok(e) => e,
            Err(e) => {
                eprintln!("internal error: the prelude failed to check: {e}");
                return ExitCode::from(2);
            }
        };
        let modules = match loader::load(Path::new(path), search) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("error: {}", e.msg);
                return ExitCode::from(2);
            }
        };
        let mut root_ok = true;
        for m in &modules {
            let errs = elab.check_module_source(&m.name, &m.src);
            if errs.is_empty() {
                continue;
            }
            root_ok = false;
            failed = true;
            // Rendered against the module's own source and its own path: an
            // error in an imported file is that file's error.
            let shown = display_path(&m.path, path);
            for (i, e) in errs.iter().enumerate() {
                if i > 0 {
                    eprintln!();
                }
                eprint!("{}", e.render_snippet(&m.src, &shown));
            }
            let n = errs.len();
            eprintln!("\n{shown}: {n} error{}", if n == 1 { "" } else { "s" });
        }
        if root_ok {
            println!("{path}: ok");
        }
    }
    ExitCode::from(if failed { 1 } else { 0 })
}

/// The root keeps the spelling the user typed; an imported module is named by
/// its resolved path, since the user never wrote one.
fn display_path(module_path: &Path, root_arg: &str) -> String {
    match Path::new(root_arg).canonicalize() {
        Ok(c) if c == module_path => root_arg.to_string(),
        _ => module_path.display().to_string(),
    }
}
