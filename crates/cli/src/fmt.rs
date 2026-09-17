//! `heather fmt` — normalize the whitespace of Heather source in place.
//!
//! Deliberately independent of the elaborator: formatting is most wanted on
//! source that does not yet compile, so this path lexes and parses but never
//! checks (issues/heather-formatter.md).

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use heather_syntax::fmt::format_source;

use crate::color;

/// `heather fmt [--check] <file-or-dir>...`
pub fn run(args: &[String]) -> ExitCode {
    let mut check_only = false;
    let mut targets: Vec<PathBuf> = Vec::new();
    for a in args {
        if a == "--check" {
            check_only = true;
        } else if a.starts_with('-') {
            eprintln!("{}: unknown flag `{a}`", color::error_label(color::stderr_enabled()));
            return ExitCode::from(2);
        } else {
            targets.push(PathBuf::from(a));
        }
    }
    if targets.is_empty() {
        eprintln!("usage: heather fmt [--check] <file-or-dir>...");
        return ExitCode::from(2);
    }

    let mut files = Vec::new();
    for t in &targets {
        if t.is_dir() {
            collect(t, &mut files);
        } else {
            files.push(t.clone());
        }
    }
    files.sort();
    files.dedup();

    let mut changed = Vec::new();
    for path in &files {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!(
                    "{}: {}: {e}",
                    color::error_label(color::stderr_enabled()),
                    path.display()
                );
                return ExitCode::from(2);
            }
        };
        let out = format_source(&src);
        if out == src {
            continue;
        }
        changed.push(path.clone());
        if !check_only {
            if let Err(e) = std::fs::write(path, &out) {
                eprintln!(
                    "{}: {}: {e}",
                    color::error_label(color::stderr_enabled()),
                    path.display()
                );
                return ExitCode::from(2);
            }
        }
    }

    if check_only {
        if changed.is_empty() {
            println!("fmt: {} file(s) already formatted", files.len());
            return ExitCode::SUCCESS;
        }
        for p in &changed {
            println!("{}", p.display());
        }
        println!("fmt: {} of {} file(s) need formatting", changed.len(), files.len());
        // 1, matching `check`: a diagnostic about the input, not a failed run.
        return ExitCode::from(1);
    }
    println!("fmt: {} of {} file(s) reformatted", changed.len(), files.len());
    ExitCode::SUCCESS
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect(&p, out);
        } else if p.extension().is_some_and(|x| x == "hthr") {
            out.push(p);
        }
    }
}
