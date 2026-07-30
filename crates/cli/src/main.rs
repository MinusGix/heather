//! `heather` — the CLI face of the checker (issues/cli-check-diagnostics.md).
//!
//! `heather check <file.hthr>…` elaborates each file against a fresh
//! prelude'd elaborator and prints diagnostics. Exit codes: 0 every file
//! checked, 1 some file had diagnostics, 2 the run itself failed (usage,
//! unreadable file, a prelude that does not check).
//!
//! Argument parsing is by hand: the interface is one subcommand, and the
//! workspace above the kernel stays dependency-light until the policy round
//! (issues/dependency-policy.md) says otherwise.

use std::process::ExitCode;

use heather_elab::Elaborator;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.split_first() {
        Some((cmd, files)) if cmd == "check" && !files.is_empty() => check(files),
        _ => {
            eprintln!("usage: heather check <file.hthr>...");
            ExitCode::from(2)
        }
    }
}

fn check(files: &[String]) -> ExitCode {
    let mut failed = false;
    for path in files {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: cannot read `{path}`: {e}");
                return ExitCode::from(2);
            }
        };
        // A fresh elaborator per file: files are whole programs today — there
        // is no import system for one file to see another through.
        let mut elab = match Elaborator::with_prelude() {
            Ok(e) => e,
            Err(e) => {
                eprintln!("internal error: the prelude failed to check: {e}");
                return ExitCode::from(2);
            }
        };
        let errs = elab.check_source(&src);
        if errs.is_empty() {
            println!("{path}: ok");
            continue;
        }
        failed = true;
        for (i, e) in errs.iter().enumerate() {
            if i > 0 {
                eprintln!();
            }
            eprint!("{}", e.render_snippet(&src, path));
        }
        let n = errs.len();
        eprintln!("\n{path}: {n} error{}", if n == 1 { "" } else { "s" });
    }
    ExitCode::from(if failed { 1 } else { 0 })
}
