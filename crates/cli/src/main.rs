//! `heather` — the CLI face of the checker (issues/cli-check-diagnostics.md).
//!
//! `heather check [-L <dir>]… [--cache] [--cache-dir <dir>] <path>…`
//! elaborates each root file **and everything it imports** against a fresh
//! prelude'd elaborator, and prints diagnostics. A directory path checks its
//! immediate `.hthr` files as one deduplicated import closure, so
//! `heather check lib/std` checks the whole standard library. Exit codes: 0 every file
//! checked, 1 some file had diagnostics, 2 the run itself failed (usage, an
//! unreadable file, an import that does not resolve, a cycle, a prelude that
//! does not check).
//!
//! `--cache` opts into the content-addressed declaration cache
//! (docs/cache-v1-design.md): declarations whose interface-closure hash a
//! previous run recorded as kernel-accepted skip the kernel gate. It is opt-in
//! precisely so that an unflagged `heather check` — the merge gate, and what
//! `scripts/bench-frontend` drives — keeps meaning exactly what it always
//! meant, byte for byte. When it *is* on, the result line says so and counts
//! what was trusted: a green partial check must never read like a green full
//! check (the Coq `vos` scar, issues/parallel-checking-and-caching.md).
//!
//! The import closure is one elaboration into one shared Ψ
//! (docs/modules-design.md §3.2): the loader orders the modules, this file
//! feeds them in that order, and each module's diagnostics are rendered
//! against its *own* source.
//!
//! Human terminal output uses a small ANSI palette; redirected streams,
//! `TERM=dumb`, and the conventional `NO_COLOR` environment variable keep
//! the byte-for-byte plain rendering used by tools and tests.
//!
//! Argument parsing is by hand: the interface is one subcommand, and the
//! workspace above the kernel stays dependency-light until the policy round
//! (issues/dependency-policy.md) says otherwise.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::rc::Rc;

use heather_cache::Cache;
use heather_elab::Elaborator;

// The loader lives in this crate's `lib` target so that the frontend bench
// corpus computes its import closure with the *same* code the CLI does
// (see `lib.rs`, issues/frontend-bench-ir-closure-stale.md).
use heather_cli::loader;

mod color;

/// Where the standard library lives when nobody says otherwise
/// (docs/modules-design.md §3.2). Defaulted only if it exists, so a run from
/// a directory without one behaves exactly as it did before modules.
const DEFAULT_LIB: &str = "lib/std";

fn main() -> ExitCode {
    let stderr_color = color::stderr_enabled();
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.split_first() {
        Some((cmd, rest)) if cmd == "check" => match parse_check_args(rest) {
            Ok((opts, files)) if !files.is_empty() => check(&opts, &files),
            Ok(_) => usage(),
            Err(msg) => {
                eprintln!("{}: {msg}", color::error_label(stderr_color));
                eprintln!("{USAGE}");
                ExitCode::from(2)
            }
        },
        Some((cmd, rest)) if cmd == "obligations" => match parse_check_args(rest) {
            Ok((opts, files)) if !files.is_empty() => obligations(&opts, &files),
            Ok(_) => usage(),
            Err(msg) => {
                eprintln!("{}: {msg}", color::error_label(stderr_color));
                eprintln!("{USAGE}");
                ExitCode::from(2)
            }
        },
        _ => usage(),
    }
}

const USAGE: &str = "usage: heather check [-L <dir>]... [--cache] [--cache-dir <dir>] <file-or-dir>...\n\
                     \x20      heather obligations [-L <dir>]... [--json] <file.hthr>...";

fn usage() -> ExitCode {
    eprintln!("{USAGE}");
    ExitCode::from(2)
}

/// Everything the flags decide.
struct Opts {
    search: Vec<PathBuf>,
    /// `--cache`: trust cache entries and record new ones. Off means the run
    /// neither reads nor writes anything and behaves exactly as before.
    cache: bool,
    cache_dir: PathBuf,
    /// `--json`: `obligations` only, per `issues/ai-facing-tooling.md`.
    json: bool,
}

/// `-L <dir>` (repeatable) and the cache flags may appear before, after or
/// between the paths; everything else is a root file or a directory whose
/// immediate `.hthr` files form one check.
fn parse_check_args(args: &[String]) -> Result<(Opts, Vec<String>), String> {
    let mut opts = Opts {
        search: Vec::new(),
        cache: false,
        cache_dir: PathBuf::from(heather_cache::DEFAULT_DIR),
        json: false,
    };
    let mut files = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if let Some(dir) = a.strip_prefix("-L") {
            let dir = if dir.is_empty() {
                it.next().ok_or("`-L` needs a directory")?.clone()
            } else {
                dir.to_string()
            };
            opts.search.push(PathBuf::from(dir));
            continue;
        }
        if a == "--cache" {
            opts.cache = true;
            continue;
        }
        if a == "--json" {
            opts.json = true;
            continue;
        }
        // `--cache-dir` implies `--cache`: naming a cache and not using it is
        // never what anyone meant.
        if let Some(rest) = a.strip_prefix("--cache-dir") {
            let dir = match rest.strip_prefix('=') {
                Some(d) if !d.is_empty() => d.to_string(),
                _ if rest.is_empty() => {
                    it.next().ok_or("`--cache-dir` needs a directory")?.clone()
                }
                _ => return Err(format!("unknown option `{a}`")),
            };
            opts.cache_dir = PathBuf::from(dir);
            opts.cache = true;
            continue;
        }
        if a.starts_with('-') {
            return Err(format!("unknown option `{a}`"));
        }
        files.push(a.clone());
    }
    if opts.search.is_empty() && Path::new(DEFAULT_LIB).is_dir() {
        opts.search.push(PathBuf::from(DEFAULT_LIB));
    }
    Ok((opts, files))
}

fn check(opts: &Opts, files: &[String]) -> ExitCode {
    let stderr_color = color::stderr_enabled();
    let stdout_color = color::stdout_enabled();
    // One cache for the whole run, shared across roots: a declaration two
    // roots have in common is checked once. Loading says out loud when it
    // threw an existing file away (a stale kernel, a corrupted file) — the
    // one thing a cache must never do is quietly do nothing.
    let cache = opts.cache.then(|| {
        let (c, rejected) = Cache::open(opts.cache_dir.clone());
        if let Some(msg) = rejected.as_ref().and_then(|r| r.message()) {
            eprintln!("{msg}");
        }
        Rc::new(c)
    });

    let mut failed = false;
    for path in files {
        // A fresh elaborator per **path**: two file paths re-elaborate a shared
        // import, which at prelude sizes costs milliseconds (caching is
        // docs/modules-design.md §8's round, not this one).
        let mut elab = match Elaborator::with_prelude() {
            Ok(e) => e,
            Err(e) => {
                eprintln!(
                    "{}: the prelude failed to check: {e}",
                    color::internal_error_label(stderr_color)
                );
                return ExitCode::from(2);
            }
        };
        // After the prelude, deliberately: the prelude is elaborated inside
        // `with_prelude` and is milliseconds, so it is hashed but never
        // cached (docs/cache-v1-design.md §4).
        let before = cache.as_ref().map(|c| {
            // Each root is a fresh Ψ, so the cache's view of it restarts too;
            // the recorded entries, being content-addressed, do not.
            c.begin_run();
            elab.set_gate(Rc::clone(c) as Rc<dyn heather_elab::gate::KernelGate>);
            c.counts()
        });
        let roots = match roots_for_path(Path::new(path)) {
            Ok(roots) => roots,
            Err(msg) => {
                eprintln!("{}: {msg}", color::error_label(stderr_color));
                return ExitCode::from(2);
            }
        };
        let root_refs = roots.iter().map(PathBuf::as_path).collect::<Vec<_>>();
        let modules = match loader::load_many(&root_refs, &opts.search) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("{}: {}", color::error_label(stderr_color), e.msg);
                return ExitCode::from(2);
            }
        };
        let mut root_ok = true;
        for m in &modules {
            let errs = elab.check_module_source(&m.name, &m.src);
            // Warnings are drained per module, before the next one is checked:
            // a span indexes into the source it came from
            // (docs/diagnostic-warnings-design.md §3). They do not fail the
            // run and they do not touch the `ok` line — a warned file is a
            // checked file (§4).
            let warns = elab.take_warnings();
            if !warns.is_empty() {
                let shown = display_path(&m.path, path);
                for w in &warns {
                    eprint!(
                        "{}",
                        color::diagnostic(
                            &w.render_snippet(&m.src, &shown),
                            color::Severity::Warning,
                            stderr_color,
                        )
                    );
                    eprintln!();
                }
                let n = warns.len();
                let count = format!("{n} warning{}", if n == 1 { "" } else { "s" });
                eprintln!("{shown}: {}", color::warning_count(&count, stderr_color));
            }
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
                eprint!(
                    "{}",
                    color::diagnostic(
                        &e.render_snippet(&m.src, &shown),
                        color::Severity::Error,
                        stderr_color,
                    )
                );
            }
            let n = errs.len();
            let count = format!("{n} error{}", if n == 1 { "" } else { "s" });
            eprintln!("\n{shown}: {}", color::error_count(&count, stderr_color));
        }
        if root_ok {
            match (&cache, before) {
                // The bare `ok` is reserved for a full check, so a green line
                // from a cached run can never be mistaken for one — and a gate
                // can mechanically demand the absence of `(cache)`.
                (Some(c), Some(before)) => {
                    let n = c.counts().since(&before);
                    println!(
                        "{path}: {} (cache) — {} declaration{} kernel-checked, {} accepted \
                         from cache",
                        color::success("ok", stdout_color),
                        n.checked,
                        if n.checked == 1 { "" } else { "s" },
                        n.hits
                    );
                }
                _ => println!("{path}: {}", color::success("ok", stdout_color)),
            }
        }
    }
    if let Some(c) = &cache
        && let Err(e) = c.save()
    {
        // Not a check failure: the answer stands, only the next run pays for
        // it again. Loud anyway, since a cache that silently never persists
        // looks exactly like a cache that never helps.
        eprintln!("cache: could not write {}: {e}", opts.cache_dir.display());
    }
    ExitCode::from(if failed { 1 } else { 0 })
}

/// `heather obligations [--json] <file>` — every obligation-bearing field of
/// every such declaration in the file, with its state, its provenance and the
/// statement it owes (`docs/obligation-records-design.md` §6).
///
/// It **checks the file first**, and prints nothing if the check fails: under
/// inline-first a listed file is a certified file, so the `state` column never
/// says "open" and a listing is never a to-do list. What it is for is the
/// Q2 verdict's "distinguish provenance on inspection" — and, for an AI-facing
/// tool, knowing what a declaration owes and who discharged it before editing
/// it.
fn obligations(opts: &Opts, files: &[String]) -> ExitCode {
    let stderr_color = color::stderr_enabled();
    for path in files {
        let mut elab = match Elaborator::with_prelude() {
            Ok(e) => e,
            Err(e) => {
                eprintln!(
                    "{}: the prelude failed to check: {e}",
                    color::internal_error_label(stderr_color)
                );
                return ExitCode::from(2);
            }
        };
        let modules = match loader::load(Path::new(path), &opts.search) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("{}: {}", color::error_label(stderr_color), e.msg);
                return ExitCode::from(2);
            }
        };
        for m in &modules {
            let errs = elab.check_module_source(&m.name, &m.src);
            if errs.is_empty() {
                continue;
            }
            let shown = display_path(&m.path, path);
            for e in &errs {
                eprint!(
                    "{}",
                    color::diagnostic(
                        &e.render_snippet(&m.src, &shown),
                        color::Severity::Error,
                        stderr_color,
                    )
                );
            }
            eprintln!("\n{shown}: not checked, so there is nothing to list");
            return ExitCode::from(1);
        }
        let rows = elab.obligations();
        if opts.json {
            println!("[");
            for (i, o) in rows.iter().enumerate() {
                println!(
                    "  {{\"owner\": {}, \"path\": {}, \"field\": {}, \"state\": {}, \
                     \"provenance\": {}, \"statement\": {}}}{}",
                    json_str(&o.owner),
                    json_str(&o.path),
                    json_str(&o.field),
                    json_str(o.state),
                    match o.provenance {
                        Some(p) => json_str(p.as_str()),
                        None => "null".to_string(),
                    },
                    json_str(&o.statement),
                    if i + 1 == rows.len() { "" } else { "," }
                );
            }
            println!("]");
            continue;
        }
        let w = |f: fn(&heather_elab::Obligation) -> &str| {
            rows.iter().map(|o| f(o).chars().count()).max().unwrap_or(0)
        };
        let (wo, wf, ws) = (w(|o| &o.owner).max(5), w(|o| &o.field).max(5), w(|o| o.state).max(5));
        println!(
            "{:wo$}  {:wf$}  {:ws$}  {:10}  statement",
            "owner", "field", "state", "provenance"
        );
        for o in rows {
            println!(
                "{:wo$}  {:wf$}  {:ws$}  {:10}  {}",
                o.owner,
                o.field,
                o.state,
                o.provenance.map(|p| p.as_str()).unwrap_or("—"),
                o.statement
            );
        }
        if rows.is_empty() {
            println!("(no obligation-bearing declarations)");
        }
    }
    ExitCode::from(0)
}

/// JSON string escaping, by hand: the workspace above the kernel stays
/// dependency-light (`issues/dependency-policy.md`), and this is the whole of
/// what a serializer would do for these six fields.
fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// The root keeps the spelling the user typed; an imported module is named by
/// its resolved path, since the user never wrote one.
fn display_path(module_path: &Path, root_arg: &str) -> String {
    match Path::new(root_arg).canonicalize() {
        Ok(c) if c == module_path => root_arg.to_string(),
        Ok(c) if c.is_dir() => match module_path.strip_prefix(&c) {
            Ok(rel) => Path::new(root_arg).join(rel).display().to_string(),
            Err(_) => module_path.display().to_string(),
        },
        _ => module_path.display().to_string(),
    }
}

/// A file is one root. A directory is a deterministic, non-recursive module
/// set: Heather modules are flat names today, and recursing would silently
/// merge unrelated module namespaces.
fn roots_for_path(path: &Path) -> Result<Vec<PathBuf>, String> {
    if !path.is_dir() {
        return Ok(vec![path.to_path_buf()]);
    }
    let mut roots = std::fs::read_dir(path)
        .map_err(|e| format!("cannot read directory `{}`: {e}", path.display()))?
        .filter_map(|entry| match entry {
            Ok(entry) if entry.path().extension().is_some_and(|ext| ext == "hthr") => {
                Some(Ok(entry.path()))
            }
            Ok(_) => None,
            Err(e) => Some(Err(format!("cannot read directory `{}`: {e}", path.display()))),
        })
        .collect::<Result<Vec<_>, _>>()?;
    roots.sort();
    if roots.is_empty() {
        return Err(format!("directory `{}` contains no `.hthr` files", path.display()));
    }
    Ok(roots)
}
