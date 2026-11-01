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
//! `--expectations` reads `// expect-error…` directives (`expect.rs`): a
//! declaration under one must be refused for the reason it names, and is
//! then not an error. Opt-in for the same reason as `--cache`, and its green
//! line counts the refusals it matched.
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
use std::sync::Arc as Rc;

use heather_cache::Cache;
use heather_cache::module_image::ImageFreshness;
use heather_elab::{Elaborator, stats};

// The loader lives in this crate's `lib` target so that the frontend bench
// corpus computes its import closure with the *same* code the CLI does
// (see `lib.rs`, issues/frontend-bench-ir-closure-stale.md).
use heather_cli::{expect, loader, semantic::SemanticSession};

mod color;
mod fmt;
mod native;

/// Where the standard library lives when nobody says otherwise
/// (docs/modules-design.md §3.2). Defaulted only if it exists, so a run from
/// a directory without one behaves exactly as it did before modules.
const DEFAULT_LIB: &str = loader::STDLIB_DIR;
const DEFAULT_LIB_ROOT: &str = "lib";

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
        Some((cmd, rest)) if cmd == "axioms" => match rest.split_first() {
            Some((target, args)) => match parse_check_args(args) {
                Ok((opts, files)) if !files.is_empty() => axioms(&opts, target, &files),
                Ok(_) => usage(),
                Err(msg) => {
                    eprintln!("{}: {msg}", color::error_label(stderr_color));
                    eprintln!("{USAGE}");
                    ExitCode::from(2)
                }
            },
            None => usage(),
        },
        Some((cmd, rest)) if cmd == "fmt" => fmt::run(rest),
        Some((cmd, rest)) if cmd == "compile-x86" => native::run(rest),
        Some((cmd, rest)) if cmd == "reflect" => native::reflect(rest),
        Some((cmd, rest)) if cmd == "write-elf" => native::write_elf(rest),
        _ => usage(),
    }
}

const USAGE: &str = "usage: heather check [-L <dir>]... [--cache] [--cache-dir <dir>] [--accept-stale-images] [--deny-axioms] [--review] [--expectations] [--build-jobs <n> [--build-only] [--build-first <dir>]... [--build-times <file.tsv>]] [--unbuilt] [--world <dir>] [--timings <file.tsv>] [--kernel-workers <n>] <file-or-dir>...\n\
                     \x20      heather obligations [-L <dir>]... [--cache] [--cache-dir <dir>] [--json] <file.hthr>...\n\
                     \x20      heather axioms <target> [-L <dir>]... [--cache] [--cache-dir <dir>] [--json] <file-or-dir>...\n\
                     \x20      heather fmt [--check] <file-or-dir>...\n\
                     \x20      heather compile-x86 <file.hthr> <function> -o <output.s> [-L <dir>]... [--cache-dir <dir>] [--timings <file.tsv>] [--kernel-workers <n>]\n\
                     \x20      heather reflect <file.hthr> <function> -o <output.hthr> [-L <dir>]... [--cache-dir <dir>] [--kernel-workers <n>]\n\
                     \x20      heather write-elf <file.hthr> <program> -o <output> [-L <dir>]... [--cache-dir <dir>] [--accept-stale-images] [--world <dir>]";

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
    /// `--json`: structured output for inspection subcommands.
    json: bool,
    /// Fail a check when any proved/computing declaration reaches a user
    /// axiom. The axiom declaration itself is an explicit policy input, not a
    /// violation until something depends on it.
    deny_axioms: bool,
    /// `--review`: the review-mode lints too (a second elaboration per
    /// written match motive), off for an ordinary check.
    review: bool,
    /// `--only a,b,mod::c`: elaborate and kernel-check exactly these
    /// declarations over a replayed prefix, publish nothing, and label the
    /// run so its numbers cannot pass for a whole-run's
    /// (`docs/check-only-design.md`). Needs `--cache`.
    only: Option<Vec<String>>,
    /// `--timings <path.tsv>` (`-` for stderr), or `HEATHER_TIMINGS` in the
    /// environment: write the attribution table — one row per declaration, per
    /// module and for the run (`docs/instrumentation-design.md` §4).
    /// Diagnostic only; it can never change a verdict.
    timings: Option<stats::Dest>,
    /// `--accept-stale-images`: replay semantic module images another build
    /// of this compiler wrote (kernel-rechecked, reported per module) instead
    /// of rebuilding them. The inner-loop policy after editing the compiler's
    /// own sources; a final verification runs without it.
    images: ImageFreshness,
    /// `--kernel-workers N` (or `HEATHER_KERNEL_WORKERS`): check declarations'
    /// proofs on N kernel worker threads, joined before the module is accepted
    /// (`docs/parallel-kernel-gate-design.md`). 1 is exactly the serial gate.
    kernel_workers: Option<usize>,
    /// `--expectations`: read `// expect-error…` directives, so a declaration
    /// they mark must be refused for the reason they name, and is then not
    /// an error (`expect.rs`). Off, a directive is a comment.
    expectations: bool,
    /// `--world <dir>`: accepted and ignored. It loaded the library's shared
    /// modules in one order before each root's own, so that the gate's
    /// processes keyed each module alike; a module is now checked over its
    /// own closure in every process (`docs/module-dag-design.md`).
    #[allow(dead_code)]
    world: Option<PathBuf>,
    /// `--build-jobs N`: before checking, elaborate every module of the load
    /// that has no image yet, each in a `heather check` of its own, up to N
    /// at a time, a module once its closure's images exist and the longest
    /// chain first (`docs/module-dag-design.md` §12). Each process spends
    /// its own CPU rail on its own module; the check that follows replays.
    build_jobs: Option<usize>,
    /// `--build-only`: stop after `--build-jobs`' builds.
    build_only: bool,
    /// `--build-times <file.tsv>`: a row per module `--build-jobs` built,
    /// with when it became ready, started and finished and the import that
    /// readied it, so the chain that set the build step's length can be
    /// read back (`docs/module-dag-design.md` §12).
    build_times: Option<PathBuf>,
    /// `--build-first <dir>`: among modules ready to build, those below a
    /// named directory and their closures start before the rest, so a
    /// reader waiting on that folder's images (the test runner's native
    /// gates) is released while the rest of the step still runs.
    build_first: Vec<PathBuf>,
    /// `--unbuilt`: name the modules of the load that have no image yet,
    /// one per line, and exit 1 when there are any; nothing is elaborated
    /// (the plan `--build-jobs` schedules from, [`BuildPlan`]). The test
    /// runner asks it when a target may start reading the gate's store.
    ///
    /// [`BuildPlan`]: heather_cli::semantic::BuildPlan
    unbuilt: bool,
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
        deny_axioms: false,
        review: false,
        only: None,
        timings: stats::Dest::from_env(),
        images: ImageFreshness::Exact,
        kernel_workers: None,
        expectations: false,
        world: None,
        build_jobs: None,
        build_only: false,
        build_times: None,
        build_first: Vec::new(),
        unbuilt: false,
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
        if a == "--accept-stale-images" {
            opts.cache = true;
            opts.images = ImageFreshness::AcceptStale;
            continue;
        }
        if let Some(rest) = a.strip_prefix("--kernel-workers") {
            let spec = match rest.strip_prefix('=') {
                Some(n) if !n.is_empty() => n.to_string(),
                _ if rest.is_empty() => {
                    it.next().ok_or("`--kernel-workers` needs a count")?.clone()
                }
                _ => return Err(format!("unknown option `{a}`")),
            };
            let n: usize = spec
                .parse()
                .map_err(|_| "`--kernel-workers` needs a positive integer".to_string())?;
            if n == 0 {
                return Err("`--kernel-workers` needs a positive integer".into());
            }
            opts.kernel_workers = Some(n);
            continue;
        }
        if a == "--deny-axioms" {
            opts.deny_axioms = true;
            continue;
        }
        if a == "--review" {
            opts.review = true;
            continue;
        }
        if let Some(rest) = a.strip_prefix("--world") {
            let dir = match rest.strip_prefix('=') {
                Some(d) if !d.is_empty() => d.to_string(),
                _ if rest.is_empty() => it.next().ok_or("`--world` needs a directory")?.clone(),
                _ => return Err(format!("unknown option `{a}`")),
            };
            opts.world = Some(PathBuf::from(dir));
            continue;
        }
        if a == "--expectations" {
            opts.expectations = true;
            continue;
        }
        if let Some(rest) = a.strip_prefix("--build-jobs") {
            let spec = match rest.strip_prefix('=') {
                Some(n) if !n.is_empty() => n.to_string(),
                _ if rest.is_empty() => it.next().ok_or("`--build-jobs` needs a count")?.clone(),
                _ => return Err(format!("unknown option `{a}`")),
            };
            match spec.parse::<usize>() {
                Ok(n) if n > 0 => opts.build_jobs = Some(n),
                _ => return Err("`--build-jobs` needs a positive integer".into()),
            }
            continue;
        }
        if a == "--build-only" {
            opts.build_only = true;
            continue;
        }
        if a == "--build-first" {
            opts.build_first.push(PathBuf::from(it.next().ok_or("`--build-first` needs a directory")?));
            continue;
        }
        if a == "--build-times" {
            opts.build_times = Some(PathBuf::from(it.next().ok_or("`--build-times` needs a file")?));
            continue;
        }
        if a == "--unbuilt" {
            opts.unbuilt = true;
            continue;
        }
        if let Some(rest) = a.strip_prefix("--only") {
            let spec = match rest.strip_prefix('=') {
                Some(d) if !d.is_empty() => d.to_string(),
                _ if rest.is_empty() => it.next().ok_or("`--only` needs a declaration name")?.clone(),
                _ => return Err(format!("unknown option `{a}`")),
            };
            let names: Vec<String> = spec.split(',').map(str::trim).filter(|n| !n.is_empty()).map(String::from).collect();
            if names.is_empty() {
                return Err("`--only` needs a declaration name".into());
            }
            opts.only.get_or_insert_with(Vec::new).extend(names);
            continue;
        }
        // `--item-timings` is the spelling the native commands grew
        // first; it is the same flag and writes the same table.
        if let Some(rest) = a.strip_prefix("--timings").or_else(|| a.strip_prefix("--item-timings"))
        {
            let spec = match rest.strip_prefix('=') {
                Some(d) if !d.is_empty() => d.to_string(),
                _ if rest.is_empty() => it.next().ok_or("`--timings` needs a file")?.clone(),
                _ => return Err(format!("unknown option `{a}`")),
            };
            opts.timings = Some(stats::Dest::parse(&spec));
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
    // The standard library, then the rest of `lib/` (the native compiler,
    // certgen), as the native builder and the editor search: modules there
    // import each other across folders. The lint profile keys on `lib/std`
    // alone.
    if opts.search.is_empty() {
        for dir in [DEFAULT_LIB, DEFAULT_LIB_ROOT] {
            if Path::new(dir).is_dir() {
                opts.search.push(PathBuf::from(dir));
            }
        }
    }
    if opts.build_jobs.is_some() && !opts.cache {
        return Err("`--build-jobs` builds module images: pass `--cache` (or `--cache-dir`)".into());
    }
    if opts.unbuilt && !opts.cache {
        return Err("`--unbuilt` reads module images: pass `--cache` (or `--cache-dir`)".into());
    }
    if opts.unbuilt && opts.build_jobs.is_some() {
        return Err("`--unbuilt` builds nothing: drop `--build-jobs`".into());
    }
    if opts.build_only && opts.build_jobs.is_none() {
        return Err("`--build-only` needs `--build-jobs`".into());
    }
    if (opts.build_times.is_some() || !opts.build_first.is_empty()) && opts.build_jobs.is_none() {
        return Err("`--build-times` and `--build-first` need `--build-jobs`".into());
    }
    if opts.only.is_some() && !opts.cache {
        return Err("`--only` replays the rest of the module from the cache: pass `--cache` (or `--cache-dir`)".into());
    }
    Ok((opts, files))
}

fn check(opts: &Opts, files: &[String]) -> ExitCode {
    if opts.unbuilt {
        return unbuilt(opts, files);
    }
    let stderr_color = color::stderr_enabled();
    let stdout_color = color::stdout_enabled();
    if opts.timings.is_some() {
        stats::enable();
    }
    // A file table is live: a run killed at the CPU rail leaves the rows of
    // every scope that closed, and the scopes still open beside them.
    if let Some(stats::Dest::File(path)) = &opts.timings
        && let Err(e) = stats::live_table(path)
    {
        eprintln!("timings: could not write: {e}");
    }
    // A `--only` run's row is labelled, so `scripts/timings` can refuse to
    // read its numbers as a whole run's (`docs/check-only-design.md` §3).
    let run_label = opts.only.as_ref().map(|names| format!("only={}", names.join(","))).unwrap_or_default();
    let run_scope = opts.timings.as_ref().map(|_| stats::scope(stats::ScopeKind::Run, "", &run_label));
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
        elab.set_review_lints(opts.review);
        elab.set_kernel_workers(
            opts.kernel_workers
                .or_else(heather_elab::kernel_workers_from_env)
                .unwrap_or(heather_elab::DEFAULT_KERNEL_WORKERS),
        );
        // After the prelude, deliberately: the prelude is elaborated inside
        // `with_prelude` and is milliseconds, so it is hashed but never
        // cached (docs/cache-v1-design.md §4).
        let before = cache.as_ref().map(|c| {
            // Each root is a fresh Ψ, so the cache's view of it restarts too;
            // the recorded entries, being content-addressed, do not.
            c.begin_run();
            let store = Rc::clone(c) as Rc<dyn heather_elab::gate::KernelGate>;
            // `--only`: the named declarations face the kernel every time
            // and the store never learns that they passed.
            let gate: Rc<dyn heather_elab::gate::KernelGate> = match &opts.only {
                Some(names) => Rc::new(heather_elab::gate::Except::new(
                    store,
                    names.iter().map(|n| n.rsplit("::").next().unwrap_or(n).to_string()).collect(),
                )),
                None => store,
            };
            elab.set_gate(gate);
            c.counts()
        });
        let root_path = Path::new(path);
        let search = search_for_path(root_path, &opts.search);
        let roots = match roots_for_path(root_path, &search) {
            Ok(roots) => roots,
            Err(msg) => {
                eprintln!("{}: {msg}", color::error_label(stderr_color));
                return ExitCode::from(2);
            }
        };
        let root_refs = roots.iter().map(PathBuf::as_path).collect::<Vec<_>>();
        // Every module is checked over its own import closure
        // (`docs/module-dag-design.md`), so the closure is all a check loads:
        // `--world` no longer changes what a module means or how its image is
        // keyed, and is accepted for the callers that still pass it.
        let loaded = loader::load_many(&root_refs, &search);
        let modules = match loaded {
            Ok(m) => m,
            Err(e) => {
                eprintln!("{}: {}", color::error_label(stderr_color), e.msg);
                return ExitCode::from(2);
            }
        };
        if let Some(jobs) = opts.build_jobs {
            build_ahead(opts, &search, modules.clone(), jobs);
            if opts.build_only {
                continue;
            }
        }
        let mut root_ok = true;
        // `--only`'s names, per module: `mod::name` names a module of the
        // closure, any other name the root module. Module names are stems,
        // so the module is the first segment, and only when the closure has
        // one by that name: `nat::Nat::add_comm` is nat's `Nat::add_comm`,
        // and a bare `Nat::add_comm` is the root's.
        let only: std::collections::BTreeMap<String, std::collections::BTreeSet<String>> = opts
            .only
            .iter()
            .flatten()
            .map(|spec| match spec.split_once("::") {
                Some((module, name)) if modules.iter().any(|m| m.name == module) => {
                    (module.to_string(), name.to_string())
                }
                _ => (modules.last().map(|m| m.name.clone()).unwrap_or_default(), spec.clone()),
            })
            .fold(Default::default(), |mut map, (module, name)| {
                map.entry(module).or_default().insert(name);
                map
            });
        let mut semantic = SemanticSession::new(opts.cache.then(|| opts.cache_dir.clone()))
            .with_freshness(opts.images)
            .with_only(only);
        // Only `--deny-axioms` reads the checked world back.
        if !opts.deny_axioms {
            semantic = semantic.without_process_world();
        }
        if opts.expectations {
            semantic = semantic.with_expectations();
        }
        let mut forced_items = 0;
        let mut refusals_matched = 0;
        // `HEATHER_VALUE_METRICS`: print the kernel's value-machine counters
        // per module (meaningful with the `value-metrics` feature; zeros
        // otherwise). Observational only — it cannot change a verdict.
        let report_metrics = std::env::var_os("HEATHER_VALUE_METRICS").is_some();
        if report_metrics {
            // The collector pins the kernel gate to this thread
            // (`docs/parallel-kernel-gate-design.md` §4), so asking for both
            // it and a worker pool silently yields the serial gate. Say which
            // one won rather than leaving the flag looking honoured.
            if elab.kernel_workers() > 1 {
                eprintln!(
                    "HEATHER_VALUE_METRICS with --kernel-workers {}: the kernel gate stays serial",
                    elab.kernel_workers(),
                );
            }
            elab.enable_value_metrics();
        }
        // In the loader's order, except that a module another process is
        // building is set aside while one whose imports are checked can go
        // first (`docs/module-dag-design.md` §7): the library gate's
        // children share one store, and without this one waits on another's
        // build lock with modules of its own ready.
        let imports: Vec<Vec<String>> = modules.iter().map(|m| heather_cli::semantic::written_imports(&m.src)).collect();
        // What each module still to come needs, so a finished module's world
        // goes once nothing left imports it (`docs/module-dag-design.md` §8).
        semantic.expect_load(modules.iter().zip(&imports).map(|(m, i)| (m.name.as_str(), i.as_slice())));
        let position: std::collections::HashMap<&str, usize> =
            modules.iter().enumerate().map(|(i, m)| (m.name.as_str(), i)).collect();
        let mut checked = vec![false; modules.len()];
        let mut pending: Vec<usize> = (0..modules.len()).collect();
        while !pending.is_empty() {
            let ready = |i: usize, checked: &[bool]| {
                imports[i].iter().all(|d| position.get(d.as_str()).is_none_or(|&j| checked[j]))
            };
            let pick = pending
                .iter()
                .position(|&i| ready(i, &checked) && !semantic.built_elsewhere(&modules[i], &imports[i], modules[i].lint_profile()))
                .or_else(|| pending.iter().position(|&i| ready(i, &checked)))
                .unwrap_or(0);
            let i = pending.remove(pick);
            checked[i] = true;
            let m = &modules[i];
            elab.reset_value_metrics();
            let outcome = semantic.check(&mut elab, m, m.lint_profile());
            if report_metrics {
                if let Some(snapshot) = elab.value_metrics() {
                    eprintln!("value metrics {}: {snapshot:?}", display_path(&m.path, path));
                }
                // The typing seam's conversion-miss table for this module
                // (non-empty only under the `value-metrics` feature). A
                // replayed import records nothing, so with `--cache` the
                // excerpts are the root module's own.
                if let Some(report) = elab.value_conv_miss_report().filter(|r| !r.is_empty()) {
                    eprint!("{report}");
                }
            }
            for notice in &outcome.notices {
                eprintln!("{notice}");
            }
            forced_items += outcome.forced_items;
            // A module refused for its import's failure is not checked, and
            // not reported as ok; the error was that import's, shown with it.
            if semantic.blocked_by_import(&m.name) {
                root_ok = false;
                failed = true;
                continue;
            }
            let mut hint = None;
            let errs = if outcome.expected_refusals > 0 {
                // Judged by the session, which published the module with them.
                refusals_matched += outcome.expected_refusals;
                outcome.errors
            } else if opts.expectations {
                let verdict = expect::judge(&m.src, outcome.errors);
                refusals_matched += verdict.matched;
                verdict.errors
            } else {
                let n = expect::count(&m.src);
                if n > 0 && !outcome.errors.is_empty() {
                    hint = Some(n);
                }
                outcome.errors
            };
            // Warnings are drained per module, before the next one is checked:
            // a span indexes into the source it came from
            // (docs/diagnostic-warnings-design.md §3). They do not fail the
            // run and they do not touch the `ok` line — a warned file is a
            // checked file (§4).
            let warns = outcome.warnings;
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
            // One source span elaborated for several declarations reports its
            // error once per declaration: a `section` head binder is spliced
            // into every member (docs/sections-design.md §5.3), a class field's
            // type into every projection. Identical renderings are shown once,
            // with their count.
            let mut distinct: Vec<(String, usize)> = Vec::new();
            for e in &errs {
                let text = e.render_snippet(&m.src, &shown);
                match distinct.iter_mut().find(|(t, _)| *t == text) {
                    Some((_, k)) => *k += 1,
                    None => distinct.push((text, 1)),
                }
            }
            for (i, (text, k)) in distinct.iter().enumerate() {
                if i > 0 {
                    eprintln!();
                }
                eprint!("{}", color::diagnostic(text, color::Severity::Error, stderr_color));
                if *k > 1 {
                    eprintln!("  = this error was reported {k} times at this span, once per declaration elaborating it");
                }
            }
            let n = distinct.len();
            let count = format!("{n} error{}", if n == 1 { "" } else { "s" });
            eprintln!("\n{shown}: {}", color::error_count(&count, stderr_color));
            if let Some(n) = hint {
                eprintln!(
                    "{shown}: {n} `// expect-error` directive{} here; `heather check --expectations` reads them",
                    if n == 1 { "" } else { "s" },
                );
            }
        }
        if root_ok && opts.only.is_some() {
            let unmet = semantic.only_unmet();
            if !unmet.is_empty() {
                root_ok = false;
                failed = true;
                eprintln!(
                    "{}: --only named {} that no module of the closure declares",
                    color::error_label(stderr_color),
                    unmet.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", "),
                );
            }
        }
        if root_ok && opts.deny_axioms {
            let violations = elab.axiom_violations();
            if !violations.is_empty() {
                root_ok = false;
                failed = true;
                for report in violations {
                    let names = report
                        .axioms
                        .iter()
                        .map(|a| a.axiom.as_str())
                        .collect::<Vec<_>>()
                        .join(", ");
                    eprintln!(
                        "{}: `{}` depends on forbidden axiom{} {names}",
                        color::error_label(stderr_color),
                        report.target,
                        if report.axioms.len() == 1 { "" } else { "s" },
                    );
                }
            }
        }
        // A green line that leaned on directives says how many refusals it
        // matched, so it never reads like a file where everything checked.
        let refusals = match refusals_matched {
            0 => String::new(),
            n => format!(", {n} expected refusal{} matched", if n == 1 { "" } else { "s" }),
        };
        if root_ok && opts.only.is_some() {
            // Reserved wording, like `(cache)`: a `--only` run never reads
            // as a check of the module (`docs/check-only-design.md` §3).
            println!(
                "{path}: {} (only) — {} declaration{} elaborated for --only, {} replayed{refusals}",
                color::success("ok", stdout_color),
                forced_items,
                if forced_items == 1 { "" } else { "s" },
                semantic.replayed_items(),
            );
        } else if root_ok {
            match (&cache, before) {
                // The bare `ok` is reserved for a full check, so a green line
                // from a cached run can never be mistaken for one — and a gate
                // can mechanically demand the absence of `(cache)`.
                (Some(c), Some(before)) => {
                    let n = c.counts().since(&before);
                    // Modules moved onto a changed world are replays too,
                    // and said so only when there are any
                    // (`docs/module-interface-cutoff-design.md`).
                    let relocated = match semantic.relocated() {
                        0 => String::new(),
                        k => format!(" ({k} moved onto a changed dependency world)"),
                    };
                    // A replay a stored verdict vouched for whole asked
                    // nothing about its declarations
                    // (`docs/module-dag-design.md` §13).
                    let relocated = match n.replay_hits {
                        0 => relocated,
                        k => format!("{relocated} ({k} vouched for whole)"),
                    };
                    println!(
                        "{path}: {} (cache) — {} declaration{} kernel-checked, {} accepted \
                         from cache, {} semantic module{} replayed{relocated}, {} declaration{} \
                         replayed after an edit{refusals}",
                        color::success("ok", stdout_color),
                        n.checked,
                        if n.checked == 1 { "" } else { "s" },
                        n.hits,
                        semantic.hits(),
                        if semantic.hits() == 1 { "" } else { "s" },
                        semantic.replayed_items(),
                        if semantic.replayed_items() == 1 { "" } else { "s" },
                    );
                }
                _ if refusals_matched > 0 => println!(
                    "{path}: {} — {}",
                    color::success("ok", stdout_color),
                    &refusals[2..],
                ),
                _ => println!("{path}: {}", color::success("ok", stdout_color)),
            }
        }
    }
    // Dumped before the cache is saved, and unconditionally: a run that ends
    // in diagnostics is exactly when attribution is consulted.
    drop(run_scope);
    if let Some(dest) = &opts.timings
        && let Err(e) = stats::dump(dest, &stats::take_rows())
    {
        eprintln!("timings: could not write: {e}");
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

/// Populate an elaborator for a read-only inspection command. These commands
/// deliberately do not use the declaration cache's trusted quick gate: a
/// semantic module hit is decoded, kernel-checked and replayed exactly as it
/// is for `check`, while a miss takes the ordinary source path and publishes
/// the resulting image for the next inspection.
fn check_inspection_modules(
    opts: &Opts,
    elab: &mut Elaborator,
    modules: &[loader::Module],
) -> Result<(), (usize, Vec<heather_elab::ElabError>)> {
    let mut semantic = SemanticSession::new(opts.cache.then(|| opts.cache_dir.clone()))
        .with_freshness(opts.images);
    for (i, m) in modules.iter().enumerate() {
        let outcome = semantic.check(elab, m, m.lint_profile());
        for notice in &outcome.notices {
            eprintln!("{notice}");
        }
        if !outcome.errors.is_empty() {
            return Err((i, outcome.errors));
        }
        // Inspection commands have historically omitted warnings. The shared
        // session has already drained them at their source boundary.
    }
    Ok(())
}

/// `heather axioms <target> [--json] <root>` checks the import closure and
/// reports the deterministic shortest path from `target` to every assumption.
fn axioms(opts: &Opts, target: &str, files: &[String]) -> ExitCode {
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
        let root_path = Path::new(path);
        let search = search_for_path(root_path, &opts.search);
        let roots = match roots_for_path(root_path, &search) {
            Ok(roots) => roots,
            Err(msg) => {
                eprintln!("{}: {msg}", color::error_label(stderr_color));
                return ExitCode::from(2);
            }
        };
        let root_refs = roots.iter().map(PathBuf::as_path).collect::<Vec<_>>();
        let modules = match loader::load_many(&root_refs, &search) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("{}: {}", color::error_label(stderr_color), e.msg);
                return ExitCode::from(2);
            }
        };
        if let Err((module, errs)) =
            check_inspection_modules(opts, &mut elab, &modules)
        {
            let m = &modules[module];
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
            eprintln!("\n{shown}: not checked, so there is no axiom report");
            return ExitCode::from(1);
        }
        let report = match elab.axiom_report(target) {
            Ok(r) => r,
            Err(msg) => {
                eprintln!("{}: {msg}", color::error_label(stderr_color));
                return ExitCode::from(1);
            }
        };
        if opts.json {
            println!("{{");
            println!("  \"target\": {},", json_str(&report.target));
            println!("  \"is_axiom\": {},", report.is_axiom);
            println!(
                "  \"direct\": [{}],",
                report.direct.iter().map(|s| json_str(s)).collect::<Vec<_>>().join(", ")
            );
            println!("  \"axioms\": [");
            for (i, a) in report.axioms.iter().enumerate() {
                let path = a.path.iter().map(|s| json_str(s)).collect::<Vec<_>>().join(", ");
                println!(
                    "    {{\"name\": {}, \"kind\": {}, \"path\": [{}]}}{}",
                    json_str(&a.axiom),
                    json_str(a.kind.as_str()),
                    path,
                    if i + 1 == report.axioms.len() { "" } else { "," }
                );
            }
            println!("  ]");
            println!("}}");
        } else if report.axioms.is_empty() {
            println!("{}: no axioms", report.target);
        } else {
            println!("{}:", report.target);
            for a in &report.axioms {
                println!("  {} ({})", a.axiom, a.kind.as_str());
                println!("    {}", a.path.join(" -> "));
            }
        }
    }
    ExitCode::from(0)
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
        if let Err((module, errs)) =
            check_inspection_modules(opts, &mut elab, &modules)
        {
            let m = &modules[module];
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

/// A file is one root. A directory is the deterministic set of modules it
/// can name: its own `.hthr` files, and every file in a folder below it
/// (dot-folders aside, as in the loader's lower tier) whose stem no search
/// directory answers itself. Such a file is exactly what `import <stem>` from
/// the directory reaches, so the library keeps its modules in folders and
/// `heather check lib/std` still checks all of them. A nested file shadowed by
/// a search directory's own (a private `shadow/base.hthr` under a public
/// `base.hthr`) is no root: no import from outside can name it.
fn roots_for_path(path: &Path, search: &[PathBuf]) -> Result<Vec<PathBuf>, String> {
    if !path.is_dir() {
        return Ok(vec![path.to_path_buf()]);
    }
    let mut roots = hthr_files(path)?;
    let answered = |stem: &std::ffi::OsStr| {
        search.iter().any(|dir| dir.join(stem).with_extension("hthr").is_file())
    };
    let mut pending = child_dirs(path)?;
    while let Some(dir) = pending.pop() {
        for file in hthr_files(&dir)? {
            if !file.file_stem().is_some_and(answered) {
                roots.push(file);
            }
        }
        pending.extend(child_dirs(&dir)?);
    }
    roots.sort();
    if roots.is_empty() {
        return Err(format!("directory `{}` contains no `.hthr` files", path.display()));
    }
    Ok(roots)
}

fn hthr_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    std::fs::read_dir(dir)
        .map_err(|e| format!("cannot read directory `{}`: {e}", dir.display()))?
        .filter_map(|entry| match entry {
            Ok(entry) if entry.path().extension().is_some_and(|ext| ext == "hthr") && entry.path().is_file() => {
                Some(Ok(entry.path()))
            }
            Ok(_) => None,
            Err(e) => Some(Err(format!("cannot read directory `{}`: {e}", dir.display()))),
        })
        .collect()
}

fn child_dirs(dir: &Path) -> Result<Vec<PathBuf>, String> {
    std::fs::read_dir(dir)
        .map_err(|e| format!("cannot read directory `{}`: {e}", dir.display()))?
        .filter_map(|entry| match entry {
            Ok(entry) if entry.path().is_dir() && !entry.file_name().to_string_lossy().starts_with('.') => {
                Some(Ok(entry.path()))
            }
            Ok(_) => None,
            Err(e) => Some(Err(format!("cannot read directory `{}`: {e}", dir.display()))),
        })
        .collect()
}

/// A directory target's imports may name modules kept below it, beside the
/// roots `roots_for_path` takes from there:
/// the target joins the search directories, and the loader looks below every
/// search directory after a miss in them (so a private `shadow/base.hthr`
/// cannot shadow or conflict with the public `base.hthr`). Module names
/// remain flat: duplicate names below are still ambiguous.
/// `--build-jobs`: elaborate the modules of `modules` that have no image,
/// one `heather check` each, `jobs` at a time (`docs/module-dag-design.md`
/// §12). A module is started once every module of its closure has an image,
/// longest remaining chain first, measured in source bytes. One that fails
/// is reported with the tail of its output and leaves its dependents
/// unbuilt; the check that follows elaborates and reports them as usual.
fn build_ahead(opts: &Opts, search: &[PathBuf], modules: Vec<loader::Module>, jobs: usize) {
    use heather_cli::semantic::{BuildPlan, BuildState};
    let mut plan = BuildPlan::new(opts.cache_dir.clone(), opts.images, modules);
    let n = plan.modules().len();
    let mut dependents = vec![Vec::new(); n];
    for i in 0..n {
        for d in plan.imports(i) {
            dependents[d].push(i);
        }
    }
    // In the loader's order every importer comes after what it imports.
    let mut chain = vec![0usize; n];
    for i in (0..n).rev() {
        chain[i] = plan.modules()[i].src.len() + dependents[i].iter().map(|&d| chain[d]).max().unwrap_or(0);
    }
    // `--build-first`: the modules below a named directory, and their
    // closures (an importer comes after its imports, so walking back reaches
    // every import after its importers).
    let canon = |p: &Path| p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
    let firsts: Vec<PathBuf> = opts.build_first.iter().map(|d| canon(d)).collect();
    let mut first = vec![false; n];
    for i in (0..n).rev() {
        first[i] |= firsts.iter().any(|d| canon(&plan.modules()[i].path).starts_with(d));
        if first[i] {
            for d in plan.imports(i).collect::<Vec<_>>() {
                first[d] = true;
            }
        }
    }
    let exe = std::env::current_exe().expect("the running binary");
    let logs = std::env::temp_dir().join(format!("heather-build-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&logs);
    let mut started = vec![false; n];
    // Seconds since the step began: when each module started and finished.
    let clock = std::time::Instant::now();
    let (mut start, mut end) = (vec![None; n], vec![None::<f64>; n]);
    let mut running: Vec<(usize, std::process::Child, PathBuf)> = Vec::new();
    let (mut built, mut failed) = (0usize, Vec::new());
    loop {
        plan.refresh();
        while running.len() < jobs {
            let Some(i) = (0..n)
                .filter(|&i| !started[i] && plan.state(i) == BuildState::Ready)
                .max_by_key(|&i| (first[i], chain[i], std::cmp::Reverse(i)))
            else {
                break;
            };
            started[i] = true;
            start[i] = Some(clock.elapsed().as_secs_f64());
            let m = &plan.modules()[i];
            let log = logs.join(format!("{}.log", m.name));
            let mut cmd = std::process::Command::new(&exe);
            cmd.arg("check").arg("--cache-dir").arg(&opts.cache_dir);
            if opts.images == ImageFreshness::AcceptStale {
                cmd.arg("--accept-stale-images");
            }
            if opts.expectations {
                cmd.arg("--expectations");
            }
            for dir in search {
                cmd.arg("-L").arg(dir);
            }
            cmd.arg(&m.path);
            let out = std::fs::File::create(&log).expect("a build log");
            cmd.stdout(std::process::Stdio::null()).stderr(out);
            match cmd.spawn() {
                Ok(child) => running.push((i, child, log)),
                Err(e) => failed.push(format!("{}: could not start: {e}", m.name)),
            }
        }
        if running.is_empty() {
            break;
        }
        // No wait-any in std: poll the few children there are.
        let finished = loop {
            if let Some(k) = running.iter_mut().position(|(_, child, _)| matches!(child.try_wait(), Ok(Some(_)) | Err(_))) {
                break running.swap_remove(k);
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
        };
        let (i, mut child, log) = finished;
        let status = child.wait();
        end[i] = Some(clock.elapsed().as_secs_f64());
        if status.as_ref().is_ok_and(|s| s.success()) {
            built += 1;
        } else {
            let text = std::fs::read_to_string(&log).unwrap_or_default();
            let tail: Vec<&str> = text.lines().rev().take(12).collect();
            let status = status.map(|s| s.to_string()).unwrap_or_else(|e| e.to_string());
            failed.push(format!(
                "{} ({status}):\n{}",
                plan.modules()[i].name,
                tail.into_iter().rev().collect::<Vec<_>>().join("\n")
            ));
        }
        let _ = std::fs::remove_file(&log);
    }
    let _ = std::fs::remove_dir(&logs);
    if let Some(path) = &opts.build_times {
        // A module was ready when the last of its imports built here finished
        // (at the start if none was); the gap to its start is the wait for a
        // job. Following `readied_by` back from the last row is the chain
        // that set the step's length.
        let mut rows: Vec<usize> = (0..n).filter(|&i| end[i].is_some()).collect();
        rows.sort_by(|&a, &b| end[a].partial_cmp(&end[b]).expect("finite"));
        let mut tsv = String::from("module\tready_s\tstart_s\tend_s\twall_s\treadied_by\n");
        for i in rows {
            let by = plan.imports(i).filter(|&d| end[d].is_some()).max_by(|&a, &b| end[a].partial_cmp(&end[b]).expect("finite"));
            let ready = by.and_then(|d| end[d]).unwrap_or(0.0);
            let (s, e) = (start[i].expect("started"), end[i].expect("finished"));
            let by = by.map_or("-".to_string(), |d| plan.modules()[d].name.to_string());
            tsv.push_str(&format!("{}\t{ready:.1}\t{s:.1}\t{e:.1}\t{:.1}\t{by}\n", plan.modules()[i].name, e - s));
        }
        if let Err(e) = std::fs::write(path, tsv) {
            eprintln!("build: cannot write `{}`: {e}", path.display());
        }
    }
    for f in &failed {
        eprintln!("build: {f}");
    }
    eprintln!("build: {built} module{} built ahead, {} failed", if built == 1 { "" } else { "s" }, failed.len());
}

/// `--unbuilt`: the modules of every path's load without an image, read off
/// image headers as [`build_ahead`] plans, in the loader's order.
fn unbuilt(opts: &Opts, files: &[String]) -> ExitCode {
    use heather_cli::semantic::{BuildPlan, BuildState};
    let stderr_color = color::stderr_enabled();
    let mut missing = std::collections::BTreeSet::new();
    for path in files {
        let root_path = Path::new(path);
        let search = search_for_path(root_path, &opts.search);
        let roots = match roots_for_path(root_path, &search) {
            Ok(roots) => roots,
            Err(msg) => {
                eprintln!("{}: {msg}", color::error_label(stderr_color));
                return ExitCode::from(2);
            }
        };
        let root_refs = roots.iter().map(PathBuf::as_path).collect::<Vec<_>>();
        let modules = match loader::load_many(&root_refs, &search) {
            Ok(m) => m,
            Err(e) => {
                eprintln!("{}: {}", color::error_label(stderr_color), e.msg);
                return ExitCode::from(2);
            }
        };
        let plan = BuildPlan::new(opts.cache_dir.clone(), opts.images, modules);
        for (i, m) in plan.modules().iter().enumerate() {
            if plan.state(i) != BuildState::Built && missing.insert(m.name.clone()) {
                println!("{}", m.name);
            }
        }
    }
    ExitCode::from(if missing.is_empty() { 0 } else { 1 })
}

fn search_for_path(path: &Path, configured: &[PathBuf]) -> Vec<PathBuf> {
    let mut search = configured.to_vec();
    if path.is_dir() && !same_search_dir(&search, path) {
        search.push(path.to_path_buf());
    }
    search
}

fn same_search_dir(search: &[PathBuf], dir: &Path) -> bool {
    let canonical = dir.canonicalize().ok();
    search.iter().any(|existing| {
        existing.as_path() == dir
            || canonical
                .as_ref()
                .is_some_and(|dir| existing.canonicalize().is_ok_and(|existing| existing == *dir))
    })
}
