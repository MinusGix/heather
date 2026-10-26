//! The frontend benchmark suite (`issues/frontend-benchmarks.md`).
//!
//! Run it through `scripts/bench-frontend`, never directly: a deep-fuel
//! conversion is memory-superlinear (an uncapped `heather check` once reached
//! ~22 GB, CLAUDE.md), and the wrapper is where the `ulimit` lives — the same
//! discipline as `scripts/test` and `scripts/bench`.
//!
//! ```text
//! scripts/bench-frontend                      # measure and print
//! scripts/bench-frontend --check              # compare against the baseline
//! scripts/bench-frontend --save               # record a new baseline
//! scripts/bench-frontend --quick --no-heavy --filter forded
//! ```
//!
//! What the suite is for: the kernel suite guards a *cost model*, this one
//! guards **user latency** — the wait between saving a file and knowing it
//! checks — and how that wait grows with file size, meta count and generated
//! term volume. Hence three things the kernel suite does not have: absolute
//! latency budgets, a phase split (parse / elaborate / kernel gate) so a
//! regression names its layer, and the forded families, which exist to give
//! `docs/inductive-fording-lowering.md` §14.2 and §14.9 a number.
//!
//! See `docs/frontend-benchmarking.md`.

mod harness;
mod fixtures;

use std::process::Command;

use harness::{Baseline, Cfg, Report, Thresholds, Verdict};

/// 256 MiB, for the kernel suite's reason: a fixture's depth should be
/// bounded by the fixture, not by whatever `RUST_MIN_STACK` the environment
/// carries. Reserved, not committed, and `scripts/bench-frontend`'s
/// `ulimit -v` still bounds total address space.
const WORKER_STACK: usize = 256 << 20;

const BASELINE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/benches/baseline.tsv");

struct Args {
    filter: Option<String>,
    list: bool,
    quick: bool,
    save: bool,
    check: bool,
    no_heavy: bool,
    baseline: String,
}

fn usage() -> ! {
    help(2)
}

fn help(code: i32) -> ! {
    eprint!(
        "\
frontend benchmarks — run via scripts/bench-frontend

  --filter <substr>   only families whose name contains <substr>
  --list              print the family list and exit
  --quick             fewer, shorter samples (shape only, not a number to trust)
  --no-heavy          skip the cases that cost seconds (ir_v1.hthr)
  --save              write the measured run to the baseline file
  --check             compare against the baseline; exit 1 on a regression
  --baseline <path>   use another baseline file
"
    );
    std::process::exit(code)
}

fn parse_args() -> Args {
    let mut a = Args {
        filter: None,
        list: false,
        quick: false,
        save: false,
        check: false,
        no_heavy: false,
        baseline: BASELINE.to_string(),
    };
    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--filter" => a.filter = Some(it.next().unwrap_or_else(|| usage())),
            "--baseline" => a.baseline = it.next().unwrap_or_else(|| usage()),
            "--help" | "-h" => help(0),
            "--list" => a.list = true,
            "--quick" => a.quick = true,
            "--save" => a.save = true,
            "--check" => a.check = true,
            "--no-heavy" => a.no_heavy = true,
            // Cargo passes these to bench harnesses; accepted and ignored so
            // `cargo bench` works without arguments.
            "--bench" | "--nocapture" => {}
            _ => usage(),
        }
    }
    a
}

fn main() {
    let args = parse_args();
    let code = std::thread::Builder::new()
        .stack_size(WORKER_STACK)
        .spawn(move || run(args))
        .expect("worker thread")
        .join()
        .expect("worker thread panicked");
    std::process::exit(code);
}

fn run(args: Args) -> i32 {
    if args.list {
        // Listing must not build fixtures: constructing them validates every
        // generated source, which is seconds of work to print two columns.
        for (name, what) in fixtures_index() {
            println!("{name:<32} {what}");
        }
        return 0;
    }

    let mut cfg = if args.quick { Cfg::quick() } else { Cfg::default() };
    cfg.no_heavy = args.no_heavy;
    if args.quick {
        println!("(--quick: shapes only — do not record or trust these numbers)\n");
    }

    let env = describe_env();
    for (k, v) in &env {
        println!("{k:>8}  {v}");
    }
    println!();

    // Setup — source generation, prelude construction and one validating run
    // per case — happens here, so the timing loop below times nothing else.
    let families: Vec<_> = fixtures::all()
        .into_iter()
        .filter(|f| args.filter.as_ref().is_none_or(|s| f.name.contains(s)))
        .collect();
    if families.is_empty() {
        eprintln!("no families match the filter");
        return 2;
    }

    let mut reports: Vec<Report> = vec![];
    for f in families {
        let r = harness::run_family(f, &cfg);
        print!("{}", harness::render_family(&r));
        println!();
        reports.push(r);
    }
    println!("peak RSS {}\n", harness::bytes(harness::peak_rss() as f64));

    if args.save {
        let text = Baseline::render(&env, &reports);
        std::fs::write(&args.baseline, text).expect("write baseline");
        println!("baseline written to {}", args.baseline);
        if args.filter.is_some() || args.quick || args.no_heavy {
            println!(
                "WARNING: saved a partial or --quick run; the baseline is now \
                 missing families or holds untrustworthy numbers"
            );
        }
    }

    if args.check {
        return check(&args, &env, &reports);
    }
    0
}

fn check(args: &Args, env: &[(String, String)], reports: &[Report]) -> i32 {
    let Ok(text) = std::fs::read_to_string(&args.baseline) else {
        eprintln!(
            "no baseline at {} — record one with `scripts/bench-frontend --save`",
            args.baseline
        );
        return 2;
    };
    let base = Baseline::parse(&text);
    let get = |k: &str| env.iter().find(|(key, _)| key == k).map(|(_, v)| v.as_str());

    // A partial or --quick check is a weaker statement than "ok", and saying
    // so is the whole difference between a gate and a rubber stamp.
    if args.filter.is_some() || args.no_heavy {
        println!("checking a subset — families or cases outside it are not compared");
    }
    if args.quick {
        println!(
            "WARNING: --check with --quick compares numbers taken from 3 short \
             rounds; expect both false alarms and missed regressions"
        );
    }

    let mut th = Thresholds::default();
    // Absolute times only mean something for the cpu, profile and compiler
    // they were recorded under — the hostname is deliberately not consulted,
    // because it is the one env row with no bearing on speed (a machine
    // rename once turned the time half off silently,
    // issues/frontend-bench-baseline-host-string.md). Slopes are compared
    // regardless — the exponent is a property of the code — and so are
    // latency budgets and guards, which are claims about what a user waits
    // for anywhere.
    let mismatched: Vec<String> = ["cpu", "profile", "rustc"]
        .iter()
        .filter(|k| get(k) != base.env_get(k))
        .map(|k| {
            format!(
                "{k}: baseline {} vs this run {}",
                base.env_get(k).unwrap_or("?"),
                get(k).unwrap_or("?")
            )
        })
        .collect();
    th.compare_times = mismatched.is_empty();
    if !th.compare_times {
        println!(
            "baseline is not time-comparable ({}) — comparing scaling shape \
             and latency budgets only, not times; the verdict will be \
             shape-only, not ok",
            mismatched.join("; "),
        );
    }

    let diffs = harness::compare(reports, &base, &th);
    let mut regressed = 0;
    for d in &diffs {
        let tag = match d.verdict {
            Verdict::Regressed => {
                regressed += 1;
                "REGRESSED"
            }
            Verdict::Improved => "improved",
            Verdict::Untracked => "untracked",
            Verdict::Info => "where",
            Verdict::Ok => continue,
        };
        println!("{tag:>10}  {:<40} {}", d.label, d.detail);
    }
    if regressed == 0 {
        let n = diffs
            .iter()
            .filter(|d| d.verdict != Verdict::Untracked && d.verdict != Verdict::Info)
            .count();
        // "ok" is reserved for a run that compared everything it knows how
        // to compare. A run that skipped its time half says so in its
        // verdict and its exit code, so a green that checked half the gate
        // cannot be read — or scripted — as the full gate passing.
        if th.compare_times {
            println!("ok: {n} comparisons within thresholds");
            0
        } else {
            let skipped = reports.iter().map(|r| r.points.len()).sum::<usize>();
            println!(
                "shape-only: {n} comparisons within thresholds — {skipped} \
                 time comparisons skipped for a baseline env mismatch. Not a \
                 full pass; re-record with `scripts/bench-frontend --save` \
                 on this toolchain to restore the time gate."
            );
            3
        }
    } else {
        println!(
            "\n{regressed} regression(s). If the change is intended and \
             understood, re-record with `scripts/bench-frontend --save`; a \
             regression worth keeping gets an issue, per issues/README.md."
        );
        1
    }
}

/// `--list` without paying for setup. Kept beside `fixtures::all` by hand,
/// which is a duplication a test guards (`tests/frontend_bench_smoke.rs`).
fn fixtures_index() -> Vec<(&'static str, &'static str)> {
    vec![
        ("corpus/prelude", "the per-file fixed cost the CLI pays"),
        ("corpus/module-replay", "one real stdlib closure from source versus safe replay"),
        ("corpus/parse", "the parser alone over lib/*.hthr"),
        ("corpus/check-file", "lib/*.hthr end to end, with the phase split"),
        ("scale/declarations", "n independent fn+theorem pairs"),
        ("scale/image-first-ordinary", "first suffix declaration over an n-declaration image"),
        ("scale/image-first-inductive", "first inductive over an n-type image"),
        ("scale/wide-inductive", "an inductive with n constructors and its n-arm match"),
        ("scale/certified-dispatch", "an n-row certified lookup and its proofs"),
        ("forded/computed-arms", "route 2b with n constructors — §14.2's μ multiplier"),
        ("forded/occurrences", "n uses of one forded family — the per-use cost"),
        ("forded/declared-index-tags", "form A swept along the index type — §14.9"),
        // One line, and it has to stay one line: `the_list_table_names_every_family`
        // matches `("<name>"` as a substring of this file.
        ("forded/declared-index-branching", "the same at a branching index — §14.9's cliff"),
        ("indexed/arms", "route 1 with n constructors — §10.3's per-occurrence family"),
        ("inductive/isa-declaration", "an n-form instruction type with operand fields, declared"),
        ("inductive/isa-constructor-use", "four constructor values of an n-form instruction type"),
        ("inductive/isa-opcode-match", "an n-arm match from an instruction type into Nat"),
        ("inductive/isa-roundtrip", "an n-arm rebuild and its identity theorem"),
        ("inductive/enum-equality", "n²-arm decidable equality on an n-constructor enum"),
        ("inductive/record-fields", "a k-field record: literal, projection, rebuild, frame"),
        ("inductive/mutual-declaration", "a group of m mutual sorts, declared"),
        ("inductive/mutual-recursion", "structural recursion over an m-member mutual group"),
        ("inductive/typed-syntax", "intrinsically typed terms with n constructors"),
        ("inductive/function-fields", "an IWf-on-W family with n function-field constructors"),
        ("meta/nested-inference", "d nested implicit instantiations"),
        ("rewrite/fa", "g(f^n(a)) = g(a) by n rewrites — mengine rewrite_fa"),
        ("rewrite/repeat-mod", "(…(b mod p)…) mod p by n−1 rewrites — mengine repeat_mod"),
        ("rewrite/let-addr0", "every + 0 out of a k-let chain — mengine addr0_let_in"),
        ("rewrite/let-nary", "3 lets of arity n rewritten away — mengine rewrite_nm"),
        ("rewrite/setoid-let-addr0", "a k-let chain along a relation, rewritten once at its bottom"),
        ("let/fan", "k lets each using the last twice"),
        ("let/dep", "fan with an unused refl proof let per link"),
        ("let/under", "fan with a λ between every link"),
        ("let/stmt", "a k-let chain equal to itself by refl"),
    ]
}

// ---------------------------------------------------------------------------
// Environment description — what makes two runs comparable
// ---------------------------------------------------------------------------

fn describe_env() -> Vec<(String, String)> {
    let mut v = vec![];
    let mut push = |k: &str, val: String| v.push((k.to_string(), val));
    push("host", read_trim("/proc/sys/kernel/hostname").unwrap_or_else(|| "unknown".into()));
    push("cpu", cpu_model());
    push("profile", if cfg!(debug_assertions) { "debug".into() } else { "release".into() });
    push("rustc", cmd("rustc", &["--version"]));
    push("commit", cmd("git", &["rev-parse", "--short", "HEAD"]));
    v
}

fn read_trim(path: &str) -> Option<String> {
    std::fs::read_to_string(path).ok().map(|s| s.trim().to_string())
}

fn cpu_model() -> String {
    let Some(text) = read_trim("/proc/cpuinfo") else { return "unknown".into() };
    text.lines()
        .find(|l| l.starts_with("model name"))
        .and_then(|l| l.split_once(':'))
        .map(|(_, v)| v.trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}

fn cmd(prog: &str, args: &[&str]) -> String {
    Command::new(prog)
        .args(args)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}
