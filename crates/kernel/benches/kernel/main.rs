//! The kernel benchmark suite (`issues/kernel-benchmarks.md`).
//!
//! Run it through `scripts/bench`, never directly: benchmarks provoke exactly
//! the runaway normalizations that `ulimit` exists to contain, and the
//! wrapper is where the limits live (same discipline as `scripts/test`).
//!
//! ```text
//! scripts/bench                     # measure and print
//! scripts/bench --check             # measure and compare against the baseline
//! scripts/bench --save              # record a new baseline
//! scripts/bench --quick --filter nat
//! ```
//!
//! What the suite is for: the kernel is the trusted basis, so it stays
//! *simple*. The answer to a slow number here is almost never "make the
//! kernel cleverer" — it is to know the cost model, keep it stable, and
//! notice when it changes. Hence the reported headline is the scaling
//! exponent, not the time, and hence the baseline.
//!
//! Everything runs on a worker thread with a deliberately large stack
//! (`WORKER_STACK`), so that a fixture's depth is bounded by the fixture and
//! not by whatever `RUST_MIN_STACK` the ambient environment happens to
//! carry. The exceptions are the `stack/*` probes, which measure stack on
//! purpose, in a child process of exactly known size.

mod harness;
mod stack;

#[path = "../../tests/common/mod.rs"]
mod common;

mod fixtures;

use std::process::Command;

use harness::{Baseline, Cfg, Report, Thresholds, Verdict};

/// 256 MiB. Reserved, not committed — the pages are touched only if a walk
/// actually goes that deep, and `scripts/bench`'s `ulimit -v` still bounds
/// total address space. Sized so the deepest fixture (`nat/check-numeral` at
/// 512 `Succ` levels, ~47 KB per level today) has several times the headroom
/// it needs: a benchmark that dies of the very cost it is measuring reports
/// nothing.
const WORKER_STACK: usize = 256 << 20;

const BASELINE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/benches/baseline.tsv");

struct Args {
    filter: Option<String>,
    list: bool,
    quick: bool,
    save: bool,
    check: bool,
    stack: bool,
    stack_only: bool,
    baseline: String,
}

fn usage() -> ! {
    help(2)
}

fn help(code: i32) -> ! {
    eprint!(
        "\
kernel benchmarks — run via scripts/bench

  --filter <substr>   only families whose name contains <substr>
  --list              print the family list and exit
  --quick             fewer, shorter samples (shape only, not a number to trust)
  --save              write the measured run to the baseline file
  --check             compare against the baseline; exit 1 on a regression
  --no-stack          skip the stack probe (it spawns subprocesses)
  --stack-only        run only the stack probe (works in a debug build too,
                      where frames are several times fatter — see
                      docs/infrastructure/benchmarking.md)
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
        stack: true,
        stack_only: false,
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
            "--no-stack" => a.stack = false,
            "--stack-only" => a.stack_only = true,
            // Cargo passes these to bench harnesses; accepted and ignored so
            // `cargo bench` works without arguments.
            "--bench" | "--nocapture" => {}
            _ => usage(),
        }
    }
    a
}

fn main() {
    // The internal probe mode: this process *is* the child (see stack.rs).
    let argv: Vec<String> = std::env::args().collect();
    if argv.len() == 5 && argv[1] == "--stack-child" {
        let bytes: usize = argv[3].parse().expect("stack bytes");
        let levels: u64 = argv[4].parse().expect("levels");
        std::process::exit(stack::child_main(&argv[2], bytes, levels));
    }

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
    if args.stack_only {
        // No fixture setup: the probe is the only measurement, which is what
        // makes this mode usable in a debug build (where generating the
        // corpus would take minutes).
        for (k, v) in describe_env() {
            println!("{k:>8}  {v}");
        }
        for p in &stack::probes() {
            print_probe(p);
        }
        return 0;
    }

    let families: Vec<_> = fixtures::all()
        .into_iter()
        .filter(|f| args.filter.as_ref().is_none_or(|s| f.name.contains(s)))
        .collect();

    if args.list {
        for f in &families {
            println!("{:<32} {}", f.name, f.what);
        }
        return 0;
    }
    if families.is_empty() {
        eprintln!("no families match the filter");
        return 2;
    }

    let cfg = if args.quick { Cfg::quick() } else { Cfg::default() };
    if args.quick {
        println!("(--quick: shapes only — do not record or trust these numbers)\n");
    }

    let env = describe_env();
    for (k, v) in &env {
        println!("{k:>8}  {v}");
    }
    println!();

    let mut reports: Vec<Report> = vec![];
    for f in families {
        // Setup (term building, generation, validation) already happened, in
        // the family constructors that `fixtures::all()` ran, so this loop is
        // timing only.
        let r = harness::run_family(f, &cfg);
        print!("{}", harness::render_family(&r));
        println!();
        reports.push(r);
    }

    let probes = if args.stack && args.filter.is_none() {
        let ps = stack::probes();
        for p in &ps {
            print_probe(p);
        }
        ps
    } else {
        Vec::new()
    };

    if args.save {
        let text = Baseline::render(&env, &reports, &probes);
        std::fs::write(&args.baseline, text).expect("write baseline");
        println!("baseline written to {}", args.baseline);
        if args.filter.is_some() || args.quick {
            println!(
                "WARNING: saved a partial or --quick run; the baseline is now \
                 missing families or holds untrustworthy numbers"
            );
        }
    }

    if args.check {
        return check(&args, &env, &reports, &probes);
    }
    0
}

fn check(args: &Args, env: &[(String, String)], reports: &[Report], probes: &[stack::Probe]) -> i32 {
    let Ok(text) = std::fs::read_to_string(&args.baseline) else {
        eprintln!("no baseline at {} — record one with `scripts/bench --save`", args.baseline);
        return 2;
    };
    let base = Baseline::parse(&text);
    let get = |k: &str| env.iter().find(|(key, _)| key == k).map(|(_, v)| v.as_str());

    // A partial or --quick check is a weaker statement than "ok", and saying
    // so is the whole difference between a gate and a rubber stamp.
    if args.filter.is_some() {
        println!("checking a filtered subset — families outside the filter are not compared");
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
    // issues/frontend-bench-baseline-host-string.md). Slopes and stack frames
    // are compared regardless — they are properties of the code (and, for
    // frames, the compiler).
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
    th.compare_stack = get("rustc") == base.env_get("rustc") && get("profile") == base.env_get("profile");
    if !th.compare_times {
        println!(
            "baseline times are from another machine ({}) — times not \
             compared; the counters and slope bands still are",
            mismatched.join("; "),
        );
    }

    let diffs = harness::compare(reports, probes, &base, &th);
    let mut regressed = 0;
    for d in &diffs {
        let tag = match d.verdict {
            Verdict::Regressed => {
                regressed += 1;
                "REGRESSED"
            }
            Verdict::Slower => "slower",
            Verdict::Improved => "improved",
            Verdict::Untracked => "untracked",
            Verdict::Ok => continue,
        };
        println!("{tag:>10}  {:<40} {}", d.label, d.detail);
    }
    if regressed == 0 {
        let n = diffs.iter().filter(|d| d.verdict != Verdict::Untracked).count();
        // "ok" is reserved for a run that compared everything the gate
        // holds: every case's counters, and the stack probes. A run that
        // skipped part says so in its verdict and its exit code, so a green
        // that checked half the gate cannot be read — or scripted — as the
        // full gate passing. Times are not part of the gate, so a baseline
        // from another machine still gives a full pass.
        let uncounted = diffs.iter().filter(|d| d.verdict == Verdict::Untracked && d.label.ends_with(" counters")).count();
        let full = uncounted == 0 && (probes.is_empty() || th.compare_stack);
        if full {
            println!("ok: {n} comparisons within thresholds");
            0
        } else {
            let skipped = uncounted + if th.compare_stack { 0 } else { probes.len() };
            println!(
                "partial: {n} comparisons within thresholds — {skipped} \
                 skipped (cases with no recorded counters, or stack probes \
                 under another toolchain). Not a full pass; re-record with \
                 `scripts/bench --save` to restore the gate."
            );
            3
        }
    } else {
        println!(
            "\n{regressed} regression(s). If the change is intended and \
             understood, re-record with `scripts/bench --save`; a regression \
             worth keeping gets an issue, per issues/README.md."
        );
        1
    }
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

fn print_probe(p: &stack::Probe) {
    println!(
        "\n{}  — {} in {} of stack\n  \
         {:>10} levels   {:>10} per level\n",
        p.name,
        p.level,
        fmt_bytes(p.stack_bytes as f64),
        p.max_levels,
        fmt_bytes(p.bytes_per_level()),
    );
}

fn fmt_bytes(b: f64) -> String {
    if b < 1024.0 {
        format!("{b:.0} B")
    } else if b < (1 << 20) as f64 {
        format!("{:.1} KiB", b / 1024.0)
    } else {
        format!("{:.1} MiB", b / (1 << 20) as f64)
    }
}
