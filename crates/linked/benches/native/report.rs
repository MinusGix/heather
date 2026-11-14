//! The table: the release binary's times and the dev binary's, the
//! instruction counts, the compile times; and the snapshot it is recorded
//! in (`crates/linked/benches/baseline.tsv`), which `--check` compares
//! against.
//!
//! The snapshot is one measurement a line, `measure <key> <value> <unit>`,
//! under `env` lines naming where it was taken. Keys:
//! `time/<profile>/<case>` (the minimum, or the best MB/s),
//! `count/sha256/block/{instructions,calls,kind/<kind>}`,
//! `count/scanner/{linked,lexer}/per-byte`, `compile/<symbol>/{cold,warm}`.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::callgrind;
use crate::compile;
use crate::{Timed, time_all};

/// Blocks callgrind runs the compression over; the count is per block, so
/// only the sum's size depends on it.
const COUNT_BLOCKS: u64 = 200;

struct Options {
    debug_times: Option<PathBuf>,
    heather: Option<PathBuf>,
    root: PathBuf,
    work: PathBuf,
    baseline: PathBuf,
    quick: bool,
    compile: bool,
    count: bool,
    save: bool,
    check: bool,
}

fn options(args: &[String]) -> Options {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().expect("the repository");
    let mut o = Options {
        debug_times: None,
        heather: None,
        work: root.join("target/bench-native"),
        baseline: root.join("crates/linked/benches/baseline.tsv"),
        root,
        quick: false,
        compile: true,
        count: true,
        save: false,
        check: false,
    };
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--debug-times" => o.debug_times = args.next().map(PathBuf::from),
            "--heather" => o.heather = args.next().map(PathBuf::from),
            "--quick" => o.quick = true,
            "--no-compile" => o.compile = false,
            "--no-count" => o.count = false,
            "--save" => o.save = true,
            "--check" => o.check = true,
            other => {
                eprintln!("bench-native report: unknown argument {other}");
                std::process::exit(2);
            }
        }
    }
    o
}

/// The measurements, by key: value and unit.
type Measures = BTreeMap<String, (f64, String)>;

fn put(m: &mut Measures, key: String, value: f64, unit: &str) {
    m.insert(key, (value, unit.to_string()));
}

fn env() -> Vec<(&'static str, String)> {
    let cpu = std::fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("model name")).and_then(|l| l.split(':').nth(1)).map(|s| s.trim().to_string()))
        .unwrap_or_else(|| "unknown".into());
    let run = |program: &str, args: &[&str]| {
        Command::new(program).args(args).output().ok().map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string()).unwrap_or_default()
    };
    let backend = if std::is_x86_feature_detected!("sha") && std::is_x86_feature_detected!("sse4.1") { "x86 SHA extensions" } else { "soft" };
    vec![
        ("cpu", cpu),
        ("rustc", run("rustc", &["--version"])),
        ("commit", run("git", &["rev-parse", "--short=12", "HEAD"])),
        ("date", run("date", &["-u", "+%Y-%m-%d"])),
        ("sha2-backend", backend.to_string()),
    ]
}

pub fn main(args: &[String]) {
    let o = options(args);
    let _ = std::fs::create_dir_all(&o.work);
    let mut m = Measures::new();

    eprintln!("bench-native: timing the release build");
    for t in time_all(o.quick) {
        put(&mut m, format!("time/release/{}", t.case), t.min, t.unit);
        put(&mut m, format!("median/release/{}", t.case), t.median, t.unit);
    }
    if let Some(path) = &o.debug_times {
        let text = std::fs::read_to_string(path).unwrap_or_default();
        for t in text.lines().filter_map(Timed::parse) {
            put(&mut m, format!("time/debug/{}", t.case), t.min, t.unit);
            put(&mut m, format!("median/debug/{}", t.case), t.median, t.unit);
        }
    }

    if o.count && callgrind::available() {
        eprintln!("bench-native: counting instructions (callgrind)");
        if let Some(counted) = callgrind::run("sha256-block", COUNT_BLOCKS, Some("sha256_compress"), &o.work) {
            let blocks = COUNT_BLOCKS as f64;
            put(&mut m, "count/sha256/block/instructions".into(), counted.total as f64 / blocks, "instructions/block");
            if let Some((kinds, calls)) = callgrind::breakdown(&counted) {
                put(&mut m, "count/sha256/block/calls".into(), calls as f64 / blocks, "calls/block");
                for (kind, n) in kinds {
                    put(&mut m, format!("count/sha256/block/kind/{kind}"), n as f64 / blocks, "instructions/block");
                }
            }
        }
        let bytes: usize = crate::corpus().iter().map(String::len).sum();
        if let Some(reading) = callgrind::run("corpus", 0, None, &o.work) {
            for case in ["scanner", "lexer"] {
                if let Some(cut) = callgrind::run(case, 0, None, &o.work) {
                    let name = if case == "scanner" { "linked" } else { "lexer" };
                    let per = cut.total.saturating_sub(reading.total) as f64 / bytes as f64;
                    put(&mut m, format!("count/scanner/{name}/per-byte"), per, "instructions/byte");
                }
            }
        }
    }

    if o.compile {
        if let Some(heather) = &o.heather {
            let only = o.quick.then_some("sha256_compress");
            for c in compile::run(heather, &o.root, &o.work, only) {
                if let Some(cold) = c.cold {
                    put(&mut m, format!("compile/{}/cold", c.symbol), cold, "s");
                }
                if let Some(warm) = c.warm {
                    put(&mut m, format!("compile/{}/warm", c.symbol), warm, "s");
                }
            }
        }
    }

    let env = env();
    let baseline = read_baseline(&o.baseline);
    print_table(&m, &env, &o);
    let mut status = 0;
    if o.check {
        status = check(&m, &env, &baseline);
    }
    if o.save {
        if o.quick {
            eprintln!("bench-native: refusing to save a --quick run (its numbers are shapes)");
            std::process::exit(2);
        }
        save(&o.baseline, &m, &env);
        println!("\nrecorded {}", o.baseline.display());
    }
    std::process::exit(status);
}

fn get(m: &Measures, key: &str) -> Option<f64> {
    m.get(key).map(|v| v.0)
}

/// A number with thousands separated, to `digits` decimals.
fn num(v: Option<f64>, digits: usize) -> String {
    let Some(v) = v else { return "—".into() };
    let s = format!("{v:.digits$}");
    let (int, frac) = s.split_once('.').map_or((s.as_str(), ""), |(a, b)| (a, b));
    let mut grouped = String::new();
    for (i, c) in int.chars().enumerate() {
        if i > 0 && (int.len() - i) % 3 == 0 {
            grouped.push(',');
        }
        grouped.push(c);
    }
    if frac.is_empty() { grouped } else { format!("{grouped}.{frac}") }
}

const IMPLEMENTATIONS: [(&str, &str); 4] = [
    ("linked", "linked: compiled Heather"),
    ("mirror", "mirror: the Heather source's shape in Rust"),
    ("textbook", "textbook scalar Rust"),
    ("sha2", "sha2 crate"),
];

fn print_table(m: &Measures, env: &[(&str, String)], o: &Options) {
    let backend = env.iter().find(|(k, _)| *k == "sha2-backend").map(|(_, v)| v.as_str()).unwrap_or("?");
    println!();
    println!("{:<48}{:>12}{:>12}", "SHA-256 compression, ns per block (min)", "opt-level 3", "opt-level 0");
    for (key, name) in IMPLEMENTATIONS {
        let name = if key == "sha2" { format!("{name} ({backend})") } else { name.to_string() };
        let case = format!("sha256/block/{key}");
        println!("  {:<46}{:>12}{:>12}", name, num(get(m, &format!("time/release/{case}")), 0), num(get(m, &format!("time/debug/{case}")), 0));
    }
    println!("{:<48}{:>12}{:>12}", "SHA-256 stream of 1 MiB, MB/s (best)", "", "");
    for (key, name) in IMPLEMENTATIONS {
        let case = format!("sha256/stream/{key}");
        println!("  {:<46}{:>12}{:>12}", name, num(get(m, &format!("time/release/{case}")), 1), num(get(m, &format!("time/debug/{case}")), 1));
    }
    println!("  (the linked code is assembly, the same in both columns; the Rust around it is not)");

    println!();
    println!("Linked compression, counted (callgrind, {COUNT_BLOCKS} blocks)");
    let instructions = get(m, "count/sha256/block/instructions");
    match instructions {
        None => println!("  not measured (no valgrind, or --no-count)"),
        Some(total) => {
            println!("  {:<46}{:>12}", "instructions per block", num(Some(total), 0));
            println!("  {:<46}{:>12}", "calls per block", num(get(m, "count/sha256/block/calls"), 0));
            for kind in callgrind::KINDS {
                if let Some(n) = get(m, &format!("count/sha256/block/kind/{kind}")) {
                    println!("    {:<44}{:>12}{:>11.1}%", kind, num(Some(n), 0), 100.0 * n / total);
                }
            }
        }
    }

    println!();
    println!("{:<48}{:>12}{:>12}", "compile-x86, seconds (wall)", "cold", "warm");
    let compiled: Vec<&str> = m.keys().filter_map(|k| k.strip_prefix("compile/")?.strip_suffix("/cold")).collect();
    if compiled.is_empty() {
        println!("  not measured ({})", if o.compile { "no heather binary given" } else { "--no-compile" });
    }
    for symbol in compiled {
        println!("  {:<46}{:>12}{:>12}", symbol, num(get(m, &format!("compile/{symbol}/cold")), 1), num(get(m, &format!("compile/{symbol}/warm")), 1));
    }

    println!();
    println!("{:<48}{:>12}{:>12}", "Scanner over lib/**/*.hthr", "MB/s", "instr/byte");
    for (key, name) in [("linked", "linked scanner (scan_token)"), ("lexer", "heather_syntax lexer (lex_rust)")] {
        println!(
            "  {:<46}{:>12}{:>12}",
            name,
            num(get(m, &format!("time/release/scanner/lib/{key}")), 1),
            num(get(m, &format!("count/scanner/{key}/per-byte")), 1)
        );
    }
}

struct Baseline {
    env: BTreeMap<String, String>,
    measures: BTreeMap<String, f64>,
}

fn read_baseline(path: &Path) -> Option<Baseline> {
    let text = std::fs::read_to_string(path).ok()?;
    let mut b = Baseline { env: BTreeMap::new(), measures: BTreeMap::new() };
    for line in text.lines().filter(|l| !l.starts_with('#')) {
        let f: Vec<&str> = line.split('\t').collect();
        match f.as_slice() {
            ["env", key, value] => {
                b.env.insert(key.to_string(), value.to_string());
            }
            ["measure", key, value, _unit] => {
                if let Ok(v) = value.parse() {
                    b.measures.insert(key.to_string(), v);
                }
            }
            _ => {}
        }
    }
    Some(b)
}

fn save(path: &Path, m: &Measures, env: &[(&str, String)]) {
    let mut out = String::from(
        "# scripts/bench-native --save: the linked code's speed and the Rust references'.\n\
         # docs/native-benchmarking.md says how to read it and when to re-record.\n",
    );
    for (key, value) in env {
        out.push_str(&format!("env\t{key}\t{value}\n"));
    }
    for (key, (value, unit)) in m {
        if key.starts_with("median/") {
            continue;
        }
        let digits = if unit == "s" || unit == "MB/s" || unit.ends_with("/byte") { 2 } else { 0 };
        out.push_str(&format!("measure\t{key}\t{value:.digits$}\t{unit}\n"));
    }
    std::fs::write(path, out).expect("the snapshot is writable");
}

/// Exit status of `--check`: 1 when a counter moved up or a linked case got
/// at least 1.25 times slower on the snapshot's machine, 3 when the times
/// could not be compared (another cpu or rustc), 0 otherwise. Counters are
/// exact, so any move is reported; a move down is a hint to re-record.
fn check(m: &Measures, env: &[(&str, String)], baseline: &Option<Baseline>) -> i32 {
    println!();
    let Some(b) = baseline else {
        println!("check: no snapshot to compare against");
        return 3;
    };
    let mut status = 0;
    for (key, recorded) in &b.measures {
        let Some(now) = get(m, key) else { continue };
        if key.starts_with("count/") {
            let ratio = now / recorded;
            if (ratio - 1.0).abs() > 0.0005 {
                let word = if now > *recorded { "rose" } else { "fell" };
                println!("check: {key} {word}: {} → {} ({ratio:.3}×)", num(Some(*recorded), 1), num(Some(now), 1));
                if now > *recorded && (key.ends_with("/instructions") || key.ends_with("/per-byte")) {
                    status = 1;
                }
            }
        }
    }
    let same_machine = env.iter().filter(|(k, _)| *k == "cpu" || *k == "rustc").all(|(k, v)| b.env.get(*k) == Some(v));
    if !same_machine {
        println!("check: times not compared (the snapshot is from another cpu or rustc): shape-only");
        return if status == 0 { 3 } else { status };
    }
    for (key, recorded) in &b.measures {
        let Some(now) = get(m, key) else { continue };
        if !key.starts_with("time/") {
            continue;
        }
        // Slower is a larger ns/block and a smaller MB/s.
        let slower = if key.contains("/stream/") || key.contains("/scanner/") { recorded / now } else { now / recorded };
        if slower >= 1.25 {
            println!("check: {key} is {slower:.2}× slower than recorded");
            if key.ends_with("/linked") {
                status = 1;
            }
        } else if slower <= 0.8 {
            println!("check: {key} is {:.2}× faster than recorded (re-record?)", 1.0 / slower);
        }
    }
    if status == 0 {
        println!("check: ok");
    }
    status
}
