//! How fast the code our compiler emits runs, against Rust references:
//! the linked SHA-256 and the linked scanner (`crates/linked`). Run through
//! `scripts/bench-native`, never bare `cargo bench` (the script builds both
//! profiles and enters the caps); `docs/native-benchmarking.md` says how to
//! read the table and when to re-record the snapshot.
//!
//! The binary has three modes, and the script drives them:
//!
//! - `time`: every timed case of this build, one TSV row each. Built twice,
//!   at the release profile (opt-level 3) and the dev profile (opt-level 0),
//!   so the Rust references are measured at both; the linked code is
//!   assembly and the same in both.
//! - `count <case>`: the work callgrind counts, nothing else.
//! - `report`: the release binary's own times, the dev binary's (a file),
//!   the instruction counts (callgrind over `count`), the compile times
//!   (`heather compile-x86`), printed as one table; `--save` records it,
//!   `--check` compares against the record.

mod callgrind;
mod compile;
mod mirror;
mod report;
mod textbook;

use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::time::Instant;

use heather_linked::scanner::{self, Kind};
use heather_linked::sha256::{self, block, stream};

/// The message the stream cases hash: one MiB, not a multiple of the block,
/// so the padding's second block is taken too.
const STREAM_BYTES: usize = (1 << 20) + 37;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).filter(|a| a != "--bench").collect();
    let quick = args.iter().any(|a| a == "--quick");
    match args.first().map(String::as_str) {
        Some("time") => {
            for row in time_all(quick) {
                println!("{}", row.tsv());
            }
        }
        Some("count") => count(args.get(1).map(String::as_str).unwrap_or(""), args.get(2).and_then(|n| n.parse().ok()).unwrap_or(200)),
        Some("report") => report::main(&args[1..]),
        _ => {
            eprintln!("usage: scripts/bench-native [--quick] [--no-compile] [--no-count] [--save | --check]");
            std::process::exit(2);
        }
    }
}

/// One measured case: `min` and `median` of the samples, in `unit`.
pub struct Timed {
    pub case: String,
    pub min: f64,
    pub median: f64,
    pub unit: &'static str,
}

impl Timed {
    fn tsv(&self) -> String {
        format!("{}\t{:.3}\t{:.3}\t{}", self.case, self.min, self.median, self.unit)
    }

    pub fn parse(line: &str) -> Option<Timed> {
        let mut f = line.split('\t');
        let case = f.next()?.to_string();
        let min = f.next()?.parse().ok()?;
        let median = f.next()?.parse().ok()?;
        let unit = match f.next()? {
            "ns/block" => "ns/block",
            "MB/s" => "MB/s",
            _ => return None,
        };
        Some(Timed { case, min, median, unit })
    }
}

/// Nanoseconds per unit of `work`, which does `units` units a call: the
/// minimum and the median over samples of at least a fixed time each. The
/// minimum is the statistic for deterministic work (docs/benchmarking.md).
fn ns_per_unit(units: f64, quick: bool, mut work: impl FnMut()) -> (f64, f64) {
    let target = if quick { 0.005 } else { 0.03 };
    let samples = if quick { 3 } else { 15 };
    let started = Instant::now();
    work();
    let once = started.elapsed().as_secs_f64().max(1e-7);
    let reps = ((target / once).ceil() as usize).max(1);
    let mut per: Vec<f64> = (0..samples)
        .map(|_| {
            let started = Instant::now();
            for _ in 0..reps {
                work();
            }
            started.elapsed().as_secs_f64() * 1e9 / (reps as f64 * units)
        })
        .collect();
    per.sort_by(|a, b| a.total_cmp(b));
    (per[0], per[per.len() / 2])
}

fn blocks_case(case: &str, quick: bool, work: impl FnMut()) -> Timed {
    let (min, median) = ns_per_unit(1.0, quick, work);
    Timed { case: case.to_string(), min, median, unit: "ns/block" }
}

/// MB/s, best and median, from ns per byte.
fn bytes_case(case: &str, bytes: usize, quick: bool, work: impl FnMut()) -> Timed {
    let (min, median) = ns_per_unit(bytes as f64, quick, work);
    Timed { case: case.to_string(), min: 1e3 / min, median: 1e3 / median, unit: "MB/s" }
}

/// Bytes that are not all alike: a fixed generator, so every run hashes the
/// same message.
fn message(n: usize) -> Vec<u8> {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x as u8
        })
        .collect()
}

fn sha2_digest(message: &[u8]) -> [u8; 32] {
    use sha2::Digest;
    sha2::Sha256::digest(message).into()
}

fn mirror_digest(message: &[u8]) -> [u8; 32] {
    let mut context = [0u8; block::CONTEXT];
    let mut s = mirror::Sha256::over(&mut context);
    s.init();
    s.update(message);
    s.finish();
    context[block::HASH..block::HASH + 32].try_into().expect("thirty-two bytes")
}

/// The fixture rule (docs/benchmarking.md): a case that stops doing its work
/// gets faster, so every case is held to an independent answer before it is
/// timed. The mirror is held to the linked code byte for byte, the whole
/// context after each exported function, which is what says it is the same
/// algorithm over the same layout and not only the same hash.
fn check() {
    for n in [0usize, 1, 55, 56, 63, 64, 65, 119, 120, 1000] {
        let m = message(n);
        let expected = sha2_digest(&m);
        assert_eq!(stream::digest(&m), expected, "linked stream at {n} bytes");
        assert_eq!(mirror_digest(&m), expected, "mirror at {n} bytes");
        assert_eq!(textbook::digest(&m), expected, "textbook at {n} bytes");
        assert_eq!(sha256::block::digest(&m), expected, "linked compression at {n} bytes");

        let mut linked = [0u8; block::CONTEXT];
        let mut mirrored = [0u8; block::CONTEXT];
        stream::spans::init(&mut linked);
        mirror::Sha256::over(&mut mirrored).init();
        assert_eq!(linked, mirrored, "context after init");
        for part in m.chunks(41) {
            stream::spans::update(&mut linked, part);
            mirror::Sha256::over(&mut mirrored).update(part);
            assert_eq!(linked, mirrored, "context after update, {n} bytes");
        }
        stream::spans::finish(&mut linked);
        mirror::Sha256::over(&mut mirrored).finish();
        assert_eq!(linked, mirrored, "context after finish, {n} bytes");
    }
    let one = message(64);
    let mut linked = [0u8; block::CONTEXT];
    let mut mirrored = [0u8; block::CONTEXT];
    stream::spans::init(&mut linked);
    stream::spans::init(&mut mirrored);
    block::compress_spans(&mut linked, &one);
    mirror::Sha256::over(&mut mirrored).compress(&one);
    assert_eq!(linked, mirrored, "context after compress");
}

/// The Heather sources the scanner cases cut: every `lib/**/*.hthr`.
pub fn corpus() -> Vec<String> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let mut entries: Vec<_> = std::fs::read_dir(dir).expect("lib/ is readable").map(|e| e.expect("an entry").path()).collect();
        entries.sort();
        for path in entries {
            if path.is_dir() {
                walk(&path, out);
            } else if path.extension().is_some_and(|e| e == "hthr") {
                out.push(path);
            }
        }
    }
    let mut paths = Vec::new();
    walk(&Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lib"), &mut paths);
    paths.iter().map(|p| std::fs::read_to_string(p).expect("a source")).collect()
}

/// Tokens the linked scanner cuts from every source, whitespace and
/// comments included; a refusal ends that source.
fn scan_all(corpus: &[String]) -> usize {
    let mut tokens = 0;
    for source in corpus {
        for token in scanner::Scanner::new(source.as_bytes()) {
            match token {
                Ok(t) if t.kind != Kind::Eof => tokens += 1,
                _ => {}
            }
        }
    }
    tokens
}

fn lex_all(corpus: &[String]) -> usize {
    corpus.iter().map(|s| heather_syntax::lexer::lex_rust(s).map_or(0, |t| t.len())).sum()
}

fn time_all(quick: bool) -> Vec<Timed> {
    check();
    let mut rows = Vec::new();

    let one = message(64);
    let block_array: [u8; 64] = one.as_slice().try_into().expect("a block");
    let mut context = [0u8; block::CONTEXT];
    stream::spans::init(&mut context);
    rows.push(blocks_case("sha256/block/linked", quick, || {
        black_box(block::compress_spans(black_box(&mut context), black_box(&one)));
    }));
    rows.push(blocks_case("sha256/block/mirror", quick, || {
        black_box(mirror::Sha256::over(black_box(&mut context)).compress(black_box(&one)));
    }));
    let mut hash = sha256::INITIAL;
    rows.push(blocks_case("sha256/block/textbook", quick, || {
        textbook::compress(black_box(&mut hash), black_box(&block_array));
    }));
    let generic = sha2::digest::generic_array::GenericArray::clone_from_slice(&one);
    rows.push(blocks_case("sha256/block/sha2", quick, || {
        sha2::compress256(black_box(&mut hash), std::slice::from_ref(black_box(&generic)));
    }));

    let m = message(STREAM_BYTES);
    rows.push(bytes_case("sha256/stream/linked", m.len(), quick, || {
        black_box(stream::digest(black_box(&m)));
    }));
    rows.push(bytes_case("sha256/stream/mirror", m.len(), quick, || {
        black_box(mirror_digest(black_box(&m)));
    }));
    rows.push(bytes_case("sha256/stream/textbook", m.len(), quick, || {
        black_box(textbook::digest(black_box(&m)));
    }));
    rows.push(bytes_case("sha256/stream/sha2", m.len(), quick, || {
        black_box(sha2_digest(black_box(&m)));
    }));

    let corpus = corpus();
    let bytes: usize = corpus.iter().map(String::len).sum();
    assert!(scan_all(&corpus) > 0 && lex_all(&corpus) > 0, "the corpus cuts into tokens");
    rows.push(bytes_case("scanner/lib/linked", bytes, quick, || {
        black_box(scan_all(black_box(&corpus)));
    }));
    rows.push(bytes_case("scanner/lib/lexer", bytes, quick, || {
        black_box(lex_all(black_box(&corpus)));
    }));
    rows
}

/// The work callgrind counts: `sha256-block` runs the linked compression
/// `n` times over one context (callgrind collects inside `sha256_compress`);
/// `scanner` and `lexer` read the corpus and cut it once, and `corpus` only
/// reads it, so the difference is the cutting.
fn count(case: &str, n: u64) {
    match case {
        "sha256-block" => {
            let one = message(64);
            let mut context = [0u8; block::CONTEXT];
            stream::spans::init(&mut context);
            for _ in 0..n {
                black_box(block::compress_spans(black_box(&mut context), black_box(&one)));
            }
        }
        "scanner" => {
            black_box(scan_all(&corpus()));
        }
        "lexer" => {
            black_box(lex_all(&corpus()));
        }
        "corpus" => {
            black_box(corpus());
        }
        _ => {
            eprintln!("count: sha256-block | scanner | lexer | corpus");
            std::process::exit(2);
        }
    }
    // Where this executable is mapped, for the instruction breakdown to
    // find callgrind's addresses in the file.
    if let Ok(maps) = std::fs::read_to_string("/proc/self/maps") {
        let exe = std::env::current_exe().ok().and_then(|p| p.to_str().map(String::from)).unwrap_or_default();
        if let Some(line) = maps.lines().find(|l| l.ends_with(&exe)) {
            let mut fields = line.split_whitespace();
            let range = fields.next().unwrap_or("");
            let offset = fields.nth(1).unwrap_or("0");
            let start = range.split('-').next().unwrap_or("0");
            eprintln!("mapped\t{start}\t{offset}");
        }
    }
}
