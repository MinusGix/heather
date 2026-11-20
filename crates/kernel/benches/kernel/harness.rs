//! The measurement machinery: timing estimator, scaling fit, baseline
//! comparison, and reporting. Deliberately small and first-party.
//!
//! **Why not Criterion.** `issues/dependency-policy.md` keeps the kernel at
//! zero dependencies, and a dev-dependency is not exempt: it lands in the
//! same `Cargo.lock` that the trusted base is audited from, and the audit
//! story ("`cargo-deny`/`cargo-vet` decided *before* the first dependency")
//! is not built yet. What Criterion buys — bootstrapped confidence
//! intervals, outlier classification, plots — is aimed at detecting small
//! differences in noisy code. This suite is aimed at a *cost model*: shape
//! (§Scaling) and order-of-magnitude regressions in deterministic,
//! allocation-bound tree walks. A min-of-samples estimator answers that.
//!
//! ## What is measured
//!
//! Per case: `samples` rounds of `iters` iterations, `iters` calibrated so a
//! round takes ~`round_ns`. Reported statistic is the **minimum** per-iter
//! time across rounds, with the median printed alongside. Min is the right
//! statistic here: the work is deterministic, so every sample measures the
//! same computation plus non-negative interference (scheduling, frequency,
//! other tenants). The minimum is the least-contaminated estimate; the
//! median is printed only so a large min/median gap warns that the machine
//! was busy and the numbers should not be trusted.
//!
//! ## Scaling
//!
//! Every family declares a work unit (nodes, `Succ` levels, cases) and each
//! case its size. The headline number is not the time but the **log-log
//! slope** of time against size — the exponent of the cost model. That is
//! the machine-independent part: absolute times differ 3× between machines
//! and CI runners, while "substitution is linear in term size" either holds
//! or is a bug. Families declare the exponent band they expect, so a walk
//! that silently becomes quadratic fails without anyone having recorded a
//! number on this machine first.

use std::fmt::Write as _;
use std::time::Instant;

/// A single measured point: one fixture at one size.
pub struct Case {
    /// Size in the family's work unit — the x-axis of the scaling fit.
    pub size: u64,
    /// Work performed by `run`, timed. Must be repeatable (same result
    /// every call) and free of setup: build fixtures when constructing the
    /// family, not here.
    pub run: Box<dyn Fn() -> u64>,
    /// Value `run` must return. Checked once before timing: a fixture that
    /// stopped doing its work (a check that now fails, a reduction that now
    /// gets stuck) would otherwise report a fast, meaningless number.
    pub expect: u64,
}

impl Case {
    pub fn new(size: u64, expect: u64, run: impl Fn() -> u64 + 'static) -> Case {
        Case { size, expect, run: Box::new(run) }
    }
}

/// A family of cases over one fixture at increasing sizes.
pub struct Family {
    /// Stable identifier, `area/fixture`. Baseline keys are built from it.
    pub name: &'static str,
    /// One line on what is being measured and why it is in the suite.
    pub what: &'static str,
    /// Work unit for `Case::size` (printed; also the denominator of the
    /// per-unit cost).
    pub unit: &'static str,
    /// Expected log-log slope band, `(low, high)`. `None` for families
    /// whose size axis is a case count rather than a problem size, where a
    /// slope of 1 is arithmetic rather than a claim.
    pub expect_slope: Option<(f64, f64)>,
    pub cases: Vec<Case>,
}

/// Outcome for one case.
pub struct Point {
    pub size: u64,
    pub min_ns: f64,
    pub median_ns: f64,
    pub iters: u64,
    /// The kernel's counters (`heather_kernel::stats`) over one run of the
    /// case, the [`COUNTED`] ones that moved. Unlike the times these are
    /// exact and machine-independent: the same code does the same work.
    pub counts: Vec<(&'static str, u64)>,
}

/// The counters a case records and `--check` gates exactly. Each is work
/// the kernel does, not time: fuel units and δ-steps of the evaluator, the
/// substitution reducer's steps, the nodes the shift and substitution
/// traversals visited, and the largest value arena one query built.
/// `arena_peak_bytes` is a size in bytes of this build's value layout, so it
/// is compared only where frame layout is (same `rustc` and profile).
pub const COUNTED: &[&str] = &[
    "eval_steps",
    "eval_delta_steps",
    "reduce_steps",
    "local_subst_nodes",
    "shift_global_nodes",
    "arena_peak_bytes",
];

/// The counter whose value depends on the build's memory layout.
const LAYOUT_COUNTER: &str = "arena_peak_bytes";

/// Counters that move by a little between identical runs, because the memos
/// that save their work are keyed by node address (`scripts/bench-probes`
/// has the same two), compared within [`APPROX_TOLERANCE`].
const APPROX: &[&str] = &["local_subst_nodes", "shift_global_nodes"];
const APPROX_TOLERANCE: f64 = 0.05;

/// Run `f` once and read the [`COUNTED`] counters it moved.
fn count_run(f: &dyn Fn() -> u64) -> (u64, Vec<(&'static str, u64)>) {
    use heather_kernel::stats;
    let peaks = stats::peak_scope_open();
    let before = stats::snapshot();
    let got = f();
    let moved = stats::snapshot().since(&before);
    stats::peak_scope_close(peaks);
    let counts = stats::Snapshot::NAMES
        .iter()
        .zip(moved.values())
        .filter(|(name, v)| *v > 0 && COUNTED.contains(name))
        .map(|(name, v)| (*name, v))
        .collect();
    (got, counts)
}

/// Outcome for one family.
pub struct Report {
    pub name: &'static str,
    pub what: &'static str,
    pub unit: &'static str,
    pub points: Vec<Point>,
    /// Fitted log-log slope, `None` for a single-point family.
    pub slope: Option<f64>,
    pub expect_slope: Option<(f64, f64)>,
}

pub struct Cfg {
    /// Target duration of one sampling round, nanoseconds.
    pub round_ns: u64,
    /// Rounds per case (the min is taken over these).
    pub samples: u32,
}

impl Default for Cfg {
    fn default() -> Cfg {
        Cfg { round_ns: 50_000_000, samples: 7 }
    }
}

impl Cfg {
    /// Enough to see a shape, not enough to trust a 5% delta. For iterating
    /// on fixtures and for CI smoke runs.
    pub fn quick() -> Cfg {
        Cfg { round_ns: 5_000_000, samples: 3 }
    }
}

// ---------------------------------------------------------------------------
// Timing
// ---------------------------------------------------------------------------

fn time_iters(f: &dyn Fn() -> u64, iters: u64) -> u64 {
    let start = Instant::now();
    for _ in 0..iters {
        std::hint::black_box((f)());
    }
    start.elapsed().as_nanos() as u64
}

/// Measure one case: validate, calibrate an iteration count, warm up, then
/// sample.
pub fn measure(case: &Case, cfg: &Cfg) -> Point {
    // The validating run is also the counted one. A fixture has run once at
    // setup already, so this run sees the same warm per-node caches (the
    // kernel's `Rc` heads) every later one does.
    let (got, counts) = count_run(&*case.run);
    assert!(
        got == case.expect,
        "fixture at size {} returned {got}, expected {} — the fixture is \
         broken, not slow (checksum mismatch means the work changed)",
        case.size,
        case.expect
    );

    // Calibrate: grow the iteration count until a round is long enough to
    // measure against a ~40 ns clock, capped so a slow case still runs.
    let mut iters = 1u64;
    let mut round = time_iters(&*case.run, iters);
    while round < cfg.round_ns / 4 && iters < 1 << 30 {
        // Grow by the observed shortfall (rounded up, at least 2×) rather
        // than doubling blindly: one extra calibration round instead of ten.
        let want = if round == 0 { 16 } else { (cfg.round_ns / round.max(1)).max(2) };
        iters = iters.saturating_mul(want.min(64));
        round = time_iters(&*case.run, iters);
    }

    // Warm up (caches, allocator arenas, frequency scaling) — one round's
    // worth, discarded.
    std::hint::black_box(time_iters(&*case.run, iters));

    let mut per_iter: Vec<f64> = Vec::with_capacity(cfg.samples as usize);
    for _ in 0..cfg.samples {
        let ns = time_iters(&*case.run, iters);
        per_iter.push(ns as f64 / iters as f64);
    }
    per_iter.sort_by(|a, b| a.partial_cmp(b).unwrap());

    Point {
        size: case.size,
        min_ns: per_iter[0],
        median_ns: per_iter[per_iter.len() / 2],
        iters,
        counts,
    }
}

pub fn run_family(fam: Family, cfg: &Cfg) -> Report {
    let points: Vec<Point> = fam.cases.iter().map(|c| measure(c, cfg)).collect();
    Report {
        name: fam.name,
        what: fam.what,
        unit: fam.unit,
        slope: fit_slope(&points),
        expect_slope: fam.expect_slope,
        points,
    }
}

// ---------------------------------------------------------------------------
// Scaling fit
// ---------------------------------------------------------------------------

/// Least-squares slope of `log(time)` against `log(size)` — the exponent of
/// the empirical cost model. Two points give the exact two-point slope; more
/// points average out per-point noise.
///
/// The smallest sizes are kept in the fit deliberately: a family whose small
/// cases are dominated by fixed overhead will show a slope below its true
/// exponent, and that is information about the fixture (sizes chosen too
/// small), not something to hide by dropping points.
pub fn fit_slope(points: &[Point]) -> Option<f64> {
    if points.len() < 2 {
        return None;
    }
    let n = points.len() as f64;
    let xs: Vec<f64> = points.iter().map(|p| (p.size as f64).ln()).collect();
    let ys: Vec<f64> = points.iter().map(|p| p.min_ns.max(1.0).ln()).collect();
    let mx = xs.iter().sum::<f64>() / n;
    let my = ys.iter().sum::<f64>() / n;
    let num: f64 = xs.iter().zip(&ys).map(|(x, y)| (x - mx) * (y - my)).sum();
    let den: f64 = xs.iter().map(|x| (x - mx) * (x - mx)).sum();
    if den == 0.0 { None } else { Some(num / den) }
}

// ---------------------------------------------------------------------------
// Baselines
// ---------------------------------------------------------------------------

/// A recorded run. TSV rather than JSON so it stays greppable, diffable, and
/// parseable without a dependency:
///
/// ```text
/// # kind  key                     …
/// env     host                    thinkpad
/// case    subst/shift-local       64      12400.0
/// slope   subst/shift-local       1.02
/// stack   stack/check-numeral     4194304 88
/// ```
#[derive(Default)]
pub struct Baseline {
    pub env: Vec<(String, String)>,
    /// `(family, size) -> min_ns`
    pub cases: Vec<(String, u64, f64)>,
    /// `family -> slope`
    pub slopes: Vec<(String, f64)>,
    /// `(probe, stack_bytes) -> max_levels`
    pub stacks: Vec<(String, u64, u64)>,
    /// `(family, size, counter) -> value`
    pub counts: Vec<(String, u64, String, u64)>,
}

impl Baseline {
    pub fn parse(text: &str) -> Baseline {
        let mut b = Baseline::default();
        for line in text.lines() {
            let line = line.trim_end();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let f: Vec<&str> = line.split('\t').filter(|s| !s.is_empty()).collect();
            match f.as_slice() {
                ["env", k, v] => b.env.push((k.to_string(), v.to_string())),
                ["case", name, size, ns] => {
                    if let (Ok(size), Ok(ns)) = (size.parse(), ns.parse()) {
                        b.cases.push((name.to_string(), size, ns));
                    }
                }
                ["slope", name, s] => {
                    if let Ok(s) = s.parse() {
                        b.slopes.push((name.to_string(), s));
                    }
                }
                ["count", name, size, counter, value] => {
                    if let (Ok(size), Ok(value)) = (size.parse(), value.parse()) {
                        b.counts.push((name.to_string(), size, counter.to_string(), value));
                    }
                }
                ["stack", name, bytes, levels] => {
                    if let (Ok(bytes), Ok(levels)) = (bytes.parse(), levels.parse()) {
                        b.stacks.push((name.to_string(), bytes, levels));
                    }
                }
                _ => {}
            }
        }
        b
    }

    pub fn render(
        env: &[(String, String)],
        reports: &[Report],
        probes: &[crate::stack::Probe],
    ) -> String {
        let mut out = String::new();
        out.push_str(
            "# Heather kernel benchmark baseline — see docs/infrastructure/benchmarking.md\n\
             # Regenerate with: scripts/bench --save\n",
        );
        for (k, v) in env {
            let _ = writeln!(out, "env\t{k}\t{v}");
        }
        for r in reports {
            for p in &r.points {
                let _ = writeln!(out, "case\t{}\t{}\t{:.1}", r.name, p.size, p.min_ns);
            }
        }
        for r in reports {
            if let Some(s) = r.slope {
                let _ = writeln!(out, "slope\t{}\t{:.3}", r.name, s);
            }
        }
        for r in reports {
            for p in &r.points {
                for (counter, v) in &p.counts {
                    let _ = writeln!(out, "count\t{}\t{}\t{counter}\t{v}", r.name, p.size);
                }
            }
        }
        for p in probes {
            let _ = writeln!(out, "stack\t{}\t{}\t{}", p.name, p.stack_bytes, p.max_levels);
        }
        out
    }

    pub fn env_get(&self, k: &str) -> Option<&str> {
        self.env.iter().find(|(key, _)| key == k).map(|(_, v)| v.as_str())
    }

    fn case(&self, name: &str, size: u64) -> Option<f64> {
        self.cases.iter().find(|(n, s, _)| n == name && *s == size).map(|(_, _, ns)| *ns)
    }

    fn slope(&self, name: &str) -> Option<f64> {
        self.slopes.iter().find(|(n, _)| n == name).map(|(_, s)| *s)
    }

    /// The family's recorded counters at `size`, or `None` when the baseline
    /// predates counters for it.
    fn counts(&self, name: &str, size: u64) -> Option<Vec<(&str, u64)>> {
        let v: Vec<_> = self
            .counts
            .iter()
            .filter(|(n, s, _, _)| n == name && *s == size)
            .map(|(_, _, c, v)| (c.as_str(), *v))
            .collect();
        (!v.is_empty()).then_some(v)
    }

    fn stack(&self, name: &str, bytes: u64) -> Option<u64> {
        self.stacks
            .iter()
            .find(|(n, b, _)| n == name && *b == bytes)
            .map(|(_, _, levels)| *levels)
    }
}

/// How a comparison came out. `Regressed` is the only value that fails a
/// `--check` run.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Verdict {
    Regressed,
    /// A time past the regression ratio. Reported, never failing: times are
    /// information and the counters are the gate (a busy machine is slower
    /// without the code doing more work, and a change that does more work
    /// moves a counter whatever the machine).
    Slower,
    Improved,
    Ok,
    /// No baseline entry, or times not comparable on this machine.
    Untracked,
}

pub struct Thresholds {
    /// Ratio above which a time counts as a regression.
    pub time_regress: f64,
    /// Ratio below which a time is called out as an improvement (a hint to
    /// re-save, not a failure).
    pub time_improve: f64,
    /// Absolute slope drift that counts as a regression.
    pub slope_drift: f64,
    /// Fraction of the recorded depth below which frames count as having
    /// grown.
    pub stack_regress: f64,
    /// Compare times at all? False when the baseline was recorded on
    /// another machine, where absolute times mean nothing.
    pub compare_times: bool,
    /// Compare stack depth? False across `rustc` versions, where frame
    /// layout is not the same question.
    pub compare_stack: bool,
}

impl Default for Thresholds {
    fn default() -> Thresholds {
        // 1.25 is set against measured run-to-run spread, not guessed: three
        // consecutive full runs on the recording machine (2026-07-28) agreed
        // within ~1–2% on the many-iteration cases and ~4% on the
        // one-iteration ones (`wf/mirror-involution`, `nat/add-normalize` at
        // 1024). 1.25 leaves room for a machine that is merely busy rather
        // than quiet, because a gate that cries wolf gets ignored — which is
        // worse than a loose one. Real regressions in a tree walk are 2×+.
        Thresholds {
            time_regress: 1.25,
            time_improve: 0.8,
            // Slopes are noisier than they look: a 4-point fit over a 16×
            // size range moves ±0.15 between runs. 0.35 catches linear →
            // quadratic (a full 1.0) with margin to spare.
            slope_drift: 0.35,
            // Stack depth is measured by bisection, so it is exact up to one
            // level: 10% is not noise tolerance but "don't fail on a
            // rounding-scale change in one frame".
            stack_regress: 0.9,
            compare_times: true,
            compare_stack: true,
        }
    }
}

pub struct Diff {
    pub label: String,
    pub verdict: Verdict,
    /// Human-readable "12.4 µs → 31.0 µs (2.50×)".
    pub detail: String,
}

pub fn compare(
    reports: &[Report],
    probes: &[crate::stack::Probe],
    base: &Baseline,
    th: &Thresholds,
) -> Vec<Diff> {
    let mut out = vec![];
    for r in reports {
        if th.compare_times {
            for p in &r.points {
                let Some(b) = base.case(r.name, p.size) else {
                    out.push(Diff {
                        label: format!("{}:{}", r.name, p.size),
                        verdict: Verdict::Untracked,
                        detail: "no baseline entry".into(),
                    });
                    continue;
                };
                let ratio = p.min_ns / b;
                let verdict = if ratio >= th.time_regress {
                    Verdict::Slower
                } else if ratio <= th.time_improve {
                    Verdict::Improved
                } else {
                    Verdict::Ok
                };
                out.push(Diff {
                    label: format!("{}:{}", r.name, p.size),
                    verdict,
                    detail: format!("{} → {} ({ratio:.2}×)", dur(b), dur(p.min_ns)),
                });
            }
        }
        // Counters are compared exactly, on every machine: the same code does
        // the same work. Any growth is a regression, any drop an improvement
        // to re-record; there is no noise to allow for. The layout counter
        // is held to the stack's condition (same rustc and profile).
        for p in &r.points {
            let Some(b) = base.counts(r.name, p.size) else {
                if !p.counts.is_empty() {
                    out.push(Diff {
                        label: format!("{}:{} counters", r.name, p.size),
                        verdict: Verdict::Untracked,
                        detail: "no recorded counters".into(),
                    });
                }
                continue;
            };
            for &counter in COUNTED {
                if counter == LAYOUT_COUNTER && !th.compare_stack {
                    continue;
                }
                let get = |v: &[(&str, u64)]| v.iter().find(|(c, _)| *c == counter).map_or(0, |(_, v)| *v);
                let (was, now) = (get(&b), get(&p.counts));
                let within = if APPROX.contains(&counter) {
                    (now as f64 - was as f64).abs() <= was as f64 * APPROX_TOLERANCE
                } else {
                    now == was
                };
                if within {
                    continue;
                }
                out.push(Diff {
                    label: format!("{}:{} {counter}", r.name, p.size),
                    verdict: if now > was { Verdict::Regressed } else { Verdict::Improved },
                    detail: format!("{was} → {now} ({:+.1}%)", (now as f64 - was as f64) * 100.0 / was.max(1) as f64),
                });
            }
        }
        // Slopes are compared on every machine: the exponent of the cost
        // model is a property of the code, not of the CPU.
        // A drift in the time slope is information like the times are: the
        // work behind it is gated exactly by the counters above.
        if let (Some(s), Some(b)) = (r.slope, base.slope(r.name)) {
            let drift = s - b;
            out.push(Diff {
                label: format!("{} slope", r.name),
                verdict: if drift > th.slope_drift { Verdict::Slower } else { Verdict::Ok },
                detail: format!("{b:.2} → {s:.2} ({drift:+.2})"),
            });
        }
        // An expected band is a standing claim about the cost model and is
        // checked whether or not a baseline exists.
        if let (Some(s), Some((lo, hi))) = (r.slope, r.expect_slope) {
            if s < lo || s > hi {
                out.push(Diff {
                    label: format!("{} slope band", r.name),
                    verdict: Verdict::Regressed,
                    detail: format!("{s:.2} outside expected {lo:.2}–{hi:.2}"),
                });
            }
        }
    }

    // Stack: fewer levels in the same stack means fatter frames.
    for p in probes {
        match base.stack(p.name, p.stack_bytes) {
            Some(b) if th.compare_stack => {
                let ratio = p.max_levels as f64 / b as f64;
                out.push(Diff {
                    label: format!("{} depth", p.name),
                    verdict: if ratio < th.stack_regress { Verdict::Regressed } else { Verdict::Ok },
                    detail: format!(
                        "{b} → {} levels in {} KiB ({:.0} B/level)",
                        p.max_levels,
                        p.stack_bytes >> 10,
                        p.bytes_per_level(),
                    ),
                });
            }
            _ => out.push(Diff {
                label: format!("{} depth", p.name),
                verdict: Verdict::Untracked,
                detail: format!("{} levels ({:.0} B/level)", p.max_levels, p.bytes_per_level()),
            }),
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

pub fn dur(ns: f64) -> String {
    if ns < 1_000.0 {
        format!("{ns:.0} ns")
    } else if ns < 1_000_000.0 {
        format!("{:.2} µs", ns / 1e3)
    } else if ns < 1_000_000_000.0 {
        format!("{:.2} ms", ns / 1e6)
    } else {
        format!("{:.2} s", ns / 1e9)
    }
}

/// The counters as a short trailer: `  [eval 1.2K δ 40 …]`.
fn render_counts(counts: &[(&str, u64)]) -> String {
    if counts.is_empty() {
        return String::new();
    }
    fn short(c: &str) -> &str {
        match c {
            "eval_steps" => "eval",
            "eval_delta_steps" => "δ",
            "reduce_steps" => "reduce",
            "local_subst_nodes" => "subst",
            "shift_global_nodes" => "shiftΨ",
            "arena_peak_bytes" => "arena",
            other => other,
        }
    }
    let num = |v: u64| match v {
        0..10_000 => v.to_string(),
        10_000..10_000_000 => format!("{:.0}K", v as f64 / 1e3),
        _ => format!("{:.0}M", v as f64 / 1e6),
    };
    let parts: Vec<String> = counts.iter().map(|(c, v)| format!("{} {}", short(c), num(*v))).collect();
    format!("   [{}]", parts.join(" "))
}

/// The slope of each counter against size: the exponent of the cost model
/// read off work instead of time, so it carries no noise.
pub fn count_slopes(r: &Report) -> Vec<(&'static str, f64)> {
    COUNTED
        .iter()
        .filter_map(|&c| {
            let pts: Vec<Point> = r
                .points
                .iter()
                .filter_map(|p| {
                    let v = p.counts.iter().find(|(n, _)| *n == c)?.1;
                    Some(Point { size: p.size, min_ns: v as f64, median_ns: v as f64, iters: 1, counts: vec![] })
                })
                .collect();
            if pts.len() != r.points.len() {
                return None;
            }
            fit_slope(&pts).map(|s| (c, s))
        })
        .collect()
}

pub fn render_family(r: &Report) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "{}  — {}", r.name, r.what);
    for p in &r.points {
        let per = p.min_ns / p.size as f64;
        let noise = p.median_ns / p.min_ns;
        let flag = if noise > 1.5 { "  ⚠ noisy" } else { "" };
        let _ = writeln!(
            out,
            "  {:>10} {:<14} {:>10}   med {:>10}   {:>10}/{}   ×{}{}{}",
            p.size,
            r.unit,
            dur(p.min_ns),
            dur(p.median_ns),
            dur(per),
            r.unit.trim_end_matches('s'),
            p.iters,
            flag,
            render_counts(&p.counts),
        );
    }
    if let Some(s) = r.slope {
        let band = match r.expect_slope {
            Some((lo, hi)) if s < lo || s > hi => format!("  ✗ outside {lo:.2}–{hi:.2}"),
            Some((lo, hi)) => format!("  (expected {lo:.2}–{hi:.2})"),
            None => String::new(),
        };
        let _ = writeln!(out, "  slope {s:.2}{band}");
    }
    let counted = count_slopes(r);
    if !counted.is_empty() {
        let parts: Vec<String> = counted.iter().map(|(c, s)| format!("{c} {s:.2}")).collect();
        let _ = writeln!(out, "  work slopes  {}", parts.join("  "));
    }
    out
}
