//! The measurement machinery for the frontend suite: timing estimator,
//! phase attribution, scaling fit, per-case guards, baseline comparison and
//! reporting.
//!
//! This is the kernel harness (`crates/kernel/benches/kernel/harness.rs`)
//! with four things added and one removed, and the differences are exactly
//! the differences between the two questions (docs/frontend-benchmarking.md):
//!
//! - **Labels.** A kernel case is identified by a number (16, 64, 256). A
//!   corpus case is identified by a file name, so `Case` carries a label and
//!   the baseline key is the label, not the size.
//! - **Phase split.** A corpus case reports where its time went — parse,
//!   elaborate, kernel gate — so a regression names its layer. The split is
//!   measured *inside* the timed closure (`crate::stats::kernel_ns` plus a
//!   parse the fixture times itself) and min-tracked across rounds like the
//!   total.
//! - **Guards.** Frontend work is orders of magnitude more expensive than a
//!   kernel tree walk (`ir_v1.hthr` is ~a minute, and an uncapped deep
//!   check once reached ~22 GB — CLAUDE.md), so every case declares a budget:
//!   a run over 3× it is not sampled, and the rest of the family — always the
//!   *larger* sizes — is skipped rather than attempted.
//! - **Latency budgets.** A case may declare an absolute alarm ceiling. It
//!   fails `--check` whether or not a baseline exists, for the reason an
//!   exponent band does: it is a standing claim, here about user latency.
//! - **No stack probe.** Stack depth is a kernel property and
//!   `crates/kernel/benches` already measures it.
//!
//! Adaptive sampling is the other concession to cost: seven rounds of a
//! 58-second case is an hour. Cases that take longer than a second get fewer
//! rounds, which is a weaker measurement, and the report says so.

use std::cell::{Cell, RefCell};
use std::fmt::Write as _;
use std::sync::Arc as Rc;
use std::time::Instant;

thread_local! {
    /// Set for exactly one run of each case — the validation run — and read
    /// by the fixtures, which do their phase attribution only then. The
    /// attribution costs an extra parse; inside a sampled round that would
    /// be measuring the benchmark instead of the elaborator.
    static PROBING: Cell<bool> = const { Cell::new(false) };
}

pub fn probing() -> bool {
    PROBING.with(|c| c.get())
}

thread_local! {
    /// Set by the smoke test (`crates/elab/tests/frontend_bench_smoke.rs`),
    /// never by the bench. **Fixture construction is the expensive part** of
    /// this suite — every generated source is validated by elaborating it,
    /// and the corpus validates `ir_v1.hthr`, which is a minute on its
    /// own. In smoke mode a family builds only its smallest non-heavy case,
    /// which is all a rot detector needs and is the difference between a
    /// 95-second test and a 3-second one.
    static SMOKE: Cell<bool> = const { Cell::new(false) };
}

pub fn smoke() -> bool {
    SMOKE.with(|c| c.get())
}

/// Unused in the bench binary by design — only the test sets it.
#[allow(dead_code)]
pub fn set_smoke(on: bool) {
    SMOKE.with(|c| c.set(on));
}

fn set_probing(on: bool) {
    PROBING.with(|c| c.set(on));
}

/// Where one file's check time went. All three come from a single
/// instrumented run; `elab_ns` is the residue, which is deliberate — it is
/// "everything the elaborator did that was not parsing and not the kernel
/// re-checking the finished declaration", including the elaborator's own
/// conversion calls (see `crates/elab/src/stats.rs`).
#[derive(Clone, Copy, Default)]
pub struct Phases {
    pub parse_ns: u64,
    pub kernel_ns: u64,
    pub total_ns: u64,
}

impl Phases {
    pub fn elab_ns(&self) -> u64 {
        self.total_ns.saturating_sub(self.parse_ns).saturating_sub(self.kernel_ns)
    }
}

/// A single measured point: one fixture at one size.
pub struct Case {
    /// Baseline key and report label — a file name for the corpus, the size
    /// rendered for a generated family.
    pub label: String,
    /// Size in the family's work unit — the x-axis of the scaling fit.
    pub size: u64,
    /// Work performed by `run`, timed. Must be repeatable (same result every
    /// call) and free of setup: build sources when constructing the family,
    /// not here.
    pub run: Box<dyn Fn() -> u64>,
    /// Value `run` must return. Checked once before timing: a fixture that
    /// stopped doing its work (a declaration that no longer elaborates, a
    /// file that now fails) would otherwise report a fast, meaningless
    /// number.
    pub expect: u64,
    /// Written by `run` when the fixture attributes its phases. Shared with
    /// the closure rather than returned so the timed signature stays one
    /// `u64`.
    pub phases: Option<Rc<Cell<Phases>>>,
    /// Wall-clock ceiling for one run. Two uses, one number: it is the
    /// **latency alarm** `--check` gates on, and 3× it is the **guard** — a
    /// validation run past that is not sampled and the family stops there.
    pub budget_ns: Option<u64>,
    /// Skipped under `--no-heavy` and by the smoke test. Set on cases that
    /// cost seconds.
    pub heavy: bool,
    /// What the fixture would say about a failed run, if it can say anything.
    /// The checksum is a count, and a count is a poor bug report: a case that
    /// elaborates sources fills this with its first diagnostic so a checksum
    /// mismatch arrives with the reason attached rather than a number.
    pub diagnosis: Option<Rc<RefCell<Option<String>>>>,
}

impl Case {
    /// A case whose label is its size — the generated families.
    pub fn new(size: u64, expect: u64, run: impl Fn() -> u64 + 'static) -> Case {
        Case {
            label: size.to_string(),
            size,
            run: Box::new(run),
            expect,
            phases: None,
            budget_ns: None,
            heavy: false,
            diagnosis: None,
        }
    }

    /// A case with its own name — the corpus files.
    pub fn named(label: &str, size: u64, expect: u64, run: impl Fn() -> u64 + 'static) -> Case {
        Case { label: label.to_string(), ..Case::new(size, expect, run) }
    }

    pub fn with_phases(mut self, cell: Rc<Cell<Phases>>) -> Case {
        self.phases = Some(cell);
        self
    }

    pub fn with_budget(mut self, ns: u64) -> Case {
        self.budget_ns = Some(ns);
        self
    }

    pub fn heavy(mut self) -> Case {
        self.heavy = true;
        self
    }

    pub fn with_diagnosis(mut self, first_error: Rc<RefCell<Option<String>>>) -> Case {
        self.diagnosis = Some(first_error);
        self
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
    /// Expected log-log slope band, `(low, high)`. `None` for families whose
    /// size axis is not a problem size — the corpus, where the x-axis is
    /// "how big is this file" across unrelated files and a slope means
    /// nothing.
    pub expect_slope: Option<(f64, f64)>,
    pub cases: Vec<Case>,
}

/// Outcome for one case.
pub struct Point {
    pub label: String,
    pub size: u64,
    pub min_ns: f64,
    pub median_ns: f64,
    pub iters: u64,
    pub samples: u32,
    pub phases: Option<Phases>,
    pub budget_ns: Option<u64>,
    /// Peak RSS of the process after this case, in bytes (Linux `VmHWM`).
    pub peak_rss: u64,
    /// The case ran once (for validation) and was over its guard, so it was
    /// not sampled. Its `min_ns` is that single run.
    pub over_budget: bool,
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
    /// Cases the guards refused to run at all (label, why).
    pub skipped: Vec<(String, String)>,
}

pub struct Cfg {
    /// Target duration of one sampling round, nanoseconds.
    pub round_ns: u64,
    /// Rounds per case, before the adaptive cut below.
    pub samples: u32,
    /// Skip cases marked `heavy`.
    pub no_heavy: bool,
    /// Peak RSS at which a family stops (bytes). The address-space rail in
    /// `scripts/bench-frontend` is the hard stop; this is the soft one that
    /// leaves a readable report instead of a dead process.
    pub mem_guard: u64,
    /// Default guard for a case that declares no budget.
    pub default_guard_ns: u64,
}

impl Default for Cfg {
    fn default() -> Cfg {
        Cfg {
            round_ns: 50_000_000,
            samples: 7,
            no_heavy: false,
            mem_guard: 3 << 30,
            default_guard_ns: 120_000_000_000,
        }
    }
}

impl Cfg {
    /// Enough to see a shape, not enough to trust a 5% delta. For iterating
    /// on fixtures and for the smoke test.
    pub fn quick() -> Cfg {
        Cfg { round_ns: 5_000_000, samples: 3, ..Cfg::default() }
    }
}

/// Rounds actually taken for a case whose single round costs `round_ns`.
/// Seven rounds of `ir_v1.hthr` is seven minutes; three is enough to see
/// a 1.25× move, and the report prints the count so a two-round number is
/// never mistaken for a seven-round one.
fn samples_for(cfg: &Cfg, one_round_ns: u64) -> u32 {
    let cut = match one_round_ns {
        n if n >= 10_000_000_000 => 2,
        n if n >= 1_000_000_000 => 3,
        n if n >= 100_000_000 => 5,
        _ => cfg.samples,
    };
    cut.min(cfg.samples).max(1)
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

/// Peak resident set size of this process, bytes. Linux-only and best-effort:
/// the number is a guard and a report line, never a gate.
pub fn peak_rss() -> u64 {
    let Ok(text) = std::fs::read_to_string("/proc/self/status") else { return 0 };
    text.lines()
        .find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|kb| kb.parse::<u64>().ok())
        .map(|kb| kb * 1024)
        .unwrap_or(0)
}

/// Measure one case: validate, guard, calibrate an iteration count, warm up,
/// then sample. Returns `None` when the guard refused the case.
pub fn measure(case: &Case, cfg: &Cfg) -> (Point, Option<String>) {
    // The validation run is also the guard's probe: a fixture has to run once
    // before anything is known about what it costs, and that one run is what
    // `scripts/bench-frontend`'s `ulimit` is there to survive.
    set_probing(true);
    let probe_start = Instant::now();
    let got = (case.run)();
    let one_round_ns = probe_start.elapsed().as_nanos() as u64;
    set_probing(false);
    assert!(
        got == case.expect,
        "fixture `{}` returned {got}, expected {} — the fixture is broken, not \
         slow (a checksum mismatch means the work changed){}",
        case.label,
        case.expect,
        match case.diagnosis.as_ref().and_then(|d| d.borrow().clone()) {
            Some(first) => format!("\nfirst diagnostic of this run:\n{first}"),
            None => String::new(),
        }
    );

    let guard = case.budget_ns.map(|b| b.saturating_mul(3)).unwrap_or(cfg.default_guard_ns);
    let phases = case.phases.as_ref().map(|c| c.get());
    if one_round_ns > guard {
        return (
            Point {
                label: case.label.clone(),
                size: case.size,
                min_ns: one_round_ns as f64,
                median_ns: one_round_ns as f64,
                iters: 1,
                samples: 1,
                phases,
                budget_ns: case.budget_ns,
                peak_rss: peak_rss(),
                over_budget: true,
            },
            Some(format!(
                "{} took {} on its validation run, over its {} guard — not sampled",
                case.label,
                dur(one_round_ns as f64),
                dur(guard as f64)
            )),
        );
    }

    // Calibrate: grow the iteration count until a round is long enough to
    // measure against a ~40 ns clock, capped so a slow case still runs.
    let mut iters = 1u64;
    let mut round = one_round_ns;
    while round < cfg.round_ns / 4 && iters < 1 << 30 {
        let want = if round == 0 { 16 } else { (cfg.round_ns / round.max(1)).max(2) };
        iters = iters.saturating_mul(want.min(64));
        round = time_iters(&*case.run, iters);
    }

    // Warm up (caches, allocator arenas, frequency scaling) — one round's
    // worth, discarded. Skipped for cases that already cost a second, where
    // the warm-up is a round nobody reads.
    if round < 1_000_000_000 {
        std::hint::black_box(time_iters(&*case.run, iters));
    }

    let samples = samples_for(cfg, round / iters.max(1));
    let mut per_iter: Vec<f64> = Vec::with_capacity(samples as usize);
    for _ in 0..samples {
        let ns = time_iters(&*case.run, iters);
        per_iter.push(ns as f64 / iters as f64);
    }
    per_iter.sort_by(|a, b| a.partial_cmp(b).unwrap());

    (
        Point {
            label: case.label.clone(),
            size: case.size,
            min_ns: per_iter[0],
            median_ns: per_iter[per_iter.len() / 2],
            iters,
            samples,
            // From the probe run, which is one sample: the split is a set of
            // proportions ("where did the time go"), not a measurement to
            // compare at 5%. The total is min-of-rounds and is.
            phases,
            budget_ns: case.budget_ns,
            peak_rss: peak_rss(),
            over_budget: false,
        },
        None,
    )
}

pub fn run_family(fam: Family, cfg: &Cfg) -> Report {
    let mut points = vec![];
    let mut skipped = vec![];
    for case in &fam.cases {
        if cfg.no_heavy && case.heavy {
            skipped.push((case.label.clone(), "heavy (--no-heavy)".to_string()));
            continue;
        }
        let (p, note) = measure(case, cfg);
        let over = p.over_budget;
        let rss = p.peak_rss;
        points.push(p);
        if let Some(note) = note {
            skipped.push((case.label.clone(), note));
        }
        // Cases are in increasing size order, so a case that blew a guard
        // means every case after it would blow it harder. Stop the family
        // rather than find out.
        if over {
            skipped.push((
                "…".to_string(),
                "later sizes not attempted (a smaller one was already over budget)".to_string(),
            ));
            break;
        }
        if rss > cfg.mem_guard {
            skipped.push((
                "…".to_string(),
                format!("later sizes not attempted (peak RSS {} over guard)", bytes(rss as f64)),
            ));
            break;
        }
    }
    Report {
        name: fam.name,
        what: fam.what,
        unit: fam.unit,
        slope: fit_slope(&points),
        expect_slope: fam.expect_slope,
        points,
        skipped,
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
/// cases are dominated by fixed overhead (here: the prelude, which every
/// generated fixture pays once) will show a slope below its true exponent,
/// and that is information about the fixture, not something to hide by
/// dropping points.
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
/// case    corpus/check-file       ir_v1.hthr      58000000000.0
/// split   corpus/check-file       ir_v1.hthr      kernel  41000000000
/// slope   scale/declarations      1.02
/// ```
#[derive(Default)]
pub struct Baseline {
    pub env: Vec<(String, String)>,
    /// `(family, label) -> min_ns`
    pub cases: Vec<(String, String, f64)>,
    /// `(family, label, phase) -> ns`
    pub splits: Vec<(String, String, String, f64)>,
    /// `family -> slope`
    pub slopes: Vec<(String, f64)>,
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
                ["case", name, label, ns] => {
                    if let Ok(ns) = ns.parse() {
                        b.cases.push((name.to_string(), label.to_string(), ns));
                    }
                }
                ["split", name, label, phase, ns] => {
                    if let Ok(ns) = ns.parse() {
                        b.splits.push((
                            name.to_string(),
                            label.to_string(),
                            phase.to_string(),
                            ns,
                        ));
                    }
                }
                ["slope", name, s] => {
                    if let Ok(s) = s.parse() {
                        b.slopes.push((name.to_string(), s));
                    }
                }
                _ => {}
            }
        }
        b
    }

    pub fn render(env: &[(String, String)], reports: &[Report]) -> String {
        let mut out = String::new();
        out.push_str(
            "# Heather frontend benchmark baseline — see docs/frontend-benchmarking.md\n\
             # Regenerate with: scripts/bench-frontend --save\n",
        );
        for (k, v) in env {
            let _ = writeln!(out, "env\t{k}\t{v}");
        }
        for r in reports {
            for p in &r.points {
                let _ = writeln!(out, "case\t{}\t{}\t{:.1}", r.name, p.label, p.min_ns);
            }
        }
        for r in reports {
            for p in &r.points {
                if let Some(ph) = p.phases {
                    for (phase, ns) in
                        [("parse", ph.parse_ns), ("elab", ph.elab_ns()), ("kernel", ph.kernel_ns)]
                    {
                        let _ = writeln!(out, "split\t{}\t{}\t{phase}\t{ns}", r.name, p.label);
                    }
                }
            }
        }
        for r in reports {
            if let Some(s) = r.slope {
                let _ = writeln!(out, "slope\t{}\t{:.3}", r.name, s);
            }
        }
        out
    }

    pub fn env_get(&self, k: &str) -> Option<&str> {
        self.env.iter().find(|(key, _)| key == k).map(|(_, v)| v.as_str())
    }

    fn case(&self, name: &str, label: &str) -> Option<f64> {
        self.cases
            .iter()
            .find(|(n, l, _)| n == name && l == label)
            .map(|(_, _, ns)| *ns)
    }

    fn split(&self, name: &str, label: &str, phase: &str) -> Option<f64> {
        self.splits
            .iter()
            .find(|(n, l, p, _)| n == name && l == label && p == phase)
            .map(|(_, _, _, ns)| *ns)
    }

    fn slope(&self, name: &str) -> Option<f64> {
        self.slopes.iter().find(|(n, _)| n == name).map(|(_, s)| *s)
    }
}

/// How a comparison came out. `Regressed` is the only value that fails a
/// `--check` run; `Info` is printed and never fails (the phase splits, which
/// are there to *explain* a regression, not to be one).
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Verdict {
    Regressed,
    Improved,
    Ok,
    Info,
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
    /// Ratio at which a phase's share is worth printing as the explanation
    /// of a move. Never a failure on its own.
    pub split_notice: f64,
    /// Compare times at all? False when the baseline was recorded on another
    /// machine, where absolute times mean nothing.
    pub compare_times: bool,
}

impl Default for Thresholds {
    fn default() -> Thresholds {
        Thresholds {
            // The kernel suite's 1.25, for the kernel suite's reason (a gate
            // that cries wolf gets ignored) — but frontend cases are longer
            // and run fewer rounds, so the measured spread is wider: the
            // corpus's one-round cases moved ~3–6% across the recording
            // runs. 1.25 still clears that with margin.
            time_regress: 1.25,
            time_improve: 0.8,
            slope_drift: 0.35,
            split_notice: 1.15,
            compare_times: true,
        }
    }
}

pub struct Diff {
    pub label: String,
    pub verdict: Verdict,
    /// Human-readable "12.4 µs → 31.0 µs (2.50×)".
    pub detail: String,
}

pub fn compare(reports: &[Report], base: &Baseline, th: &Thresholds) -> Vec<Diff> {
    let mut out = vec![];
    for r in reports {
        for p in &r.points {
            // A declared latency budget is a standing claim about user
            // latency, so it is checked on every machine, baseline or not —
            // the same status an exponent band has. It is deliberately loose
            // (docs/frontend-benchmarking.md): the point is to notice a file
            // that became unusable, not to police 20%.
            if let Some(b) = p.budget_ns {
                if p.min_ns > b as f64 {
                    out.push(Diff {
                        label: format!("{}:{} budget", r.name, p.label),
                        verdict: Verdict::Regressed,
                        detail: format!(
                            "{} over the {} latency budget",
                            dur(p.min_ns),
                            dur(b as f64)
                        ),
                    });
                }
            }
            if p.over_budget {
                out.push(Diff {
                    label: format!("{}:{} guard", r.name, p.label),
                    verdict: Verdict::Regressed,
                    detail: "not sampled: one run exceeded the guard".to_string(),
                });
            }
            if !th.compare_times {
                continue;
            }
            let Some(b) = base.case(r.name, &p.label) else {
                out.push(Diff {
                    label: format!("{}:{}", r.name, p.label),
                    verdict: Verdict::Untracked,
                    detail: "no baseline entry".into(),
                });
                continue;
            };
            let ratio = p.min_ns / b;
            let verdict = if ratio >= th.time_regress {
                Verdict::Regressed
            } else if ratio <= th.time_improve {
                Verdict::Improved
            } else {
                Verdict::Ok
            };
            // A busy machine inflates min and median together, so a
            // regression flag on a case whose own median is far above its
            // own min is a claim about the machine as much as the code.
            // Printing the ratio beside the verdict is what lets a reader
            // apply docs/benchmarking.md's "re-run before believing it"
            // without a second run first.
            let noise = p.median_ns / p.min_ns;
            let noise = if noise > 1.15 { format!("  [med/min {noise:.2}×]") } else { String::new() };
            out.push(Diff {
                label: format!("{}:{}", r.name, p.label),
                verdict,
                detail: format!("{} → {} ({ratio:.2}×){noise}", dur(b), dur(p.min_ns)),
            });
            // The layer attribution. Printed when a phase moved, whether or
            // not the total did: this is the line that says *where*.
            if let Some(ph) = p.phases {
                for (phase, ns) in
                    [("parse", ph.parse_ns), ("elab", ph.elab_ns()), ("kernel", ph.kernel_ns)]
                {
                    let Some(bs) = base.split(r.name, &p.label, phase) else { continue };
                    let ratio = ns as f64 / bs.max(1.0);
                    if ratio >= th.split_notice || ratio <= 1.0 / th.split_notice {
                        out.push(Diff {
                            label: format!("  {}:{} {phase}", r.name, p.label),
                            verdict: Verdict::Info,
                            detail: format!(
                                "{} → {} ({ratio:.2}×)",
                                dur(bs),
                                dur(ns as f64)
                            ),
                        });
                    }
                }
            }
        }
        // Slopes are compared on every machine: the exponent of the cost
        // model is a property of the code, not of the CPU.
        if let (Some(s), Some(b)) = (r.slope, base.slope(r.name)) {
            let drift = s - b;
            out.push(Diff {
                label: format!("{} slope", r.name),
                verdict: if drift > th.slope_drift { Verdict::Regressed } else { Verdict::Ok },
                detail: format!("{b:.2} → {s:.2} ({drift:+.2})"),
            });
        }
        // An expected band is a standing claim about the cost model and is
        // checked whether or not a baseline exists.
        //
        // Both sides fail, and they fail for opposite reasons, so the message
        // says which side it left: *above* is the cost model getting worse,
        // and it is the reading a round should suspect itself of; *below* is
        // the claim having gone stale — the code got cheaper than what is
        // written down, and what it wants is a re-record, not a fix. A round
        // that reads a red gate has to be able to tell those apart in one
        // line; three bands sat exited from below for eleven days
        // (issues/frontend-benchmarks.md, 2026-08-17) partly because red said
        // only "outside".
        if let (Some(s), Some((lo, hi))) = (r.slope, r.expect_slope) {
            if s < lo || s > hi {
                let side = if s < lo {
                    "below — the recorded claim is stale, re-record it"
                } else {
                    "above — the cost model got worse"
                };
                out.push(Diff {
                    label: format!("{} slope band", r.name),
                    verdict: Verdict::Regressed,
                    detail: format!("{s:.2} outside expected {lo:.2}–{hi:.2}, {side}"),
                });
            }
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

pub fn bytes(b: f64) -> String {
    if b < 1024.0 {
        format!("{b:.0} B")
    } else if b < (1 << 20) as f64 {
        format!("{:.1} KiB", b / 1024.0)
    } else if b < (1 << 30) as f64 {
        format!("{:.1} MiB", b / (1 << 20) as f64)
    } else {
        format!("{:.2} GiB", b / (1 << 30) as f64)
    }
}

pub fn render_family(r: &Report) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "{}  — {}", r.name, r.what);
    for p in &r.points {
        let per = p.min_ns / p.size.max(1) as f64;
        let noise = p.median_ns / p.min_ns;
        let mut flags = String::new();
        if noise > 1.5 {
            flags.push_str("  ⚠ noisy");
        }
        if p.samples < 5 {
            let _ = write!(flags, "  ({} rounds)", p.samples);
        }
        if p.iters > 1 {
            let _ = write!(flags, "  ×{}", p.iters);
        }
        if p.over_budget {
            flags.push_str("  ✗ OVER GUARD");
        }
        if let Some(b) = p.budget_ns {
            if p.min_ns > b as f64 {
                let _ = write!(flags, "  ✗ over the {} budget", dur(b as f64));
            }
        }
        let _ = writeln!(
            out,
            "  {:>14} {:<10} {:>10}   med {:>10}   {:>10}/{}{}",
            p.label,
            r.unit,
            dur(p.min_ns),
            dur(p.median_ns),
            dur(per),
            r.unit.trim_end_matches('s'),
            flags,
        );
        if let Some(ph) = p.phases {
            let pct = |x: u64| 100.0 * x as f64 / ph.total_ns.max(1) as f64;
            let _ = writeln!(
                out,
                "  {:>14} parse {} ({:.1}%)   elab {} ({:.1}%)   kernel {} ({:.1}%)",
                "",
                dur(ph.parse_ns as f64),
                pct(ph.parse_ns),
                dur(ph.elab_ns() as f64),
                pct(ph.elab_ns()),
                dur(ph.kernel_ns as f64),
                pct(ph.kernel_ns),
            );
        }
    }
    for (label, why) in &r.skipped {
        let _ = writeln!(out, "  {label:>14} skipped: {why}");
    }
    if let Some(s) = r.slope {
        let band = match r.expect_slope {
            Some((lo, hi)) if s < lo || s > hi => format!("  ✗ outside {lo:.2}–{hi:.2}"),
            Some((lo, hi)) => format!("  (expected {lo:.2}–{hi:.2})"),
            None => String::new(),
        };
        let _ = writeln!(out, "  slope {s:.2}{band}");
    }
    out
}
