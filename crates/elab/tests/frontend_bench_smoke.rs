//! Smoke test for the frontend benchmark suite
//! (`issues/frontend-benchmarks.md`, `docs/infrastructure/frontend-benchmarking.md`).
//!
//! A benchmark suite nobody runs between rounds rots silently: a generated
//! fixture stops elaborating, a family name drifts from the `--list` table,
//! the baseline parser stops round-tripping. None of that is caught by
//! `cargo test`, because bench targets are not test targets — so this file
//! reaches into `benches/frontend/` with `#[path]` (the same trick the kernel
//! bench uses in the other direction to reach `tests/common`) and runs the
//! suite's own machinery under `scripts/test`.
//!
//! What it deliberately does **not** do is measure. Every timing here is a
//! shape at best: the point is that the fixtures build, validate, run and
//! report, at the smallest size of each family and with the heavy corpus
//! cases (`lib/certgen/ir_v1.hthr`, ~a minute) excluded. `scripts/test`'s CPU rail is
//! 300 seconds and `crates/elab/tests/ir_v1.rs` already spends a quarter of
//! it.

// The bench binary uses more of the harness than a test does (rendering,
// the RSS probe); unused-here is not unused.
#[allow(dead_code)]
#[path = "../benches/frontend/harness.rs"]
mod harness;

#[allow(dead_code)]
#[path = "../benches/frontend/fixtures/mod.rs"]
mod fixtures;

use harness::{Baseline, Case, Cfg, Point, Report};

/// One round of every family, at its smallest non-heavy case. This is the
/// test that catches "the generator emits something that no longer
/// elaborates", which is the failure that would otherwise be discovered by
/// whoever next ran a four-minute benchmark.
#[test]
fn every_family_builds_validates_and_runs_one_round() {
    harness::set_smoke(true);
    let cfg = Cfg { round_ns: 1, samples: 1, no_heavy: true, ..Cfg::default() };
    let families = fixtures::all();
    assert!(families.len() >= 8, "the suite lost families: {}", families.len());

    for fam in families {
        let case = fam
            .cases
            .iter()
            .find(|c| !c.heavy)
            .unwrap_or_else(|| panic!("family `{}` has only heavy cases", fam.name));
        let (point, note) = harness::measure(case, &cfg);
        assert!(note.is_none(), "family `{}`: {}", fam.name, note.unwrap());
        assert!(point.min_ns > 0.0, "family `{}` measured nothing", fam.name);
        // Every family that reports a split must report a plausible one: the
        // phases come from a different (probe) run than the timing, so they
        // are not compared to `min_ns`, but they must add up.
        if let Some(ph) = point.phases {
            assert!(
                ph.total_ns >= ph.parse_ns + ph.kernel_ns,
                "family `{}`: split exceeds the run it came from",
                fam.name
            );
        }
    }
}

/// The `--list` table in `main.rs` is written by hand so that `--list` costs
/// nothing (building the fixtures validates every generated source). This is
/// the check that keeps the hand-written copy honest — it is duplicated
/// knowledge, and duplicated knowledge gets a test or gets deleted.
#[test]
fn the_list_table_names_every_family() {
    harness::set_smoke(true);
    let listed = include_str!("../benches/frontend/main.rs");
    for fam in fixtures::all() {
        assert!(
            listed.contains(&format!("(\"{}\"", fam.name)),
            "family `{}` is missing from fixtures_index() in benches/frontend/main.rs",
            fam.name
        );
    }
}

/// The baseline is a hand-editable TSV with no parser library behind it, so
/// the round trip is worth one test: a `--save` whose file `--check` cannot
/// read is a gate that silently passes.
#[test]
fn a_baseline_round_trips() {
    let report = Report {
        name: "smoke/family",
        what: "a synthetic report",
        unit: "widgets",
        points: vec![Point {
            label: "ir_v1.hthr".into(),
            size: 100,
            min_ns: 1234.0,
            median_ns: 1300.0,
            iters: 1,
            samples: 3,
            phases: Some(harness::Phases { parse_ns: 100, kernel_ns: 900, total_ns: 1234 }),
            budget_ns: Some(5000),
            peak_rss: 0,
            over_budget: false,
        }],
        slope: Some(1.5),
        expect_slope: Some((1.0, 2.0)),
        skipped: vec![],
    };
    let env = vec![("host".to_string(), "somewhere".to_string())];
    let text = Baseline::render(&env, std::slice::from_ref(&report));
    let base = Baseline::parse(&text);
    assert_eq!(base.env_get("host"), Some("somewhere"));
    assert_eq!(base.cases.len(), 1);
    assert_eq!(base.slopes.len(), 1);
    // parse, elab and kernel, with elab the residue.
    assert_eq!(base.splits.len(), 3);
    assert!(text.contains("split\tsmoke/family\tir_v1.hthr\telab\t234"));

    // And the comparison against itself is clean, which is the property
    // `--check` rests on.
    let th = harness::Thresholds::default();
    let diffs = harness::compare(std::slice::from_ref(&report), &base, &th);
    assert!(
        diffs.iter().all(|d| d.verdict != harness::Verdict::Regressed),
        "a report regressed against a baseline recorded from itself"
    );
}

/// The guard that keeps one runaway fixture from taking the suite: a case
/// over its budget is measured once, reported, and not sampled.
#[test]
fn a_case_over_its_guard_is_not_sampled() {
    let case = Case::new(1, 0, || {
        std::thread::sleep(std::time::Duration::from_millis(20));
        0
    })
    .with_budget(1_000_000); // 1 ms budget, so a 3 ms guard against a 20 ms run
    let (point, note) = harness::measure(&case, &Cfg::quick());
    assert!(point.over_budget, "a 20 ms run under a 3 ms guard was sampled anyway");
    assert_eq!(point.samples, 1);
    assert!(note.expect("a note").contains("not sampled"));
}

/// The fit is the headline number, so it gets the one test that says it is a
/// fit and not a ratio: exact powers in, exact exponents out.
#[test]
fn the_slope_fit_reads_exact_powers() {
    let points = |f: fn(f64) -> f64| -> Vec<Point> {
        [1.0f64, 2.0, 4.0, 8.0]
            .iter()
            .map(|&n| Point {
                label: n.to_string(),
                size: n as u64,
                min_ns: f(n),
                median_ns: f(n),
                iters: 1,
                samples: 1,
                phases: None,
                budget_ns: None,
                peak_rss: 0,
                over_budget: false,
            })
            .collect()
    };
    assert!((harness::fit_slope(&points(|n| n)).unwrap() - 1.0).abs() < 1e-9);
    assert!((harness::fit_slope(&points(|n| n * n)).unwrap() - 2.0).abs() < 1e-9);
    assert!(harness::fit_slope(&points(|_| 42.0)).unwrap().abs() < 1e-9);
}
