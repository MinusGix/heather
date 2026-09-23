//! The instrumentation layer's own tests (`docs/instrumentation-design.md`).
//!
//! Each one pins a property the layer is only useful if it has: the counters
//! move, the timers attribute to the phase that spent the time, nesting does
//! not double-count, and a run that did not ask for attribution collects
//! nothing.

use heather_elab::Elaborator;
use heather_elab::stats::{self, Counter, ScopeKind, Timer};
use heather_kernel::stats as kstats;

const MODULE: &str = r#"
fn double(n: Nat) -> Nat {
    match n {
        Zero => Zero,
        Succ(m) => Succ(Succ(double(m))),
    }
}

theorem double_zero(): double(Zero) = Zero { refl }
"#;

/// A module with declarations produces a declaration row each, parse time
/// lands in its own column, and the kernel's counters move — the four things
/// every other use of the layer reads.
#[test]
fn a_checked_module_attributes_by_declaration() {
    let mut elab = Elaborator::with_prelude().expect("prelude");
    elab.enable_item_timings();
    {
        // The module row is pushed when this guard drops, so the rows are
        // drained after it, not inside it.
        let _scope = stats::scope(ScopeKind::Module, "probe", "");
        let errors = elab.check_module_source("probe", MODULE);
        assert!(errors.is_empty(), "{errors:?}");
    }
    let module = stats::take_rows();

    let items: Vec<_> = module.iter().filter(|r| r.kind == ScopeKind::Item).collect();
    assert!(items.len() >= 2, "one row per declaration: {:?}", names(&module));
    assert!(items.iter().any(|r| r.item == "double"));
    assert!(items.iter().any(|r| r.item == "double_zero"));

    let module_row = module
        .iter()
        .find(|r| r.kind == ScopeKind::Module)
        .expect("a module row");
    assert_eq!(module_row.module, "probe");
    assert!(module_row.timers[Timer::Parse as usize] > 0, "parse time is its own column");
    assert!(
        module_row.total_ns >= items.iter().map(|r| r.total_ns).sum::<u64>(),
        "a module row is inclusive of its declarations",
    );

    // Parsing happens before the first declaration scope opens, so a
    // declaration's time is parser-independent by construction.
    assert!(
        items.iter().all(|r| r.timers[Timer::Parse as usize] == 0),
        "no declaration pays for the parse",
    );

    // The gate ran, and the kernel counted what it did there.
    assert!(items.iter().any(|r| r.kernel_ns > 0), "the kernel gate is timed");
    assert!(items.iter().any(|r| r.counters[Counter::DeclsGated as usize] > 0));
    let conv: u64 = items
        .iter()
        .map(|r| r.kernel.conv_shortcut_hits + r.kernel.conv_memo_hits + r.kernel.conv_misses)
        .sum();
    assert!(conv > 0, "checking these declarations asks for conversions");
    assert!(
        items.iter().map(|r| r.kernel.eval_steps).sum::<u64>() > 0,
        "and the evaluator takes steps",
    );

    stats::disable();
}

/// A module that walks every phase of a declaration, so the columns added to
/// name the `other` bucket (`issues/perf-instrumentation-consolidation.md`,
/// 2026-09-11) can each be shown to move.
const PHASES: &str = r#"
inductive Colour { Red, Green }

fn flip(c: Colour) -> Colour {
    match c {
        Red => Green,
        Green => Red,
    }
}

fn double(n: Nat) -> Nat {
    match n {
        Zero => Zero,
        Succ(m) => Succ(Succ(double(m))),
    }
}

theorem double_zero(): double(Zero) = Zero { refl }
"#;

/// Every phase column added to name `other` is populated by a module that
/// exercises it, and no row claims more phase time than it took.
///
/// The assertions are about *which* column moved and about the nesting
/// relation, never about a duration: a number here would be a benchmark
/// pretending to be a test.
#[test]
fn the_declaration_phases_are_each_attributed() {
    let mut elab = Elaborator::with_prelude().expect("prelude");
    elab.enable_item_timings();
    {
        let _scope = stats::scope(ScopeKind::Run, "phases", "");
        let errors = elab.check_module_source("phases", PHASES);
        assert!(errors.is_empty(), "{errors:?}");
    }
    let rows = stats::take_rows();
    let run = rows
        .iter()
        .find(|r| r.kind == ScopeKind::Run)
        .expect("a run row");

    // The four halves of a declaration, the non-`fn` forms' lowering, the
    // elaborator's own head-shape probes, and the source lints. `DiagNote` is
    // deliberately **not** in this list: a successful module runs no
    // diagnostic probe at all (`issues/elab-diagnostic-probe-cost.md`), which
    // is the assertion below.
    for timer in [
        Timer::DeclType,
        Timer::DeclBody,
        Timer::DeclEmit,
        Timer::DeclCommit,
        Timer::Lower,
        Timer::ElabWhnf,
        Timer::Lint,
    ] {
        assert!(
            run.timers[timer as usize] > 0,
            "{} is not populated by a module that exercises it",
            Timer::NAMES[timer as usize],
        );
    }
    // `refl` against a computing left-hand side *records* a mismatch
    // candidate, and the proof succeeds — so the candidate is dropped unread
    // and its conversion never runs. The two counters say exactly that, and
    // they are the pair that named the cost
    // (`issues/elab-diagnostic-probe-cost.md`).
    assert!(
        run.counters[Counter::DiagCandidates as usize] > 0,
        "this module writes a `refl` whose sides are not syntactically equal",
    );
    assert_eq!(
        run.counters[Counter::DiagNotes as usize], 0,
        "a successful module must not pay for a diagnostic probe",
    );
    assert_eq!(
        run.timers[Timer::DiagNote as usize], 0,
        "and therefore spends no time in one",
    );

    // The exclusive rule, on every row of a real module and not only on the
    // synthetic nesting fixture below.
    for row in &rows {
        let phases: u64 = row.timers.iter().sum();
        assert!(
            phases <= row.total_ns,
            "{} {}:{} claims {phases} ns of phases in {} ns",
            row.kind.as_str(),
            row.module,
            row.item,
            row.total_ns,
        );
    }

    // The declaration phases partition `check_decl`, so what a `fn`'s row
    // leaves unattributed is bookkeeping, not its elaboration.
    let double = rows
        .iter()
        .find(|r| r.kind == ScopeKind::Item && r.item == "double")
        .expect("a row for `double`");
    assert!(double.timers[Timer::DeclType as usize] > 0);
    assert!(double.timers[Timer::DeclBody as usize] > 0);
    assert!(
        double.other_ns() < double.total_ns,
        "a declaration's phases account for some of it",
    );

    stats::disable();
}

fn names(rows: &[stats::ItemTiming]) -> Vec<String> {
    rows.iter().map(|r| format!("{}:{}", r.kind.as_str(), r.item)).collect()
}

/// Nesting rule: a bracket inside a bracket charges only itself, so one row's
/// timer columns never exceed its total. Without the rule the inner phase
/// would be counted twice and a dump could claim more time than elapsed.
#[test]
fn a_nested_timer_does_not_double_count() {
    stats::enable();
    let rows = {
        let _scope = stats::scope(ScopeKind::Run, "nesting", "");
        stats::timed(Timer::Resolve, || {
            spin();
            stats::timed(Timer::Unify, spin);
        });
        drop(_scope);
        stats::take_rows()
    };
    let row = rows.iter().find(|r| r.module == "nesting").expect("the run row");
    let resolve = row.timers[Timer::Resolve as usize];
    let unify = row.timers[Timer::Unify as usize];
    assert!(unify > 0, "the inner phase is measured");
    assert!(resolve > 0, "so is the outer phase's own share");
    assert!(
        resolve + unify <= row.total_ns,
        "self times sum to at most the scope: resolve={resolve} unify={unify} total={}",
        row.total_ns,
    );
    stats::disable();
}

/// A run that asked for nothing collects nothing: the scope guard is one
/// branch and the row buffer stays empty.
#[test]
fn collection_is_off_until_it_is_asked_for() {
    stats::disable();
    let _ = stats::take_rows();
    assert!(!stats::collecting());
    {
        let _scope = stats::scope(ScopeKind::Item, "quiet", "nothing");
        spin();
    }
    assert!(stats::take_rows().is_empty(), "no rows without collection");
}

/// The kernel's counters are readable on their own, and `since` is the
/// difference the scope machinery reads.
#[test]
fn kernel_counters_are_snapshot_and_differenced() {
    let before = kstats::snapshot();
    let mut elab = Elaborator::with_prelude().expect("prelude");
    let errors = elab.check_module_source("counted", MODULE);
    assert!(errors.is_empty(), "{errors:?}");
    let delta = kstats::snapshot().since(&before);
    assert!(delta.conv_shortcut_hits + delta.conv_memo_hits + delta.conv_misses > 0);
    assert!(delta.eval_steps > 0);
    assert_eq!(
        delta.values().len(),
        kstats::Snapshot::NAMES.len(),
        "every counter is a named column",
    );
}

/// The TSV header is stable and carries every declared column, which is what
/// makes a dump readable by something other than the run that wrote it.
#[test]
fn the_dump_header_names_every_column() {
    let header = stats::header();
    let columns: Vec<&str> = header.trim_end().split('\t').collect();
    assert_eq!(&columns[..5], ["scope", "module", "item", "total_ns", "other_ns"]);
    for name in Timer::NAMES {
        assert!(columns.contains(name), "missing timer column {name}");
    }
    for name in Counter::NAMES {
        assert!(columns.contains(name), "missing counter column {name}");
    }
    for name in kstats::Snapshot::NAMES {
        assert!(columns.contains(name), "missing kernel counter column {name}");
    }
    assert_eq!(
        columns.len(),
        5 + Timer::NAMES.len() + Counter::NAMES.len() + kstats::Snapshot::NAMES.len() + 4,
        "the four value-metric columns close the row",
    );
}

/// A conversion that fails for exhausted fuel and one that fails on a
/// mismatch are different diagnoses and get different columns
/// (`issues/generated-proof-cost-diagnostics.md`).
#[test]
fn a_mismatch_and_an_exhaustion_are_separate_columns() {
    let before = kstats::snapshot();
    let mut elab = Elaborator::with_prelude().expect("prelude");
    // `n = Succ(n)` is a conversion the kernel must refuse on a genuine
    // mismatch: the two sides are both well-formed and neither diverges.
    let errors = elab.check_module_source(
        "mismatch",
        "theorem wrong(n: Nat): n = Succ(n) { refl }\n",
    );
    assert!(!errors.is_empty(), "the fixture must fail to check");
    let delta = kstats::snapshot().since(&before);
    assert!(
        delta.conv_not_convertible > 0,
        "a real mismatch is counted as one, not as exhausted fuel",
    );
    assert_eq!(delta.conv_out_of_fuel, 0, "and nothing ran out of fuel here");
}

fn spin() {
    // Enough work that the wall clock moves; the assertions are about
    // relations between the numbers, never about their size.
    let start = std::time::Instant::now();
    let mut n = 0u64;
    while start.elapsed().as_micros() < 200 {
        n = n.wrapping_add(1);
    }
    std::hint::black_box(n);
}

/// `HEATHER_TIMINGS_DIR`: a named test thread keeps an ambient copy of its
/// rows and writes them when it exits, without turning explicit collection on
/// — so this binary, re-run as a child with the variable set, leaves a table
/// for `collection_is_off_until_it_is_asked_for` (which still passes: it
/// asserts `collecting()` is false) and one for the module check below.
#[test]
fn a_timings_dir_leaves_a_table_per_test_thread() {
    if std::env::var_os("HEATHER_TIMINGS_DIR").is_some() {
        return; // the child run: nothing to re-spawn
    }
    let dir = std::env::temp_dir().join(format!("heather-timings-dir-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "a_checked_module_attributes_by_declaration", "collection_is_off_until_it_is_asked_for", "--test-threads", "2"])
        .env("HEATHER_TIMINGS_DIR", &dir)
        .output()
        .unwrap();
    assert!(out.status.success(), "child run failed:\n{}", String::from_utf8_lossy(&out.stdout));
    let tables: Vec<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).collect();
    let checked = tables.iter()
        .find(|p| p.file_name().unwrap().to_string_lossy().contains(".a_checked_module_attributes_by_declaration."))
        .unwrap_or_else(|| panic!("no table for the module test among {tables:?}"));
    assert!(checked.file_name().unwrap().to_string_lossy().starts_with("instrumentation."), "{checked:?}");
    let text = std::fs::read_to_string(checked).unwrap();
    assert!(text.starts_with("scope\tmodule\titem\t"), "the --timings header");
    assert!(text.lines().any(|l| l.starts_with("item\tprobe\tdouble\t")), "a row per declaration:\n{text}");
    let _ = std::fs::remove_dir_all(&dir);
}
