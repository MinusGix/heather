//! The fixture families, and the two ways a fixture runs a source file.
//!
//! Both ways are real user latency, and which one a family uses is a
//! statement about what it measures:
//!
//! - [`fresh_closure_runner`] builds a **new prelude'd elaborator per run**
//!   and feeds it a whole import closure, which is exactly what
//!   `heather check <file>` does per root file (`crates/cli/src/main.rs`).
//!   The corpus uses it, because the corpus number is meant to be the number
//!   a user waits for. A one-file corpus entry is a one-module closure.
//! - [`cloned_runner`] clones a prelude'd elaborator instead. Measured
//!   2026-08-04: building the prelude is ~100 µs, cloning one is ~104 ns —
//!   a thousandfold, and both numbers are in the report (`corpus/prelude`
//!   has a case for each). 100 µs is nothing against `ir_v1.hthr` and
//!   everything against a generated fixture at its smallest size, and a
//!   fixed cost under a log-log fit does not merely add noise, it
//!   *flattens the exponent* — which is the number this suite reports.
//!   Generated families use it, and their times are therefore "against a
//!   warm prelude".
//!
//! Both are repeatable, which the harness requires: `check_source` mutates
//! the elaborator, so a timed closure may never reuse one.

use std::cell::{Cell, RefCell};
use heather_kernel::rc::Rc;
use std::time::Instant;

use heather_elab::{Elaborator, IndexedRoute, SemanticImage, stats};
use heather_syntax::parse_file;

use crate::harness::{Family, Phases};

pub mod corpus;
pub mod forded;
pub mod indexed;
pub mod intricate;
pub mod meta;
pub mod rewriting;
pub mod scale;

/// Every family, in report order. Constructing them does all the setup —
/// source generation, prelude construction, and one validating run each — so
/// that the timing loop times nothing else (the kernel suite's fixture rule
/// 1, docs/infrastructure/benchmarking.md).
pub fn all() -> Vec<Family> {
    let mut v = vec![];
    v.extend(corpus::families());
    v.extend(scale::families());
    v.extend(forded::families());
    v.extend(indexed::families());
    v.extend(intricate::families());
    v.extend(meta::families());
    v.extend(rewriting::families());
    v
}

/// A prelude'd elaborator to clone from. Built once per family that wants
/// one; failing here is a broken prelude, not a slow one.
pub fn prelude() -> Elaborator {
    Elaborator::with_prelude().expect("the prelude must check")
}

/// Panic unless `src` checks cleanly against a fresh elaborator — the
/// fixture-validation rule, run at setup. A fixture that stopped doing its
/// work gets *faster*, so an unvalidated benchmark reports a win for a bug.
pub fn validate(what: &str, src: &str) -> Elaborator {
    let mut e = prelude();
    let errs = e.check_source(src);
    assert!(
        errs.is_empty(),
        "fixture `{what}` does not check ({} error(s)); first:\n{}",
        errs.len(),
        errs[0].render(src)
    );
    e
}

/// Validate a route-sensitive fixture and assert the declaration took the
/// lowering the fixture claims to measure.
pub fn validate_route(
    what: &str,
    src: &str,
    declaration: &str,
    expected: IndexedRoute,
) -> Elaborator {
    let e = validate(what, src);
    assert_eq!(
        e.indexed_route(declaration),
        Some(expected),
        "fixture `{what}` does not exercise its claimed indexed route"
    );
    e
}

/// Attribute this run's phases — **only on the harness's probe run**, never
/// on a sampled one.
///
/// The parse has to be timed on its own pass: it is a pure function of the
/// source, so a second parse measures the same work the run did, and
/// instrumenting `check_source` from inside would put a branch in the
/// elaborator for the benchmark's benefit. That extra pass costs time, which
/// is precisely why it must not happen inside a sampled round —
/// `crate::harness::probing` is the flag that keeps the two apart.
fn measure_phases(src: &str, cell: &Rc<Cell<Phases>>, total_ns: u64) {
    if !crate::harness::probing() {
        return;
    }
    let t = Instant::now();
    let parsed = parse_file(src);
    let parse_ns = t.elapsed().as_nanos() as u64;
    assert!(parsed.is_ok(), "a fixture that does not parse");
    cell.set(Phases { parse_ns, kernel_ns: stats::kernel_ns(), total_ns });
}

/// A run over a whole **import closure**, in the order the CLI's loader
/// produces (docs/language/modules-design.md §3.2): dependencies first, root last, one
/// shared elaborator. `ir_v1.hthr` became multi-file when the Nat kit
/// moved to `lib/std/num/nat.hthr`, so the number a user waits for is the closure
/// and not the root — timing the root alone would time a file that no longer
/// checks, and a fixture that stops working gets *faster*.
///
/// The checksum is the number of **Ψ bindings** the closure leaves behind —
/// a count of work *done*, not of errors. An error count is a poor checksum
/// for a corpus case: it is zero both when the closure checks and when a
/// declaration quietly stops being elaborated at all, and a fixture doing
/// less work gets faster. A failed declaration registers nothing (globals and
/// Ψ are touched only after the kernel gate), so any lost declaration moves
/// this number.
/// A checksum is still only a *count*, though, and a count is a poor bug
/// report. The runner therefore also records the first diagnostic it saw,
/// rendered against the module it came from, and
/// [`crate::harness::Case::with_diagnosis`] hands it to the checksum
/// assertion. Diagnosing the stale closure of
/// issues/frontend-bench-ir-closure-stale.md cost a detour that this one line
/// would have saved.
pub fn fresh_closure_runner(
    modules: Vec<(String, String)>,
) -> (impl Fn() -> u64, Rc<Cell<Phases>>, Diagnosis) {
    let cell = Rc::new(Cell::new(Phases::default()));
    let out = cell.clone();
    let first: Diagnosis = Rc::new(RefCell::new(None));
    let seen = first.clone();
    // The phase split is attributed against the root's source, which is the
    // file the split is a statement about.
    let root = modules.last().expect("a closure has a root").1.clone();
    let run = move || {
        stats::reset_kernel_ns();
        let t = Instant::now();
        let mut e = Elaborator::with_prelude().expect("prelude");
        for (name, src) in &modules {
            let es = e.check_module_source(name, src);
            // Recording only the *first* error of the whole closure: a broken
            // import cascades (every later module fails on the module that
            // failed before it), so the first one is the one that explains
            // the rest.
            if let Some(e0) = es.first()
                && seen.borrow().is_none()
            {
                *seen.borrow_mut() = Some(format!("module `{name}`: {}", e0.render(src)));
            }
        }
        let done = e.psi().bindings.len() as u64;
        let total_ns = t.elapsed().as_nanos() as u64;
        measure_phases(&root, &out, total_ns);
        done
    };
    (run, cell, first)
}

/// The first diagnostic a runner saw, if any — written by the run, read by
/// the checksum assertion.
pub type Diagnosis = Rc<RefCell<Option<String>>>;

/// [`validate`] for a closure: every module must check, in order. Returns the
/// closure's Ψ-binding count — the checksum the timed runs must reproduce.
///
/// The heavy corpus cases used to skip this, because validating one meant
/// checking `ir_v1.hthr` and that was ~90 s. It is seconds now (the
/// kernel-side rounds of early August), so the suite's own fixture rule — *a
/// fixture validates before it is timed* — is affordable again, and the
/// exception that let issues/frontend-bench-ir-closure-stale.md's closure fail
/// for a day is gone.
pub fn validate_closure(what: &str, modules: &[(String, String)]) -> u64 {
    let mut e = prelude();
    for (name, src) in modules {
        let errs = e.check_module_source(name, src);
        assert!(
            errs.is_empty(),
            "fixture `{what}` does not check at module `{name}` ({} error(s)); first:\n{}",
            errs.len(),
            errs[0].render(src)
        );
    }
    e.psi().bindings.len() as u64
}

/// A run against a warm prelude: the clone is inside the timing, because it
/// is the price of making the run repeatable and it is microseconds.
pub fn cloned_runner(base: Elaborator, src: String) -> (impl Fn() -> u64, Rc<Cell<Phases>>) {
    let cell = Rc::new(Cell::new(Phases::default()));
    let out = cell.clone();
    let run = move || {
        stats::reset_kernel_ns();
        let t = Instant::now();
        let mut e = base.clone();
        let errs = e.check_source(&src);
        let total_ns = t.elapsed().as_nanos() as u64;
        measure_phases(&src, &out, total_ns);
        errs.len() as u64
    };
    (run, cell)
}

/// A run in a fresh suffix over a captured semantic image. Unlike
/// [`cloned_runner`], this seals module-sized registry deltas before timing,
/// so growth in the imported prefix can expose first-write detachment.
pub fn image_runner(image: SemanticImage, src: String) -> (impl Fn() -> u64, Rc<Cell<Phases>>) {
    let cell = Rc::new(Cell::new(Phases::default()));
    let out = cell.clone();
    let run = move || {
        stats::reset_kernel_ns();
        let t = Instant::now();
        let mut e = image.elaborator();
        let errs = e.check_source(&src);
        let total_ns = t.elapsed().as_nanos() as u64;
        measure_phases(&src, &out, total_ns);
        errs.len() as u64
    };
    (run, cell)
}
