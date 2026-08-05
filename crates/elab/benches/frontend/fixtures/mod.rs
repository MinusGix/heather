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
//!   has a case for each). 100 µs is nothing against `lib/ir_v1.hthr` and
//!   everything against a generated fixture at its smallest size, and a
//!   fixed cost under a log-log fit does not merely add noise, it
//!   *flattens the exponent* — which is the number this suite reports.
//!   Generated families use it, and their times are therefore "against a
//!   warm prelude".
//!
//! Both are repeatable, which the harness requires: `check_source` mutates
//! the elaborator, so a timed closure may never reuse one.

use std::cell::Cell;
use std::rc::Rc;
use std::time::Instant;

use heather_elab::{Elaborator, stats};
use heather_syntax::parse_file;

use crate::harness::{Family, Phases};

pub mod corpus;
pub mod forded;
pub mod meta;
pub mod scale;

/// Every family, in report order. Constructing them does all the setup —
/// source generation, prelude construction, and one validating run each — so
/// that the timing loop times nothing else (the kernel suite's fixture rule
/// 1, docs/benchmarking.md).
pub fn all() -> Vec<Family> {
    let mut v = vec![];
    v.extend(corpus::families());
    v.extend(scale::families());
    v.extend(forded::families());
    v.extend(meta::families());
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
pub fn validate(what: &str, src: &str) {
    let mut e = prelude();
    let errs = e.check_source(src);
    assert!(
        errs.is_empty(),
        "fixture `{what}` does not check ({} error(s)); first:\n{}",
        errs.len(),
        errs[0].render(src)
    );
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
/// produces (docs/modules-design.md §3.2): dependencies first, root last, one
/// shared elaborator. `lib/ir_v1.hthr` became multi-file when the Nat kit
/// moved to `lib/std/nat.hthr`, so the number a user waits for is the closure
/// and not the root — timing the root alone would time a file that no longer
/// checks, and a fixture that stops working gets *faster*.
///
/// The checksum is the total error count across the closure, so a module that
/// stopped checking is still visible as a changed count.
pub fn fresh_closure_runner(
    modules: Vec<(String, String)>,
) -> (impl Fn() -> u64, Rc<Cell<Phases>>) {
    let cell = Rc::new(Cell::new(Phases::default()));
    let out = cell.clone();
    // The phase split is attributed against the root's source, which is the
    // file the split is a statement about.
    let root = modules.last().expect("a closure has a root").1.clone();
    let run = move || {
        stats::reset_kernel_ns();
        let t = Instant::now();
        let mut e = Elaborator::with_prelude().expect("prelude");
        let mut errs = 0u64;
        for (name, src) in &modules {
            errs += e.check_module_source(name, src).len() as u64;
        }
        let total_ns = t.elapsed().as_nanos() as u64;
        measure_phases(&root, &out, total_ns);
        errs
    };
    (run, cell)
}

/// [`validate`] for a closure: every module must check, in order.
pub fn validate_closure(what: &str, modules: &[(String, String)]) {
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
