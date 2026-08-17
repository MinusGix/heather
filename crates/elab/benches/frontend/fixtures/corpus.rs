//! The corpus: real library files, timed the way `heather check` checks them
//! (fresh prelude'd elaborator per file, `crates/cli/src/main.rs`).
//!
//! No exponent is claimed here. The x-axis is source bytes across unrelated
//! files, and `lib/ir_v1.hthr` is not "a bigger `lib/vec_code.hthr`" — it is
//! a file of deep proofs whose cost is conversion, not size. What the corpus
//! reports is absolute latency and the **phase split**: how much of the wait
//! is parsing, how much is the elaborator, how much is the kernel gate
//! re-checking what the elaborator built.

use std::path::{Path, PathBuf};

use heather_elab::Elaborator;

use crate::harness::{Case, Family};

use super::{fresh_closure_runner, validate_closure};

const VEC_CODE: &str = include_str!("../../../../../lib/vec_code.hthr");
const IR_V1: &str = include_str!("../../../../../lib/ir_v1.hthr");

fn lib_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lib")
}

/// The import closure of a library file, in loader order (dependencies first,
/// root last) — computed by **the CLI's own loader**, not listed here.
///
/// It used to be listed (`bool`, `nat`, `ir_v1`), and the list went stale the
/// day `lib/std/bool.hthr` gained `import logic;`
/// (issues/frontend-bench-ir-closure-stale.md). The failure was quiet in the
/// worst way: `bool`'s unresolvable import aborts `check_module_source`
/// *before* the module registers a scope, so `nat` then could not see `bool`
/// and `ir_v1` could not see `nat` — one missing name reported as three
/// broken modules, and a corpus case timing an elaborator that did almost no
/// work. The closure a fixture claims to time is a fact about the library, so
/// it is read from the library.
///
/// `-L lib/std` matches `crates/cli/src/main.rs`'s `DEFAULT_LIB`.
fn closure(file: &str) -> Vec<(String, String)> {
    let root = lib_dir().join(file);
    let search = [lib_dir().join("std")];
    let modules = heather_cli::loader::load(&root, &search)
        .unwrap_or_else(|e| panic!("corpus fixture `{file}`: {}", e.msg));
    modules.into_iter().map(|m| (m.name, m.src)).collect()
}

/// Everything up to the first theorem — every datatype, helper and
/// interpreter in the file and none of its proofs. The library keeps its
/// declarations ahead of its theorems, and `crates/elab/tests/ir_v1.rs`
/// splits it at the same seam for the same reason: it is the half whose cost
/// is *elaboration* rather than proof conversion.
fn decls_prefix(src: &str) -> String {
    let cut = src.find("\ntheorem ").expect("the library has theorems");
    src[..cut].to_string()
}

pub fn families() -> Vec<Family> {
    vec![prelude_family(), parse_family(), check_file()]
}

/// What every file pays before its own first declaration. This is the fixed
/// part of `heather check`'s per-file cost, and the reason the generated
/// families measure against a *cloned* prelude instead.
fn prelude_family() -> Family {
    // The second case is the justification for how the generated families
    // are timed (`super::cloned_runner`): they clone this instead of
    // rebuilding it, and the two numbers side by side are what makes that
    // an argument rather than an assumption.
    let base = super::prelude();
    Family {
        name: "corpus/prelude",
        what: "building a prelude'd elaborator — the per-file fixed cost the CLI pays",
        unit: "preludes",
        expect_slope: None,
        cases: vec![
            Case::named("build", 1, 1, || Elaborator::with_prelude().is_ok() as u64),
            Case::named("clone", 1, 1, move || {
                let e = base.clone();
                std::hint::black_box(&e);
                1
            }),
        ],
    }
}

fn check_file() -> Family {
    let mut cases = vec![];
    for (label, file, decls_only, heavy, budget_ns) in [
        // Budgets are alarms, not gates: each is ~100× (a small file, where
        // "still instant?" is the question) or ~5× (a big one, where the
        // question is "still tolerable?") of what it measured on
        // 2026-08-04. The gate against a 30% drift is the baseline
        // comparison; these fire when a file stops being usable at all.
        ("vec_code.hthr", "vec_code.hthr", false, false, 100_000_000u64),
        ("ir_v1.hthr:decls", "ir_v1.hthr", true, true, 8_000_000_000),
        // The latency budget, and the suite's alarm bell. Measured
        // 2026-08-04: **59 s** through the release CLI on a quiet machine,
        // 84–88 s from this harness while the machine carried a load
        // average of ~10 and the CPU sat at 96 °C. The ceiling is 150 s —
        // ~2.5× the quiet figure and ~1.7× the loaded one — because a
        // budget that a busy machine trips is a budget that gets deleted,
        // and what it is for is "the library file now takes five minutes".
        // It is deliberately *not* derived from the baseline: a budget that
        // moves with the recording is not a budget.
        ("ir_v1.hthr", "ir_v1.hthr", false, true, 150_000_000_000),
    ] {
        // Heavy cases were *unvalidated* for as long as validating one meant
        // ~90 s of `lib/ir_v1.hthr`; it is seconds now, so every corpus case
        // is validated again and its checksum is the Ψ-binding count that
        // validation returned — a count of declarations landed, not of errors
        // raised. That is what makes "the fixture is doing the same work"
        // checkable without a clock, which is exactly what the stale closure
        // (issues/frontend-bench-ir-closure-stale.md) needed and did not have.
        // In smoke mode the heavy cases are not built at all
        // (crate::harness::smoke).
        if heavy && crate::harness::smoke() {
            continue;
        }
        // The `ir_v1` cases are an import **closure**; `vec_code.hthr`
        // imports nothing and is a one-module closure, so both go through
        // the same loader and the same runner, and the corpus keeps timing
        // what the CLI does.
        let mut modules = closure(file);
        let root = &mut modules.last_mut().expect("a closure has a root").1;
        if decls_only {
            *root = decls_prefix(root);
        }
        // The x-axis stays the *root's* bytes: the label names the root, and
        // the imports are part of the wait, not part of the size.
        let size = root.len() as u64;
        let bindings = validate_closure(label, &modules);
        let (run, cell, first_error) = fresh_closure_runner(modules);
        let mut case = Case::named(label, size, bindings, run)
            .with_phases(cell)
            .with_budget(budget_ns)
            .with_diagnosis(first_error);
        if heavy {
            case = case.heavy();
        }
        cases.push(case);
    }
    Family {
        name: "corpus/check-file",
        what: "lib/*.hthr end to end, as `heather check` does it (prelude included)",
        unit: "bytes",
        // Unrelated files: a slope over them would be arithmetic about the
        // corpus, not a claim about the frontend.
        expect_slope: None,
        cases,
    }
}

/// Parsing alone, over the same corpus. Its own family rather than only the
/// split line, because parse time is the one phase that is cheap enough to
/// measure properly (many rounds) and the one whose cost model is simple
/// enough to have an expectation: linear in source bytes.
pub fn parse_family() -> Family {
    let mut cases = vec![];
    for (label, src) in [("vec_code.hthr", VEC_CODE), ("ir_v1.hthr", IR_V1)] {
        let owned = src.to_string();
        // The item count is the checksum: a parser that started dropping
        // items would otherwise report a win.
        let items = heather_syntax::parse_file(src).expect("parses").items.len() as u64;
        cases.push(Case::named(label, src.len() as u64, items, move || {
            heather_syntax::parse_file(&owned).expect("parses").items.len() as u64
        }));
    }
    Family {
        name: "corpus/parse",
        what: "the parser alone over the corpus — the cheap phase, measured properly",
        unit: "bytes",
        expect_slope: None,
        cases,
    }
}
