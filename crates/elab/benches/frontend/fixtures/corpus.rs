//! The corpus: real library files, timed the way `heather check` checks them
//! (fresh prelude'd elaborator per file, `crates/cli/src/main.rs`).
//!
//! No exponent is claimed here. The x-axis is source bytes across unrelated
//! files, and `lib/ir_v1.hthr` is not "a bigger `lib/vec_code.hthr`" — it is
//! a file of deep proofs whose cost is conversion, not size. What the corpus
//! reports is absolute latency and the **phase split**: how much of the wait
//! is parsing, how much is the elaborator, how much is the kernel gate
//! re-checking what the elaborator built.

use heather_elab::Elaborator;

use crate::harness::{Case, Family};

use super::{fresh_runner, validate};

const VEC_CODE: &str = include_str!("../../../../../lib/vec_code.hthr");
const IR_V1: &str = include_str!("../../../../../lib/ir_v1.hthr");

/// Everything up to the first theorem — every datatype, helper and
/// interpreter in the file and none of its proofs. The library keeps its
/// declarations ahead of its theorems, and `crates/elab/tests/ir_v1.rs`
/// splits it at the same seam for the same reason: it is the half whose cost
/// is *elaboration* rather than proof conversion.
fn ir_v1_decls() -> &'static str {
    let cut = IR_V1.find("\ntheorem ").expect("the library has theorems");
    &IR_V1[..cut]
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
    for (label, src, heavy, budget_ns) in [
        // Budgets are alarms, not gates: each is ~100× (a small file, where
        // "still instant?" is the question) or ~5× (a big one, where the
        // question is "still tolerable?") of what it measured on
        // 2026-08-04. The gate against a 30% drift is the baseline
        // comparison; these fire when a file stops being usable at all.
        ("vec_code.hthr", VEC_CODE, false, 100_000_000u64),
        ("ir_v1.hthr:decls", ir_v1_decls(), true, 8_000_000_000),
        // The latency budget, and the suite's alarm bell. Measured
        // 2026-08-04: **59 s** through the release CLI on a quiet machine,
        // 84–88 s from this harness while the machine carried a load
        // average of ~10 and the CPU sat at 96 °C. The ceiling is 150 s —
        // ~2.5× the quiet figure and ~1.7× the loaded one — because a
        // budget that a busy machine trips is a budget that gets deleted,
        // and what it is for is "the library file now takes five minutes".
        // It is deliberately *not* derived from the baseline: a budget that
        // moves with the recording is not a budget.
        ("ir_v1.hthr", IR_V1, true, 150_000_000_000),
    ] {
        // A heavy case is not *validated* at all: validating means checking
        // the file, so it would add a whole extra `lib/ir_v1.hthr` (~90 s)
        // to every run on top of the probe and the two sampled rounds. The
        // harness's checksum still catches a file that stopped checking —
        // it reports a count instead of a message, and the message is one
        // `heather check lib/ir_v1.hthr` away. In smoke mode the case is
        // not built at all (crate::harness::smoke).
        if heavy {
            if crate::harness::smoke() {
                continue;
            }
        } else {
            validate(label, src);
        }
        let (run, cell) = fresh_runner(src.to_string());
        let mut case = Case::named(label, src.len() as u64, 0, run)
            .with_phases(cell)
            .with_budget(budget_ns);
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
