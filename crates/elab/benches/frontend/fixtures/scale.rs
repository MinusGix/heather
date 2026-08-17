//! Generated scale: what happens to the frontend as a *file* grows, with
//! nothing clever in it.
//!
//! Sources are generated here rather than committed as `.hthr` files. The
//! kernel suite's precedent is generated corpora too (`fixtures/terms.rs`),
//! and the argument is the same one plus a second: a swept family is four
//! files that differ only in a loop bound, so committing them commits the
//! generator's output instead of the generator, and the sweep can never be
//! extended without a diff nobody reads. The committed `.hthr` files stay
//! what they are for: real proofs, in `lib/`.

use crate::harness::{Case, Family};
use heather_elab::IndexedRoute;

use super::{cloned_runner, prelude, validate, validate_route};

pub fn families() -> Vec<Family> {
    vec![declarations(), wide_inductive()]
}

/// `n` independent declarations, each a small `fn` plus the `theorem` that
/// runs it. Every one of them looks the same to the elaborator; what grows
/// is Ψ, the global name table, and the number of times the kernel gate is
/// entered.
fn declarations() -> Family {
    let src = |n: u64| {
        let mut s = String::from(
            "fn base(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => Succ(k) } }\n",
        );
        for i in 0..n {
            s.push_str(&format!(
                "fn f{i}(a: Nat, b: Nat) -> Nat {{ let x = base(a); Succ(x) }}\n\
                 theorem t{i}(): f{i}(1, 2) = 2 {{ refl }}\n"
            ));
        }
        s
    };
    Family {
        name: "scale/declarations",
        what: "n independent fn+theorem pairs — file size with no pathology in it",
        unit: "decls",
        // Linear is the claim: nothing in a declaration should cost more
        // because an unrelated declaration exists. A superlinear reading
        // here means a per-declaration walk over Ψ.
        expect_slope: Some((0.80, 1.30)),
        cases: sweep("scale/declarations", &[16, 32, 64, 128], src),
    }
}

/// One tier-0 inductive with `n` constructors, and one `fn` that matches all
/// `n` arms. The lowering builds a recursor whose motive and branch
/// telescope grow with the constructor count, so this is the elaborator's
/// own generated-term volume — the cheap, unindexed version of what
/// `forded.rs` measures.
fn wide_inductive() -> Family {
    let src = |n: u64| {
        let ctors: Vec<String> =
            (0..n).map(|i| format!("K{i}(x{i}: Nat)")).collect();
        let arms: Vec<String> =
            (0..n).map(|i| format!("        K{i}(v) => Succ(v),")).collect();
        format!(
            "inductive W {{ {} }}\nfn wread(w: W) -> Nat {{\n    match w {{\n{}\n    }}\n}}\n",
            ctors.join(", "),
            arms.join("\n"),
        )
    };
    Family {
        name: "scale/wide-inductive",
        what: "an inductive with n constructors and the n-arm match over it",
        unit: "ctors",
        // Quadratic by construction and not a defect: the recursor has n
        // branches and each branch's telescope mentions the motive, so the
        // emitted term is O(n²) before anything checks it. The band is
        // recorded rather than claimed — what it guards is a *third* power
        // appearing.
        //
        // 2026-08-17, re-recorded (issues/frontend-benchmarks.md): **1.23**,
        // measured as the mean of six consecutive runs whose whole range was
        // 1.22-1.25. The 1.30 floor had been exited from below since at least
        // 2026-08-16 and the exit was not noise; the band now spans the
        // measurement +/-0.35, which is the same distance `--check` calls a
        // slope drift, so band and drift gate mean the same thing by "moved".
        expect_slope: Some((0.90, 1.60)),
        cases: sweep("scale/wide-inductive", &[4, 8, 16, 32], src),
    }
}

/// Build one case per size: generate, validate, then hand the harness a
/// closure that checks the generated source against a cloned prelude.
pub fn sweep(
    what: &'static str,
    sizes: &[u64],
    src: impl Fn(u64) -> String,
) -> Vec<Case> {
    let base = prelude();
    // In smoke mode only the smallest size is built at all: validating a
    // generated source means elaborating it, so construction is where this
    // suite's seconds go (crate::harness::smoke).
    let sizes = if crate::harness::smoke() { &sizes[..1] } else { sizes };
    sizes
        .iter()
        .map(|&n| {
            let text = src(n);
            validate(&format!("{what}:{n}"), &text);
            let (run, cell) = cloned_runner(base.clone(), text);
            Case::new(n, 0, run).with_phases(cell)
        })
        .collect()
}

/// A swept indexed family whose smallest case first pins the classifier's
/// route. Later sizes share the same source schema and only vary its width.
pub fn indexed_sweep(
    what: &'static str,
    sizes: &[u64],
    declaration: &str,
    route: IndexedRoute,
    src: impl Fn(u64) -> String,
) -> Vec<Case> {
    let base = prelude();
    let sizes = if crate::harness::smoke() { &sizes[..1] } else { sizes };
    sizes
        .iter()
        .enumerate()
        .map(|(i, &n)| {
            let text = src(n);
            if i == 0 {
                validate_route(&format!("{what}:{n}"), &text, declaration, route);
            } else {
                validate(&format!("{what}:{n}"), &text);
            }
            let (run, cell) = cloned_runner(base.clone(), text);
            Case::new(n, 0, run).with_phases(cell)
        })
        .collect()
}
