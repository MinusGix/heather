//! The meta-heavy fixture: implicit type arguments solved by inference,
//! nested so that the *type* the elaborator carries grows with the size.
//!
//! `issues/frontend-benchmarks.md` asks for one fixture that "keeps quadratic
//! blowups visible", and the shape that would blow up is a solved
//! instantiation being re-walked at every level of a nest: each `pair` call
//! solves two type parameters against a type that itself contains the
//! previous solution. Postponement and retry belong to
//! `issues/elab-unifier-completeness.md`; what this family assumes is only
//! that meta-heavy files exist to measure.
//!
//! One family, deliberately: the suite is a latency gate, not an inference
//! test suite, and the acceptance for inference is in
//! `crates/elab/tests/polymorphism.rs`.

use crate::harness::Family;

use super::scale::sweep;

const HEAD: &str = "\
fn id<A>(x: A) -> A { x }
inductive Pair<A, B> { MkPair(fst: A, snd: B) }
fn pair<A, B>(a: A, b: B) -> Pair<A, B> { MkPair(a, b) }
fn fst<A, B>(p: Pair<A, B>) -> A { match p { MkPair(a, b) => a } }
fn snd<A, B>(p: Pair<A, B>) -> B { match p { MkPair(a, b) => b } }
";

pub fn families() -> Vec<Family> {
    vec![nested_inference()]
}

fn nested_inference() -> Family {
    fn ty(d: u64) -> String {
        if d == 0 { "Nat".into() } else { format!("Pair<Nat, {}>", ty(d - 1)) }
    }
    fn val(d: u64) -> String {
        if d == 0 { "id(n)".into() } else { format!("pair(id(n), {})", val(d - 1)) }
    }
    let src = |d: u64| {
        // Build it (inference solving `A`/`B` at every level, in a checking
        // position against the written result type) and read it back down
        // (inference again, this time from the receiver's type).
        let mut proj = String::from("p");
        for _ in 0..d {
            proj = format!("snd({proj})");
        }
        format!(
            "{HEAD}fn build(n: Nat) -> {} {{ {} }}\nfn read(p: {}) -> Nat {{ {proj} }}\n",
            ty(d),
            val(d),
            ty(d),
        )
    };
    Family {
        name: "meta/nested-inference",
        what: "d nested implicit instantiations, built and projected back down",
        unit: "levels",
        // ~1.6 measured 2026-08-04. Above linear because the type at level d
        // has size d, so a walk per level is d² work in the source's own
        // terms — expected, and the band is set to catch it becoming cubic,
        // which is what a re-solved instantiation per level would look like.
        expect_slope: Some((1.20, 2.30)),
        cases: sweep("meta/nested-inference", &[4, 8, 16, 32], src),
    }
}
