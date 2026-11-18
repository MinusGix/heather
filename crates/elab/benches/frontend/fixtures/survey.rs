//! Families found by the cold-library survey of 2026-11-18
//! (`issues/elaboration-cost-overview-2026-11-18.md`): each isolates one
//! cost that a heavy library declaration paid, so that a fix shows up here
//! as a moved slope or per-unit cost, not only as a faster library run.
//!
//! The `match/*` pair is one measurement and its control. Inside a plain
//! `match`, every term the checking fallback compares (`got` against
//! `expected`, syntactically different) is asked whether the match's test
//! occurs in either type, so that it can be carried along the arm's equation
//! (`docs/language/matching/arm-readings-design.md` §5,
//! [[match-arm-coercion-abstracts-both-types]]). The question was answered by
//! abstracting the test out of both types, a rebuild of each, and in
//! `supremum::OrderComplete::below_located` that was two thirds of the
//! declaration with every one of its 260 askings a miss. The two families
//! check the same `let`s, in an arm and outside any match; the control's
//! per-unit cost is what a check costs without the question, and the gap
//! between the two is the question's price.
//!
//! `loops/word-body` is a `for` over words whose body assigns a word field
//! `k` times, the shape of SHA-256's rounds. It was exponential in `k` until
//! the loop's companions stopped spelling a `let`'s value once per read
//! ([[word-loop-body-exponential]]).

use heather_elab::Elaborator;

use crate::harness::{Case, Family};

use super::cloned_runner;
use super::scale::sweep;

pub fn families() -> Vec<Family> {
    vec![match_arm_checks(), match_plain_checks(), match_arm_type_size(), loops_word_body()]
}

/// `k` lets, each checking `mk(e) : T(e)` against `Nat`: the types differ as
/// written and agree by δ, so each goes through the checking fallback. `e`
/// is `s` nested `mix`es of `n`, which is the size of both types.
fn checks(k: u64, s: u64, in_arm: bool) -> String {
    let mut e = String::from("n");
    for _ in 0..s {
        e = format!("mix(n, {e})");
    }
    let mut lets = String::new();
    for i in 0..k {
        lets.push_str(&format!("        let a{i}: Nat = mk({e});\n"));
    }
    let head = "fn mix(x, y: Nat) -> Nat { x }\nfn g(n: Nat) -> Nat { n }\nfn T(n: Nat) -> Type { Nat }\nfn mk(n: Nat) -> T(n) { 0 }\n";
    if in_arm {
        format!("{head}fn f(n: Nat) -> Nat {{\n    match g(n) {{\n      Zero => 0,\n      Succ(j) => {{\n{lets}        0\n      }}\n    }}\n}}\n")
    } else {
        format!("{head}fn f(n: Nat) -> Nat {{\n    {{\n{lets}        0\n    }}\n}}\n")
    }
}

/// **Lower bound: linear in k**, at the control's per-unit cost: whether the
/// test occurs in a type is a read of the type, and a miss should cost no
/// more than the comparison that sent the term there.
fn match_arm_checks() -> Family {
    Family {
        name: "match/arm-checks",
        what: "k fallback checks inside a plain match's arm (control: match/plain-checks)",
        unit: "checks",
        // Recorded, not claimed: 1.03 over 16..128 on the cloud box,
        // 2026-11-18, at 1.2 to 1.5 times the control's per-check cost;
        // 1.1 to 1.2 times once the occurrence test stopped weakening the
        // test at every node (same day).
        expect_slope: Some((0.68, 1.38)),
        cases: sweep("match/arm-checks", &[16, 32, 64, 128], |k| checks(k, 16, true)),
    }
}

/// The control: the same `k` checks with no `match` around them.
fn match_plain_checks() -> Family {
    Family {
        name: "match/plain-checks",
        what: "the same k fallback checks outside any match (the control)",
        unit: "checks",
        // Recorded: 1.03 over 16..128 on the cloud box, 2026-11-18.
        expect_slope: Some((0.68, 1.38)),
        cases: sweep("match/plain-checks", &[16, 32, 64, 128], |k| checks(k, 16, false)),
    }
}

/// Thirty-two checks in an arm, over types of growing size. **Lower bound:
/// the control's**, which is linear in `s` because the comparison itself
/// reads the types.
fn match_arm_type_size() -> Family {
    Family {
        name: "match/arm-type-size",
        what: "32 fallback checks in a plain match's arm, over types of size s",
        unit: "type nodes",
        // Recorded: 0.94 over 8..64 on the cloud box, 2026-11-18.
        expect_slope: Some((0.59, 1.29)),
        cases: sweep("match/arm-type-size", &[8, 16, 32, 64], |s| checks(32, s, true)),
    }
}

/// An elaborator with `bitvec_omega`'s closure checked from source: what a
/// `for` over words needs (`u64`, and the word range's `decreases` proof).
/// Setup, never timed.
fn words_base() -> Elaborator {
    let mut e = super::prelude();
    let root = super::corpus::lib_dir().join("std/tactic/bitvec_omega.hthr");
    for (module, src) in super::corpus::closure(&root) {
        let errs = e.check_module_source(&module, &src);
        assert!(errs.is_empty(), "words base: module `{module}` does not check: {}", errs[0].render(&src));
    }
    e
}

/// `k` assignments `r.a := r.a + i` in the body of `for i in 0..8`, `r` a
/// record of two `u64`s. **Lower bound: linear in k**, as the same body over
/// `Nat` is. It was exponential (slope 3.47 over 4..7, 2026-11-18): the
/// measured loop's companions (`#ext`, `_unfold`, `#induct`) substitute each
/// `let` into the next, and `r := r with { a = r.a + i }` reads `r` twice, so
/// the spelled body doubled per statement and every operator's carrier probe
/// re-elaborated it. A value read twice is now bound once
/// (`measure::subst_shared`).
fn loops_word_body() -> Family {
    let base = words_base();
    let src = |k: u64| {
        let body = "        r.a := r.a + i;\n".repeat(k as usize);
        format!("import logic;\nimport bitvec;\nimport bitvec_omega;\nrecord R {{ a: u64, b: u64 }}\nfn R::f(mut self r: R) -> u64 {{\n    for i in 0..8 {{\n{body}    }}\n    r.a\n}}\n")
    };
    let sizes: &[u64] = if crate::harness::smoke() { &[2] } else { &[8, 16, 32, 64] };
    let cases = sizes
        .iter()
        .map(|&k| {
            let text = src(k);
            let errs = base.clone().check_source(&text);
            assert!(errs.is_empty(), "fixture `loops/word-body:{k}` does not check: {}", errs[0].render(&text));
            let (run, cell) = cloned_runner(base.clone(), text);
            Case::new(k, 0, run).with_phases(cell)
        })
        .collect();
    Family {
        name: "loops/word-body",
        what: "k word-field assignments in a `for` over words",
        unit: "statements",
        // Recorded: 0.75 over 8..64 on the cloud box, 2026-11-18, under a
        // fixed second of setup; the last doubling alone is 1.2.
        expect_slope: Some((0.4, 1.1)),
        cases,
    }
}
