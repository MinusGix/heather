//! The meaning check for structural recursion (issues/recursion-meaning-check.md,
//! `crates/elab/src/meaning.rs`): in review mode, every structurally recursive
//! `fn` is checked to unfold to its own source, so a lowering that computes
//! something else is reported rather than silently accepted.
//!
//! The negative controls need a real miscompile. The planner refuses or
//! re-routes every one known today, so they run with it switched off
//! (`skip_recursion_plan`), which reproduces exactly the lowering the planner's
//! past misses produced — and each control first shows, by `refl`, that the
//! compiled function computes the wrong answer.

use heather_elab::{Elaborator, Lint};

fn meaning_warnings(e: &mut Elaborator) -> Vec<String> {
    e.take_warnings()
        .into_iter()
        .filter(|w| w.lint == Lint::RecursionMeaning)
        .map(|w| w.msg)
        .collect()
}

fn reviewed(src: &str) -> Vec<String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.set_review_lints(true);
    let errors = e.check_source(src);
    assert!(errors.is_empty(), "{errors:?}");
    meaning_warnings(&mut e)
}

/// Plain structural recursion, an accumulator the recursion generalizes, a
/// case split under the recursion, a polymorphic list recursion, and a
/// recursion under an outer case split (#389's `inner`, which needs the split
/// parameter to be a constructor before the two sides meet): each unfolds to
/// its source.
#[test]
fn ordinary_structural_recursions_mean_their_source() {
    let src = "
        inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
        fn double(n: Nat) → Nat { match n { Zero => 0, Succ(k) => Succ(Succ(double(k))) } }
        fn acc(n: Nat, x: Nat) → Nat { match n { Zero => x, Succ(k) => acc(k, Succ(x)) } }
        fn walk(d: Nat, n: Nat) → Nat {
            match d { Zero => 0, Succ(k) => match n { Zero => walk(k, n), Succ(_) => Succ(walk(k, n)) } }
        }
        fn len<A>(xs: List<A>) → Nat { match xs { Nil => 0, Cons(_, t) => Succ(len(t)) } }
        fn inner(d: Nat, n: Nat) → Nat {
            match d { Zero => 0, Succ(k) => match n { Zero => d, Succ(m) => inner(d, m) } }
        }
        fn keep(n: Nat, x: Nat) → Nat {
            let y = Succ(x);
            match n { Zero => y, Succ(k) => keep(k, x) }
        }
    ";
    let ws = reviewed(src);
    assert!(ws.is_empty(), "{ws:?}");
}

/// A course-of-values recursion reads the predecessor's predecessor, so its
/// source's nested `match` reduces only after a second split: the check
/// deepens instead of reporting it.
#[test]
fn a_course_of_values_recursion_means_its_source_at_depth_two() {
    let src = "
        fn half(n: Nat) → Nat {
            match n { Zero => 0, Succ(k) => match k { Zero => 0, Succ(l) => Succ(half(l)) } }
        }
    ";
    let ws = reviewed(src);
    assert!(ws.is_empty(), "{ws:?}");
}

/// Outside review mode nothing is stated, and nothing is reported.
#[test]
fn the_meaning_check_is_silent_outside_review_mode() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.skip_recursion_plan();
    let src = "
        fn u(n: Nat, x: Nat) → Nat {
            let y = Succ(x);
            match n { Zero => y, Succ(k) => u(k, Succ(Succ(x))) }
        }
    ";
    assert!(e.check_source(src).is_empty());
    assert!(meaning_warnings(&mut e).is_empty());
}

fn miscompiled(src: &str, wrong: &str) -> Vec<String> {
    // The compiled function computes the wrong answer: `refl` proves it.
    let mut shown = Elaborator::with_prelude().expect("prelude");
    shown.skip_recursion_plan();
    let errors = shown.check_source(&format!("{src}\n{wrong}"));
    assert!(errors.is_empty(), "the miscompile reproduces: {errors:?}");
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.skip_recursion_plan();
    e.set_review_lints(true);
    let errors = e.check_source(src);
    assert!(errors.is_empty(), "{errors:?}");
    meaning_warnings(&mut e)
}

/// issues/recursion-let-reads-changing-parameter.md: a `let` above the
/// recursive `match` reads a parameter the self-call varies, and the
/// structural lowering keeps the top call's value at every level.
#[test]
fn a_stale_let_is_reported() {
    let src = "
        fn u(n: Nat, x: Nat) → Nat {
            let y = Succ(x);
            match n { Zero => y, Succ(k) => u(k, Succ(Succ(x))) }
        }
    ";
    // The source says u(1, x) = x + 3.
    let ws = miscompiled(src, "theorem wrong(x: Nat): u(1, x) = Succ(x) { refl }");
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert!(ws[0].contains("`u` does not unfold to its source"), "{ws:?}");
}

/// PR #389's wrong meaning: a branch above the recursive `match` reads a
/// parameter the recursion varies, and is decided once, by the top call.
#[test]
fn a_branch_on_a_varied_parameter_is_reported() {
    let src = "
        fn v(d: Nat, n: Nat) → Nat {
            match d { Zero => 0, Succ(_) => match n { Zero => 7, Succ(k) => v(k, k) } }
        }
    ";
    // The source says v(1, 1) = v(0, 0) = 0.
    let ws = miscompiled(src, "theorem wrong(): v(1, 1) = 7 { refl }");
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert!(ws[0].contains("`v` does not unfold to its source"), "{ws:?}");
}
