//! The meaning check for structural recursion (issues/recursion-meaning-check.md,
//! `crates/elab/src/meaning.rs`): with the check on (`set_meaning_check`,
//! `heather check --meaning-check`), every structurally recursive `fn` is
//! checked to unfold to its own source, so a lowering that computes something
//! else is refused, located at the declaration, rather than silently accepted.
//!
//! The negative controls need a real miscompile. The planner refuses or
//! re-routes every one known today, so they run with it switched off
//! (`skip_recursion_plan`), which reproduces exactly the lowering the planner's
//! past misses produced — and each control first shows, by `refl`, that the
//! compiled function computes the wrong answer.

use heather_elab::{Elaborator, Lint};

use crate::support;

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

/// A member whose parameter has the member's base name (`Stmt::weights`'s
/// `weights`, `Scope::nodes`'s `nodes` in the library): the body's bare
/// `count` is the parameter, and the self-calls are method calls, so the
/// restated source keeps the parameter instead of naming the function.
#[test]
fn a_parameter_named_like_its_member_is_not_the_self_reference() {
    let src = "
        inductive Tree { Leaf, Node(l: Tree, r: Tree) }
        fn Tree::count(self t: Tree, count: Nat) → Nat {
            match t { Leaf => Succ(count), Node(l, r) => r.count(l.count(count)) }
        }
        inductive Seq { Done, More(n: Nat, rest: Seq) }
        fn Seq::sum(self s: Seq, sum: Nat) → Nat {
            match s { Done => sum, More(_, rest) => rest.sum(Succ(sum)) }
        }
    ";
    let ws = reviewed(src);
    assert!(ws.is_empty(), "{ws:?}");
}

/// An interface definition's body is withheld at open arguments once it is
/// registered (issues/interface-definitions.md), where `refl` could not
/// unfold it. It is elaborated as the plain `fn` first, and checked there,
/// before the body is withheld: it holds, and nothing is reported.
#[test]
fn an_interface_definition_is_checked_before_its_body_is_withheld() {
    let src = "
        interface fn twice(n: Nat) → Nat { match n { Zero => 0, Succ(k) => Succ(Succ(twice(k))) } }
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

/// The check is off by default (until its cost comes down): then, outside
/// review mode, nothing is stated, and a miscompile is accepted silently.
#[test]
fn with_the_check_off_nothing_is_stated_outside_review_mode() {
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

/// With the check off, review mode still reports a miscompile, as the
/// `recursion-meaning` lint rather than a refusal.
#[test]
fn with_the_check_off_review_mode_reports_a_miscompile() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.skip_recursion_plan();
    e.set_review_lints(true);
    let src = "
        fn u(n: Nat, x: Nat) → Nat {
            let y = Succ(x);
            match n { Zero => y, Succ(k) => u(k, Succ(Succ(x))) }
        }
    ";
    assert!(e.check_source(src).is_empty());
    let ws = meaning_warnings(&mut e);
    assert_eq!(ws.len(), 1, "{ws:?}");
    assert!(ws[0].contains("`u` does not unfold to its source"), "{ws:?}");
}

/// The miscompile `src` reproduces with the planner and the check off
/// (`refl` proves `wrong`, a value the source does not compute), and with
/// the check on it is refused, for not unfolding to its source, located at
/// the declaration.
fn refused_miscompile(src: &str, wrong: &str, name: &str) {
    let mut shown = Elaborator::with_prelude().expect("prelude");
    shown.skip_recursion_plan();
    shown.set_meaning_check(false);
    let errors = shown.check_source(&format!("{src}\n{wrong}"));
    assert!(errors.is_empty(), "the miscompile reproduces: {errors:?}");
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.skip_recursion_plan();
    e.set_meaning_check(true);
    let rendered = support::assert_refused(
        &mut e,
        "miscompile",
        src,
        support::Refusal::Says(&format!("the compiled `{name}` does not unfold to its source")),
    );
    let at = src.find(&format!("fn {name}(")).expect("the declaration");
    let line = src[..at].lines().count();
    assert!(rendered.starts_with(&format!("{line}:")), "located at `fn {name}` (line {line}): {rendered}");
}

/// issues/recursion-let-reads-changing-parameter.md: a `let` above the
/// recursive `match` reads a parameter the self-call varies, and the
/// structural lowering keeps the top call's value at every level.
#[test]
fn a_stale_let_is_refused() {
    let src = "
        fn u(n: Nat, x: Nat) → Nat {
            let y = Succ(x);
            match n { Zero => y, Succ(k) => u(k, Succ(Succ(x))) }
        }
    ";
    // The source says u(1, x) = x + 3.
    refused_miscompile(src, "theorem wrong(x: Nat): u(1, x) = Succ(x) { refl }", "u");
}

/// PR #389's wrong meaning: a branch above the recursive `match` reads a
/// parameter the recursion varies, and is decided once, by the top call.
#[test]
fn a_branch_on_a_varied_parameter_is_refused() {
    let src = "
        fn v(d: Nat, n: Nat) → Nat {
            match d { Zero => 0, Succ(_) => match n { Zero => 7, Succ(k) => v(k, k) } }
        }
    ";
    // The source says v(1, 1) = v(0, 0) = 0.
    refused_miscompile(src, "theorem wrong(): v(1, 1) = 7 { refl }", "v");
}
