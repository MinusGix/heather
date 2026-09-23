//! Auto-refl MVP: an empty proof block `{}` gets ONE speculative `refl`,
//! kept iff the kernel accepts it. Tracking issue:
//! `issues/auto-refl-empty-block.md`.
//!
//! The negative controls are the substance. A "trivial closer" that quietly
//! succeeds where it should not is worse than no closer at all, so every way
//! the speculation can fail is asserted to produce the *open goal listing* —
//! not a pass, not a panic, and not a kernel error about a term nobody wrote.

use heather_elab::{ElabError, Elaborator};

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

/// The rejection, plus the assertion that it is the *goal* mechanism talking.
fn open_goal(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected an open goal, but it elaborated"),
        Err(err @ ElabError::UnsolvedGoals { .. }) => err.render(src),
        Err(other) => panic!(
            "expected the open-goal listing, got a different error: {}",
            other.render(src)
        ),
    }
}

const ADD: &str = "fn add(a: Nat, b: Nat) -> Nat \
                   { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }";

// -- 1: what it closes ----------------------------------------------------

// The headline from the issue.
#[test]
fn an_empty_block_closes_a_computation() {
    ok(&format!("{ADD} theorem two_two(): add(2, 2) = 4 {{}}"));
}

// Axis 2/3 (docs/testing-generated-terms.md): **open** endpoints, where
// nothing evaluates to a numeral and the conversion is a real one. `add`
// recurses on its second argument, so this is definitional and the empty
// block closes it — while the mirror image below is not, and does not.
#[test]
fn an_empty_block_closes_an_open_definitional_equation() {
    ok(&format!("{ADD} theorem right_unit(n: Nat): add(n, 0) = n {{}}"));
}

// A `{}` is not restricted to a declaration body: any checking position. An
// annotated `let` is the cleanest one, and an `@`-call with its type argument
// given is the argument-position case.
//
// The *un*marked `sym({})` does not work, and that is not this feature's
// doing: an explicit argument of an implicit-taking callee is elaborated in
// inference mode until every meta its domain mentions is solved, so `{}` there
// has no goal to see — the same reason `refl` and `?` cannot go there either.
#[test]
fn an_empty_block_works_in_a_checking_argument_position() {
    ok(&format!(
        "{ADD} theorem two_two(): add(2, 2) = 4 {{ let p: (add(2, 2) = 4) = {{}}; p }}"
    ));
    ok(&format!(
        "{ADD} theorem flipped(): 4 = add(2, 2) {{ @sym<Nat>(add(2, 2), 4, {{}}) }}"
    ));
}

// …and inside a `match` arm, which is a checking position under a motive.
#[test]
fn an_empty_block_works_in_a_match_arm() {
    ok(&format!(
        "{ADD}
         theorem left_unit(n: Nat): add(0, n) = n {{
             match n {{ Zero => {{}}, Succ(k) => Nat::cong_succ(left_unit(k)) }}
         }}"
    ));
}

// -- 2: negative controls -------------------------------------------------

// A false equation: the goal stays open, and the message is the goal listing
// rather than a `NotConvertible` from the declaration's final kernel check.
#[test]
fn a_false_equation_leaves_the_goal_open() {
    let e = open_goal(&format!("{ADD} theorem two_five(): add(2, 2) = 5 {{}}"));
    assert!(e.contains("unsolved goals"), "{e}");
    assert!(e.contains("two_five"), "{e}");
}

// The other side of the `add` asymmetry: `add(0, n) = n` is *true* but not
// definitional (`add` recurses on the right), so one speculative `refl` is
// not enough and the goal stays open. This is the test that says the
// speculation is a kernel conversion and not a syntactic guess that got
// lucky.
#[test]
fn a_true_but_non_definitional_equation_leaves_the_goal_open() {
    let e = open_goal(&format!("{ADD} theorem left_unit(n: Nat): add(0, n) = n {{}}"));
    assert!(e.contains("unsolved goals"), "{e}");
}

// A goal that is not an equation at all — a *value*. Nothing about `refl`
// shapes it, so the empty block raises the goal instead. This is the
// "ignored for values" property, and it is a listing rather than a panic.
#[test]
fn an_empty_block_on_a_value_goal_leaves_the_goal_open() {
    let e = open_goal("fn v() -> Nat {}");
    assert!(e.contains("unsolved goals"), "{e}");
    assert!(e.contains("?g1"), "{e}");
}

// An open goal is a real goal: an `on` in the same block discharges it, which
// is what "the goal stays open" is supposed to mean.
#[test]
fn an_undischarged_speculation_is_a_goal_an_on_can_close() {
    ok(&format!(
        "{ADD}
         theorem left_unit(n: Nat): add(0, n) = n {{
             {{}}
             on ?g1 := match n {{ Zero => refl, Succ(k) => Nat::cong_succ(left_unit(k)) }};
         }}"
    ));
}

// The trigger is *exactly* empty braces. A block with statements and no
// result is still the parse error it was: a block that does work and then
// closes by computation is a different feature.
#[test]
fn a_block_with_statements_and_no_result_is_still_a_parse_error() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let errs = e.check_source("fn v() -> Nat { let x = 1; }");
    assert!(!errs.is_empty(), "a resultless block must not parse");
}

// `refl` itself is untouched: it is not a tolerant no-op, so a `refl` at a
// non-equation goal is still an error naming `refl` (the conservative
// reading, `issues/surface-proof-automation.md` §1).
#[test]
fn refl_is_not_made_tolerant() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source("fn v() -> Nat { refl }") {
        Ok(()) => panic!("`refl` must not close a value goal"),
        Err(err) => {
            let r = err.render("fn v() -> Nat { refl }");
            assert!(r.contains("refl"), "{r}");
            assert!(!r.contains("unsolved goals"), "{r}");
        }
    }
}
