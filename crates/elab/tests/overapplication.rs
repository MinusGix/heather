//! Call-site over-application: `f(a1, …, an)` with more arguments than `f`
//! has parameters spills into iterated application, so `nth(t, k)` is
//! `nth(t)(k)`. Tracking issue: `issues/call-site-overapplication.md`.
//!
//! The explicit path (`apply_explicit`) already walked the Π spine one
//! argument at a time and so already spilled; the refusal lived in
//! `apply_implicit`'s saturation check, which is why every positive test here
//! that matters is at a callee **with implicits**. The negative controls are
//! the point of the file: a spilled argument meeting a non-function must still
//! be an arity error naming the callee, and under-application must still be
//! "too few".

use heather_elab::Elaborator;

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(src),
    }
}

/// A curried-by-necessity `fn` of the shape `std/list`'s `nth` has: the
/// argument that varies with the recursion is *returned*, because the
/// termination checker wants one decreasing argument with the rest fixed
/// (issues/ih-generalization.md). Polymorphic, so the callee has an implicit
/// to insert and the call goes through `apply_implicit`.
const CURRIED: &str = r#"
inductive Option<A> { None, Some(v: A) }
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }

fn nth<A>(xs: List<A>) -> Nat -> Option<A> {
    match xs {
        Nil => λ (i: Nat) => None,
        Cons(h, t) => λ (i: Nat) => match i { Zero => Some(h), Succ(k) => nth(t)(k) },
    }
}
"#;

// -- 1: the headline ------------------------------------------------------

#[test]
fn an_extra_argument_spills_into_a_second_application() {
    ok(&format!(
        "{CURRIED}
         fn at<A>(xs: List<A>, i: Nat) -> Option<A> {{ nth(xs, i) }}"
    ));
}

// The spelling it is sugar for must still mean the same thing — and the two
// must be *definitionally* the same, not merely both well-typed. Checked as a
// proof, so the kernel compares them rather than evaluating one.
#[test]
fn the_spilled_call_is_the_parenthesized_one() {
    ok(&format!(
        "{CURRIED}
         theorem same<A>(xs: List<A>, i: Nat): nth(xs, i) = nth(xs)(i) {{ refl }}"
    ));
}

// Axis 2 (docs/testing-generated-terms.md): an **open** element type. The
// implicit `A` is solved from the receiver here, and a spilled argument
// arrives after the meta block is discharged — so this is the test that says
// the discharge happened before the spill and not after.
#[test]
fn spilling_works_at_an_open_element_type() {
    ok(&format!(
        "{CURRIED}
         fn at2<A>(xs: List<List<A>>, i: Nat) -> Option<List<A>> {{ nth(xs, i) }}"
    ));
}

// Axis 3: a *checking* position, where the result type has to convert with a
// goal rather than be reduced away. `Nil` is neutral in `A`, so nothing
// computes the answer out from under the annotation.
#[test]
fn spilling_in_checking_position_at_a_neutral_scrutinee() {
    ok(&format!(
        "{CURRIED}
         theorem out_of_range<A>(i: Nat): nth(Nil<A>, i) = None<A> {{ refl }}"
    ));
}

// Three arguments past a one-parameter callee: the spill is a spine, not one
// extra slot.
#[test]
fn two_arguments_can_spill() {
    ok("fn k(x: Nat) -> Nat -> Nat -> Nat { λ (y: Nat) => λ (z: Nat) => x }
        fn use_k(a: Nat) -> Nat { k(a, a, a) }");
}

// -- 2: the induction hypothesis ------------------------------------------

// The case the feature exists for. A recursion whose non-decreasing argument
// *varies* has to return a function (issues/ih-generalization.md's
// workaround), so **every** use of its ih is an over-application. The ih is
// not a global — it is the eliminator's hypothesis — so it takes its own path
// (`elab_self_call`), which had its own exact-arity check.
#[test]
fn an_induction_hypothesis_can_be_over_applied() {
    ok("inductive Bool { False, True }
        fn leb(n: Nat) -> Nat -> Bool {
            match n {
                Zero => λ (m: Nat) => True,
                Succ(k) => λ (m: Nat) => match m { Zero => False, Succ(l) => leb(k)(l) },
            }
        }
        theorem flip(x: Nat): (y: Nat) -> leb(x)(y) = False -> leb(y)(x) = True {
            match x {
                Zero => λ y p => absurd(p),
                Succ(k) => λ y =>
                    match y {
                        Zero => λ p => refl,
                        Succ(l) => λ p => flip(k, l, p),
                    },
            }
        }");
}

// …and the ih's guard is unaffected: the spilled arguments are applied to the
// ih's *result*, so the decreasing argument is still checked against the
// enclosing `match`. Negative control — passing the wrong descendant is still
// a guard failure, not an application.
#[test]
fn a_spilled_ih_still_has_to_descend() {
    let e = bad("fn f(n: Nat) -> Nat -> Nat {
                     match n {
                         Zero => λ (m: Nat) => m,
                         Succ(k) => λ (m: Nat) => f(n, m),
                     }
                 }");
    assert!(e.contains("must descend"), "{e}");
}

// Under-application of an ih is still refused with the count, since the ih's
// own arguments are what the guard is checked against.
#[test]
fn an_under_applied_ih_is_still_refused() {
    let e = bad("fn g(a: Nat, b: Nat) -> Nat {
                     match a { Zero => b, Succ(k) => g(k) }
                 }");
    assert!(e.contains("must pass all"), "{e}");
}

// -- 3: negative controls -------------------------------------------------

// The tail is not a function: still an arity error, still naming the callee.
// This is the control that says the feature is a spill and not a silent drop.
#[test]
fn over_application_onto_a_non_function_is_still_an_arity_error() {
    let e = bad(&format!(
        "{CURRIED}
         fn oops<A>(xs: List<A>, i: Nat) -> Option<A> {{ nth(xs, i, i) }}"
    ));
    assert!(e.contains("applied to too many arguments"), "{e}");
    assert!(e.contains("`nth`"), "the callee must be named: {e}");
}

// The same control on a callee with **no** implicits, which takes the other
// path into `apply_explicit`.
#[test]
fn over_application_of_a_monomorphic_fn_is_still_an_arity_error() {
    let e = bad("fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
                 fn oops(a: Nat) -> Nat { add(a, a, a) }");
    assert!(e.contains("applied to too many arguments"), "{e}");
    assert!(e.contains("`add`"), "{e}");
}

// Under-application is untouched: spilling must not have turned the
// saturation check into "any number of arguments will do".
#[test]
fn under_application_is_still_too_few() {
    let e = bad(&format!(
        "{CURRIED}
         fn oops<A>() -> Nat {{ nth() }}"
    ));
    assert!(e.contains("too few arguments"), "{e}");
}

// A spilled argument of the wrong type is a type error at *that* argument,
// not an arity error: the spill re-enters the ordinary checking path.
#[test]
fn a_spilled_argument_is_still_type_checked() {
    let e = bad(&format!(
        "{CURRIED}
         fn oops<A>(xs: List<A>, ys: List<A>) -> Option<A> {{ nth(xs, ys) }}"
    ));
    assert!(!e.contains("too many arguments"), "should be a type error: {e}");
}
