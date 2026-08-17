//! Checking that ends in inference reports the mismatch itself
//! (`issues/check-fallback-discards-expected-type.md`).
//!
//! The simplest type error in the language used to be a bare kernel
//! `NotConvertible` at the whole declaration: the fallback held an inferred type
//! and dropped it. The claim tested here is narrow and it is *not* "the
//! elaborator typechecks". The mismatch is *recorded* during checking and read
//! only by the kernel gate, only when the gate itself rejects — so nothing is
//! reported that the kernel did not refuse, and a more specific diagnostic
//! raised further down the same declaration still wins the message. Three of the
//! six tests below are the controls that pin that boundary: a mismatch the
//! display cannot state, a false equation caught by `refl`'s own arm, and a type
//! that converts only after δ and β.

use heather_elab::{ElabError, Elaborator};

const LIST: &str = "
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
fn append<A>(xs: List<A>, ys: List<A>) -> List<A> {
    match xs { Nil => ys, Cons(h, t) => Cons(h, append(t, ys)) }
}
";

fn reject(src: &str) -> ElabError {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err,
    }
}

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

/// The filed acceptance case. A numeral is the leaf where the inferred type is
/// free, so this is the cheap half of the fix.
#[test]
fn a_literal_at_the_wrong_type_reports_at_the_literal() {
    let src = format!("{LIST}fn d5<A>(xs: List<A>) -> List<A> {{ 3 }}\n");
    let r = reject(&src);
    let rendered = r.render(&src);
    assert!(
        rendered.contains("this has type `Nat`, but `List<…>` is expected here"),
        "{rendered}"
    );
    assert!(!rendered.contains("the kernel rejected"), "{rendered}");
    // At the `3`, not at the declaration.
    let ElabError::Elab { span, .. } = r else { panic!("expected an elaborator error: {r}") };
    assert_eq!(&src[span.start as usize..span.end as usize], "3");
}

/// A variable at the wrong type takes the general route — the `_` arm of
/// `elab_check_skel` — rather than the numeral's.
#[test]
fn a_variable_at_the_wrong_type_reports_at_the_variable() {
    let src = format!("{LIST}fn d6<A>(xs: List<A>, n: Nat) -> List<A> {{ n }}\n");
    let r = reject(&src);
    let rendered = r.render(&src);
    assert!(
        rendered.contains("this has type `Nat`, but `List<…>` is expected here"),
        "{rendered}"
    );
    let ElabError::Elab { span, .. } = r else { panic!("expected an elaborator error: {r}") };
    assert_eq!(&src[span.start as usize..span.end as usize], "n");
}

/// A *call* at the wrong type — not a leaf, so its inferred type is a computed
/// instantiation. The round measured whether to cover this: the conversion at
/// every checked expression moves the frontend suite by less than its own
/// run-to-run noise, so the coverage is free and the narrow variants the issue
/// proposed were not worth their narrowing.
#[test]
fn a_call_at_the_wrong_type_reports_at_the_call() {
    let src = format!("{LIST}fn d7<A>(xs: List<A>) -> Nat {{ append(xs, xs) }}\n");
    let rendered = reject(&src).render(&src);
    assert!(
        rendered.contains("this has type `List<…>`, but `Nat` is expected here"),
        "{rendered}"
    );
    assert!(!rendered.contains("the kernel rejected"), "{rendered}");
}

/// The other half of the same boundary: a mismatch the display cannot *state*
/// is not reported, because "this has type `X`, but `X` is expected here" reads
/// as a compiler bug and says less than the gate does.
#[test]
fn a_mismatch_the_display_cannot_state_is_left_to_the_kernel() {
    let src = "
inductive And<A, B> { Both(left: A, right: B) }
theorem t(p: And<True, True>, q: And<True, And<True, True>>): True {
    match p { Both(l, r) => l }
}
fn wrong(p: And<True, And<True, True>>) -> And<True, True> { p }
";
    let rendered = reject(src).render(src);
    assert!(rendered.contains("the kernel rejected"), "{rendered}");
}

/// **Negative control, and the architectural one.** The elaborator reports what
/// it can see; it does not become the judge. A declaration it accepts and the
/// kernel refuses still reports as a kernel rejection — `refl` has its own
/// checking arm, so it never reaches the fallback, and the gate is what
/// catches a false equation.
#[test]
fn the_kernel_is_still_the_judge() {
    let src = "theorem broken(n: Nat): n = Succ(n) { refl }\n";
    let rendered = reject(src).render(src);
    assert!(rendered.contains("the kernel rejected"), "{rendered}");
}

/// **Negative control, the one that would break real programs.** The comparison
/// is a *conversion*, not an equality of representations: an expected type that
/// is a lazily wrapped code (`El(Alias())`, δ- and β-steps away from `Nat`) must
/// still accept a `Nat`. This is the open/lazy-type axis of
/// `docs/testing-generated-terms.md`, and a syntactic check would fail it.
#[test]
fn a_type_that_only_converts_is_still_accepted() {
    ok("
        fn Alias() -> Type { Nat }
        fn k(n: Nat) -> Alias() { n }
        fn uses(n: Nat) -> Nat { k(n) }
        ");
}
