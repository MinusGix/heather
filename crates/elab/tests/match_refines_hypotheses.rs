//! Acceptance for issues/elab-match-refines-hypothesis-kernel-rejects.md: a
//! `match` on a local in checking position generalizes the hypotheses that
//! mention it into the motive, so each arm sees them at its constructor — in
//! the term the kernel checks, not only in what the arm was told. Before this,
//! `h: ¬(n = 0)` in the `Zero` arm was still about `n`, and `h(refl)` reached
//! the kernel as `refl : n = 0`.
//!
//! What the positives vary (docs/testing-generated-terms.md): a neutral
//! scrutinee (a computed one refines by syntactic occurrence, the last tests
//! below, docs/language/matching/dependent-match-compiler-design.md §5), a hypothesis behind a
//! defined head, an **open** element type (`Opt<A>`), a goal that refines
//! with the hypothesis, a dependent chain of hypotheses, and checking
//! position throughout. The controls show that the refinement is per arm.

use heather_elab::Elaborator;

use crate::support::{assert_refused, Refusal};

const BASE: &str = r#"
inductive Never {}

fn Is(n: Nat) -> Type { n = 0 }

inductive Opt<A> { None, Some(a: A) }

inductive B { T, F }

fn isz(n: Nat) -> B { match n { Zero => T, Succ(_) => F } }

fn is_some<A>(o: Opt<A>) -> B { match o { None => F, Some(_) => T } }
"#;

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&format!("{BASE}\n{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err:?}"));
}

fn refused(name: &str, src: &str, why: Refusal) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert_refused(&mut e, name, &format!("{BASE}\n{src}"), why)
}

#[test]
fn a_hypothesis_about_the_scrutinee_is_refined_in_each_arm() {
    ok(r#"
// The issue's probe: the hypothesis's type is a defined head over `n`.
theorem defined_head(n: Nat, h: Is(n) -> Never): Nat {
    match n {
        Zero => match h(refl) {},
        Succ(k) => k,
    }
}

// Written out, and as the arm's whole body.
theorem written(n: Nat, h: n = 0 -> Never): Nat {
    match n {
        Zero => match h(refl) {},
        Succ(k) => k,
    }
}

// An open element type: `h` is about `o`, an `Opt<A>` for every `A`.
theorem unwrap<A>(o: Opt<A>, h: o = None -> Never): A {
    match o {
        None => match h(refl) {},
        Some(a) => a,
    }
}
"#);
}

#[test]
fn the_goal_and_the_hypotheses_refine_together() {
    ok(r#"
// In the `Succ` arm the goal is `0 = Succ(k)` and `h` is `Succ(k) = 0`.
theorem flip(n: Nat, h: n = 0): 0 = n {
    match n {
        Zero => refl,
        Succ(_) => sym(h),
    }
}

// `e` mentions `h`, which mentions `n`: both are generalized, in order, so
// `e` is about the refined `h`.
theorem chain(n: Nat, h: n = 0, e: h = h): e = e {
    match n {
        Zero => refl,
        Succ(_) => refl,
    }
}

// A pattern variable named like a refined hypothesis still shadows it, as
// it did before the hypothesis was refined.
theorem shadowed(n: Nat, k: n = 0): Nat {
    match n {
        Zero => 0,
        Succ(k) => k,
    }
}

// Nested: the inner `match` refines the hypothesis the outer one already
// refined.
theorem nested(m: Nat, n: Nat, h: Is(m) -> Is(n) -> Never): Nat {
    match m {
        Zero => match n { Zero => match h(refl, refl) {}, Succ(k) => k },
        Succ(k) => k,
    }
}
"#);
}

#[test]
fn a_recursion_still_varies_its_own_hypotheses() {
    // A structural recursion's `match` keeps the motive the recursion needs;
    // the hypothesis it passes at a new value is generalized as a varied
    // parameter (issues/ih-generalization.md), not as a refinement.
    ok(r#"
fn count(n: Nat, h: n = n) -> Nat {
    match n {
        Zero => 0,
        Succ(k) => Succ(count(k, refl)),
    }
}
"#);
}

#[test]
fn the_refinement_is_the_arms_own() {
    // In the `Succ` arm `h` is about `Succ(k)`, and `refl : Succ(k) = 0` is
    // false: refused, where before the elaborator would have let the kernel
    // judge `refl : n = 0`.
    refused(
        "wrong_arm",
        r#"
theorem wrong_arm(n: Nat, h: n = 0 -> Never): Nat {
    match n {
        Zero => 0,
        Succ(k) => match h(refl) {},
    }
}
"#,
        Refusal::Says("definitionally equal"),
    );
    // A hypothesis about another local is untouched by the match.
    refused(
        "other_local",
        r#"
theorem other_local(m: Nat, n: Nat, h: m = 0 -> Never): Nat {
    match n {
        Zero => match h(refl) {},
        Succ(k) => k,
    }
}
"#,
        Refusal::Says("definitionally equal"),
    );
}

#[test]
fn a_computed_scrutinee_refines_the_hypotheses_that_contain_it() {
    ok(r#"
// Probe P1's shape: in the `F` arm `h` is `F = T`.
theorem computed(n: Nat, h: isz(n) = T): Nat {
    match isz(n) {
        T => 0,
        F => absurd(h),
    }
}

// An open element type, and the hypothesis on the other side.
theorem computed_open<A>(o: Opt<A>, h: T = is_some(o)): Nat {
    match is_some(o) {
        T => 0,
        F => absurd(h),
    }
}

// A literal argument: the scrutinee is closed and still refines.
theorem computed_literal(h: isz(0) = F): Nat {
    match isz(0) {
        T => absurd(h),
        F => 0,
    }
}

// A chain: `e` mentions `h`, which contains the scrutinee.
theorem computed_chain(n: Nat, h: isz(n) = T, e: h = h): Nat {
    match isz(n) {
        T => 0,
        F => absurd(h),
    }
}

// A function body whose arms do not read `h` keeps its plain term: the
// equation states the body as written, by `refl`.
fn plain(n: Nat, h: isz(n) = T) -> Nat { match isz(n) { T => n, F => 0 } }
theorem plain_is_plain(n: Nat, h: isz(n) = T): plain(n, h) = (match isz(n) as λ _ => Nat { T => n, F => 0 }) { refl }
"#);
}

#[test]
fn a_computed_scrutinee_refines_only_what_contains_it() {
    // The hypothesis says the other thing: in the `F` arm it is `F = F`, and
    // `absurd` has nothing to refute.
    refused(
        "computed_wrong",
        r#"
theorem computed_wrong(n: Nat, h: isz(n) = F): Nat {
    match isz(n) {
        T => 0,
        F => absurd(h),
    }
}
"#,
        Refusal::Says("absurd"),
    );
    // A hypothesis about another argument is untouched.
    refused(
        "computed_other",
        r#"
theorem computed_other(m: Nat, n: Nat, h: isz(m) = T): Nat {
    match isz(n) {
        T => 0,
        F => absurd(h),
    }
}
"#,
        Refusal::Says("absurd"),
    );
}
