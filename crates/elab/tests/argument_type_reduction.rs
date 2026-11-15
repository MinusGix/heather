//! Reading implicit arguments off an argument type that has to *reduce* first
//! (issues/motive-application-hides-hypothesis-type.md,
//! docs/elaborator/argument-type-reduction-design.md, 2026-08-17).
//!
//! An induction principle whose motive is a value parameter — `int_ind(P: Int
//! -> Type, …)`, and every hand-written principle over a non-recursive
//! inductive is one — binds its step hypothesis at `P(OfNat(k))`. Once `P` is
//! given that type is a **β-redex**: `(λ (z: Int) => add(a, z) = add(z, a))
//! (OfNat(k))`. It is an `Id` and does not say so, so every consumer that
//! fills implicits by unifying against an argument's type — `cong_int`, `sym`,
//! anything — refused it, and `lib/std/num/int.hthr` restated the hypothesis
//! inside `@cong_int(f, lhs, rhs, ih)` at eight sites.
//!
//! `Elaborator::unify_arg_ty` reads the type as written first and, only when
//! that learned nothing, reads its weak head normal form. The axes
//! (docs/testing-generated-terms.md): the hypothesis type appears both as a
//! redex and already-normal; `List<A>` carries an OPEN element type; every
//! acceptance below is a *checking* position and one is an inference position
//! nested inside one; and the last three tests are the negative controls —
//! an implicit that is genuinely underdetermined, a redex whose normal form
//! is not an `Id` at all, and a nonsense endpoint that must still be refused.

use heather_elab::{ElabError, Elaborator};

/// `add`, plus the `Nat` induction principle with the motive as a **value**
/// parameter. That is the shape the issue is about: nothing about `Nat` needs
/// this (a `match` recurses), and writing it this way reproduces `int_ind`
/// exactly while keeping the file free of `Int`.
const PRE: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k) => Succ(add(k, n)),
    }
}

theorem nat_ind(P: Nat -> Type, z: P(0),
                up: (k: Nat) -> P(k) -> P(Succ(k)), n: Nat): P(n) {
    match n as λ y => P(y) {
        Zero => z,
        Succ(k) => up(k, nat_ind(P, z, up, k)),
    }
}

inductive Bit { B0, B1 }

inductive List<A> { Nil, Cons(head: A, tail: List<A>) }

fn app<A>(xs: List<A>, ys: List<A>) -> List<A> {
    match xs {
        Nil => ys,
        Cons(h, t) => Cons(h, app(t, ys)),
    }
}

theorem cong_list<A>(f: List<A> -> List<A>, {a: List<A>}, {b: List<A>},
                     p: a = b): f(a) = f(b) {
    j(p, λ y q => f(a) = f(y), refl)
}

theorem list_ind<A>(P: List<A> -> Type, z: P(Nil),
                    up: (h: A) -> (t: List<A>) -> P(t) -> P(Cons(h, t)),
                    xs: List<A>): P(xs) {
    match xs as λ y => P(y) {
        Nil => z,
        Cons(h, t) => up(h, t, list_ind(P, z, up, t)),
    }
}
"#;

fn run(src: &str) -> Result<(), ElabError> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(PRE).expect("preamble");
    e.elab_source(src)
}

fn ok(src: &str) {
    if let Err(err) = run(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    match run(src) {
        Ok(()) => panic!("expected a refusal, but it checked:\n{src}"),
        Err(err) => match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        },
    }
}

// ---------------------------------------------------------------------------
// The headline: the issue's arm, at the terse spelling.

/// `ih : (λ (z: Nat) => add(z, 0) = z)(k)` — a redex — and `cong_succ` fills
/// both endpoints off it. This is `lib/std/num/int.hthr`'s `add_comm` arm with
/// `Int` replaced by `Nat` and `cong_int` by the prelude's `cong_succ`.
#[test]
fn a_motive_applied_hypothesis_fills_implicits() {
    ok("theorem add_zero_r(n: Nat): add(n, 0) = n {
            nat_ind(λ (z: Nat) => add(z, 0) = z,
                refl,
                λ (k: Nat) (ih: add(k, 0) = k) => Nat::cong_succ(ih),
                n)
        }");
}

/// The same hypothesis under `sym`, which is the issue's second symptom and
/// the evidence that this is about implicit-filling from an argument's type
/// and not about one congruence lemma. The inner `sym(ih)` is an *argument*
/// of `cong_succ`, so it elaborates in inference position with no expected
/// type to fall back on.
#[test]
fn the_same_hypothesis_under_sym() {
    ok("theorem add_zero_r2(n: Nat): add(n, 0) = n {
            nat_ind(λ (z: Nat) => add(z, 0) = z,
                refl,
                λ (k: Nat) (ih: add(k, 0) = k) => sym(Nat::cong_succ(sym(ih))),
                n)
        }");
}

/// Axis: the hypothesis type **already normal**. A `match`'s own `ih` binder
/// is an `Id` as written, and it went through the syntactic read before this
/// change and must go through exactly the same one now — the reduction is
/// reached only when the first read learns nothing.
#[test]
fn an_already_normal_hypothesis_takes_the_old_path() {
    ok("theorem add_zero_m(n: Nat): add(n, 0) = n {
            match n { Zero => refl, Succ(k, ih) => Nat::cong_succ(ih) }
        }");
}

/// Axis: an **open** element type. `A` is a parameter of the theorem, so the
/// motive is a `List<A> -> Type` at a type nobody can close, and `cong_list`
/// has to solve `A` *and* both endpoints out of the reduced hypothesis type.
#[test]
fn an_open_element_type_reduces_the_same_way() {
    ok("theorem app_nil<A>(xs: List<A>): app(xs, Nil) = xs {
            list_ind(λ (w: List<A>) => app(w, Nil) = w,
                refl,
                λ (h: A) (t: List<A>) (ih: app(t, Nil) = t) =>
                    cong_list(λ (w: List<A>) => Cons(h, w), ih),
                xs)
        }");
}

// ---------------------------------------------------------------------------
// Composition with the motive synthesis that landed the same day
// (docs/elaborator/goal-motive-synthesis-design.md): a synthesized motive's arm goal is
// an applied motive too, so a motive-less `match` inside a value-parameter
// induction is both mechanisms at once.

/// The inner `match` writes no motive, and the expected type it has to
/// synthesize one *from* is the outer principle's motive applied — a redex on
/// both counts. Each arm then fills `cong_succ`'s endpoints out of the step
/// hypothesis, which is the other half. Neither is written out.
#[test]
fn a_synthesized_motive_composes_with_the_reduced_read() {
    ok("theorem add_zero_c(b: Bit, n: Nat): add(n, 0) = n {
            nat_ind(λ (z: Nat) => add(z, 0) = z,
                refl,
                λ (k: Nat) (ih: add(k, 0) = k) =>
                    match b { B0 => Nat::cong_succ(ih), B1 => Nat::cong_succ(ih) },
                n)
        }");
}

// ---------------------------------------------------------------------------
// Negative controls.

/// An implicit that is **genuinely underdetermined** must still be refused,
/// with the message it always had: reducing may only make evidence readable,
/// never invent a solution. `?f` heads a flex application, which no
/// first-order rule may touch, and its type is already normal — so the retry
/// runs and learns nothing, exactly as intended.
#[test]
fn an_underdetermined_implicit_is_still_refused() {
    let msg = bad(
        "theorem ap<A>({f: A -> A}, a: A, p: f(a) = a): f(a) = a { p }
         theorem use(n: Nat, q: add(n, n) = n): add(n, n) = n { ap(n, q) }",
    );
    assert!(msg.contains("could not infer the implicit argument `f`"), "{msg}");
}

/// A redex whose normal form is **not an `Id`**: the motive is constantly
/// `Nat`, so `ih` reduces to `Nat` and there is still nothing for `cong_succ`
/// to read. The requirement is that it terminate and report, rather than loop
/// or fill the endpoints with something that is not a proof.
#[test]
fn a_redex_that_is_not_an_equation_is_refused() {
    let msg = bad(
        "theorem konst(n: Nat): Nat {
             nat_ind(λ (z: Nat) => Nat,
                 0,
                 λ (k: Nat) (ih: Nat) => Nat::cong_succ(ih),
                 n)
         }",
    );
    assert!(msg.contains("could not infer the implicit argument"), "{msg}");
}

/// The reduction is not a licence: a hypothesis that reduces to an `Id`
/// between the *wrong* endpoints still fails, at the kernel or before it. The
/// endpoints are read off the argument, so a solved-but-wrong call is exactly
/// what must not silently pass.
#[test]
fn a_reduced_hypothesis_at_the_wrong_endpoints_still_fails() {
    let msg = bad(
        "theorem wrong(n: Nat): add(n, 0) = n {
             nat_ind(λ (z: Nat) => add(z, 0) = z,
                 refl,
                 λ (k: Nat) (ih: add(k, 0) = k) => sym(Nat::cong_succ(ih)),
                 n)
         }",
    );
    assert!(!msg.is_empty(), "a wrong direction must be refused");
}
