//! Stage-2 acceptance (issues/elab-stage2-metas.md): the Nat suite with
//! *both* stage-2 ergonomics on — motive-less `match` (synthesized motives)
//! and implicit lemma endpoints (`sym(add_zero(n))`, not
//! `sym(add(n,0), n, add_zero(n))`). The endpoints `a`, `b`, (`c`) of the
//! prelude lemmas are `{}`-implicit; the elaborator recovers them by unifying
//! the proof argument's type against the parameter domain, discharges the
//! metavariables with one global substitution, and hands a fully explicit
//! core term to the kernel — which gates it exactly as before.

use heather_elab::{ElabError, Elaborator};

// The benchmark from the issue: no `as`, no endpoint arguments anywhere.
const NAT_SUITE_IMPLICIT: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k, ih) => Succ(ih),
    }
}

theorem add_zero(n: Nat): add(n, 0) = n {
    match n {
        Zero => refl,
        Succ(k, ih) => cong_succ(ih),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m {
        Zero => refl,
        Succ(k, ih) => cong_succ(ih),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m {
        Zero => sym(add_zero(n)),
        Succ(k, ih) => trans(cong_succ(ih), sym(add_succ(n, k))),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a {
        Zero => refl,
        Succ(k, ih) => cong_succ(ih),
    }
}
"#;

#[test]
fn nat_suite_annotation_free() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE_IMPLICIT)
        .expect("annotation-free Nat suite must elaborate and kernel-check");
    // prelude's 4 + the suite's `fn add` and 4 theorems, all landed as
    // Ψ-globals (a `fn` is a *defined* one since
    // issues/simulate-conversion-cost.md).
    assert_eq!(e.psi().bindings.len(), 9);
}

#[test]
fn implicit_endpoints_are_solved() {
    // A single implicit-endpoint call, in isolation: `sym` with only its
    // proof argument; the endpoints come from `add_zero(n) : add(n,0) = n`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem add_zero(n: Nat): add(n, 0) = n {
            match n { Zero => refl, Succ(k, ih) => cong_succ(ih) }
        }
        theorem flip(n: Nat): n = add(n, 0) { sym(add_zero(n)) }
        "#,
    )
    .expect("sym's endpoints must be inferred from its proof argument");
}

#[test]
fn explicit_override_still_available() {
    // `@sym(a, b, p)` supplies the implicit endpoints positionally — the
    // stage-1 fallback the sketches promise.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source("theorem manual(a: Nat, b: Nat, p: a = b): b = a { @sym(a, b, p) }")
        .expect("explicit `@` override must accept positional endpoints");
}

#[test]
fn wrong_implicit_proof_is_kernel_rejected() {
    // If the (inferred) endpoints make a false statement, the *kernel* — not
    // the unifier — must reject: `sym` of `add_zero(n)` proves
    // `n = add(n,0)`, which is not `add(n,0) = add(n,0)`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem add_zero(n: Nat): add(n, 0) = n {
            match n { Zero => refl, Succ(k, ih) => cong_succ(ih) }
        }
        theorem bogus(n: Nat): add(n, 0) = add(n, 0) { sym(add_zero(n)) }
        "#,
    );
    // Reported by the gate either way; the message now names both statements
    // (issues/check-fallback-discards-expected-type.md).
    let Err(ElabError::Elab { msg, .. }) = r else { panic!("expected a rejection, got {r:?}") };
    assert!(
        msg.contains("this has type `n = add(n, 0)`, but `add(n, 0) = add(n, 0)` is expected here"),
        "{msg}"
    );
}

#[test]
fn too_few_explicit_args_is_an_elab_error() {
    // `trans` needs two proof arguments; giving one is an arity error caught
    // before the kernel.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        "theorem oops(a: Nat, b: Nat, p: a = b): a = b { trans(p) }",
    );
    assert!(matches!(r, Err(ElabError::Elab { .. })), "expected an elab arity error, got {r:?}");
}

// ---------------------------------------------------------------------------
// The expected-type harvest and its guards
// (docs/unifier-completeness-design.md §5).

#[test]
fn refl_as_an_argument_is_deferred_and_retried() {
    // `refl` is checking-only; its parameter's domain (`a = b`) still
    // mentions the endpoint metas when the argument is reached, so it is
    // deferred, the expected type solves the endpoints, and the retried
    // `refl` gets a meta-free `Id`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source("theorem t(n: Nat): n = n { sym(refl) }")
        .expect("`refl` must defer until the endpoints are harvested");
}

#[test]
fn a_vector_literal_argument_is_deferred_and_retried() {
    // Same for a vector literal, with the retry unblocked by a *later*
    // argument's inference rather than by the expected type.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        "fn pick<A>(xs: [A; 2], x: A) -> A { x }
         fn go() -> Nat { pick([1, 2], 5) }",
    )
    .expect("the literal must defer until `x` solves `A`");
}

#[test]
fn a_flex_headed_result_is_not_peeled_by_the_harvest() {
    // The flex-head guard (design §5.4), pinned directly: `ap`'s result type
    // is `?f(a) = a`, and both the argument's type and the expected type
    // offer `add(n, n) = n`. First-order peeling would "solve"
    // `?f := add(n)` — here even acceptably, which is exactly why the guard
    // must be what refuses: flex-headed applications are outside the Miller
    // fragment, only the LGG rule (whose both-sides trigger does not fire on
    // this one-sided shape) is trusted for them, and the outcome is the
    // caller's message rather than a solution nobody stated.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        "fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
         theorem ap<A>({f: A -> A}, a: A, p: f(a) = a): f(a) = a { p }
         theorem use(n: Nat, q: add(n, n) = n): add(n, n) = n { ap(n, q) }",
    );
    match r {
        Err(ElabError::Elab { msg, .. }) => {
            assert!(msg.contains("could not infer the implicit argument `f`"), "{msg}");
        }
        other => panic!("expected the could-not-infer message, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Inference through an indexed family's type
// (issues/type-arg-inference-through-index.md). A declared-index family's
// type is `El` of an index recursion choosing among quoted codes, with the
// payload type a variable *inside* the code literals — so until the walker
// could descend `elimN` and the code constructors, `t: W3<A>(n)` could not
// teach it `A` even though a plain `r: Res<A>` could.

const W3I: &str = r#"
inductive W3i<A> : (n: Nat) -> Type {
    WNil                            : W3i<A>(0),
    WOne(x: A)                      : W3i<A>(0),
    WTwo                            : W3i<A>(0),
    WCons(n: Nat, x: A, t: W3i<A>(n)) : W3i<A>(Succ(n)),
}
"#;

#[test]
fn a_declared_index_familys_argument_solves_the_type_parameter() {
    // The reproducer from the issue: no `<A>` at either call site.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&format!(
        "{W3I}
         fn idw<A>(n: Nat, t: W3i<A>(n)) -> W3i<A>(n) {{ t }}
         theorem idw_id<A>(n: Nat, t: W3i<A>(n)): idw(n, t) = t {{ refl }}"
    ))
    .expect("`t`'s type mentions `A`; the call must infer it");
}

#[test]
fn a_forded_familys_argument_solves_the_type_parameter() {
    // The other family class: a computed-index (forded) declaration over a
    // non-recursive skeleton, whose Σ-ford the structural walk reaches
    // directly.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        inductive Fq<A> : (n: Nat) -> Type {
            FqZ              : Fq<A>(0),
            FqA(n: Nat, x: A) : Fq<A>(n),
        }
        fn idq<A>(n: Nat, t: Fq<A>(n)) -> Fq<A>(n) { t }
        theorem idq_id<A>(n: Nat, t: Fq<A>(n)): idq(n, t) = t { refl }
        "#,
    )
    .expect("a forded family's type argument must infer the same way");
}

#[test]
fn a_structural_look_alike_still_fails_at_the_kernel() {
    // Negative control. A family's lowered type is *structural* — there is
    // no name in it for the walker to compare — so against a look-alike
    // family the walker may well learn `A`. That is fine exactly as long as
    // the kernel still judges the call — a wrong pairing must fail
    // *somewhere*, and the walker's license ("only learns, kernel decides")
    // is what this pins. If these families ever become genuinely
    // convertible, this call becomes well-typed and the learned solution
    // correct — then the test should flip to a positive, not the walker to
    // a refusal.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        inductive P2<A> : (n: Nat) -> Type {
            PNil            : P2<A>(0),
            PCons(x: A)     : P2<A>(0),
        }
        inductive Q2<A> : (n: Nat) -> Type {
            QNil            : Q2<A>(0),
            QCons(x: A)     : Q2<A>(0),
        }
        fn fp<A>(n: Nat, t: P2<A>(n)) -> Nat { 0 }
        fn fq(n: Nat, t: Q2<Nat>(n)) -> Nat { fp(n, t) }
        "#,
    );
    assert!(r.is_err(), "a mismatched family argument must not typecheck, got {r:?}");
}
