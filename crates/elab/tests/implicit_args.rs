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
    assert!(matches!(r, Err(ElabError::Kernel { .. })), "expected a kernel rejection, got {r:?}");
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
