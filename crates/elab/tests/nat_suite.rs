//! Stress-proof-suite item 1 (issues/stress-proof-suite.md): the Nat
//! arithmetic + Id lemmas, elaborated from surface syntax and checked by the
//! real kernel. Every declaration that lands here has passed
//! `check_type` + `check_term`; the negative tests confirm the kernel gate
//! actually rejects (elaborator soundness is by construction, not by trust).
//!
//! This file pins the **stage-1 explicit forms** as a regression: `as λ z => M`
//! motives spelled out, and endpoints to the (now implicit-parametered)
//! prelude lemmas supplied positionally via `@` (issues/elab-stage2-metas.md).
//! The annotation-free stage-2 forms live in `implicit_args.rs`.

use heather_elab::{ElabError, Elaborator};
use heather_kernel::term::GlobalBinding;

const NAT_SUITE: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k, ih) => Succ(ih),
    }
}

theorem add_zero(n: Nat): add(n, 0) = n {
    match n as λ z => add(z, 0) = z {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(k, 0), k, ih),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m as λ z => add(z, Succ(n)) = Succ(add(z, n)) {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(k, Succ(n)), Succ(add(k, n)), ih),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m as λ z => add(z, n) = add(n, z) {
        Zero => @sym(add(n, 0), n, add_zero(n)),
        Succ(k, ih) => @trans(
            Succ(add(k, n)),
            Succ(add(n, k)),
            add(n, Succ(k)),
            @cong_succ(add(k, n), add(n, k), ih),
            @sym(add(n, Succ(k)), Succ(add(n, k)), add_succ(n, k))
        ),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a as λ z => add(add(z, b), c) = add(z, add(b, c)) {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(add(k, b), c), add(k, add(b, c)), ih),
    }
}
"#;

#[test]
fn prelude_checks() {
    Elaborator::with_prelude().expect("prelude must elaborate and kernel-check");
}

#[test]
fn nat_suite_checks() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE).expect("Nat suite must elaborate and kernel-check");
    // The prelude's 3 theorems + the suite's `fn add` and 4 theorems all
    // landed as Ψ-globals (a `fn` is a *defined* one since
    // issues/simulate-conversion-cost.md).
    assert_eq!(e.psi().bindings.len(), 8);
}

#[test]
fn a_fn_is_transparent_and_a_theorem_is_not() {
    // The whole point of issues/simulate-conversion-cost.md's definitions
    // round, asserted where it is decided: `add` keeps its body so that
    // conversion can run it, and every `theorem` stays opaque so that its
    // proof never enters a comparison. `bindings[3]` is the suite's `fn`,
    // right after the prelude's three theorems.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE).expect("Nat suite must elaborate and kernel-check");
    let bodied: Vec<bool> = e
        .psi()
        .bindings
        .iter()
        .map(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }))
        .collect();
    assert_eq!(bodied, vec![false, false, false, true, false, false, false, false]);
}

#[test]
fn computation_check() {
    // Concrete arithmetic reduces: 2 + 2 = 4 proved by refl alone.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE).expect("suite");
    e.elab_source("theorem two_plus_two(): add(2, 2) = 4 { refl }")
        .expect("2 + 2 = 4 by refl");
}

#[test]
fn kernel_rejects_wrong_proof() {
    // `refl` cannot prove add(n, 1) = n; the KERNEL (not the elaborator's
    // surface checks) must be what rejects it.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE).expect("suite");
    let r = e.elab_source("theorem bogus(n: Nat): add(n, 1) = n { refl }");
    assert!(
        matches!(r, Err(ElabError::Kernel { .. })),
        "expected a kernel rejection, got {r:?}"
    );
}

#[test]
fn kernel_rejects_wrong_lemma_use() {
    // sym applied with swapped endpoints: types don't line up.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        "theorem bogus(a: Nat, b: Nat, p: a = b): b = a { @sym(b, a, p) }",
    );
    assert!(
        matches!(r, Err(ElabError::Kernel { .. })),
        "expected a kernel rejection, got {r:?}"
    );
}

#[test]
fn unbound_name_is_an_elab_error() {
    let mut e = Elaborator::new();
    let r = e.elab_source("theorem nope(n: Nat): n = n { mystery(n) }");
    assert!(matches!(r, Err(ElabError::Elab { .. })), "got {r:?}");
}
