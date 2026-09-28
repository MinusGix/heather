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
//!
//! The source itself lives in `support::NAT_SUITE`, shared with
//! `determinism.rs`, which hashes exactly what this file checks.

use heather_elab::{ElabError, Elaborator};
use heather_kernel::term::GlobalBinding;

mod support;
use support::NAT_SUITE;

#[test]
fn prelude_checks() {
    Elaborator::with_prelude().expect("prelude must elaborate and kernel-check");
}

#[test]
fn nat_suite_checks() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE).expect("Nat suite must elaborate and kernel-check");
    // The prelude's `CollectionLiteral#tycode_fn` and 4 theorems + the
    // suite's `fn add` and 4 theorems all landed as Ψ-globals (a `fn` is a
    // *defined* one since issues/simulate-conversion-cost.md; the code
    // function is docs/per-instantiation-type-codes-design.md §2's, over the
    // prelude's one parameterized declaration — whose *projections* are not
    // named, §13.6's boundary).
    assert_eq!(e.psi().bindings.len(), 10);
}

#[test]
fn a_fn_is_transparent_and_a_theorem_is_not() {
    // The whole point of issues/simulate-conversion-cost.md's definitions
    // round, asserted where it is decided: `add` keeps its body so that
    // conversion can run it, and every `theorem` stays opaque so that its
    // proof never enters a comparison. `bindings[5]` is the suite's `fn`,
    // right after the prelude's one generated definition
    // (`CollectionLiteral#tycode_fn`,
    // `docs/per-instantiation-type-codes-design.md` §2) and four theorems —
    // a generated definition is bodied like any other definition, which is
    // why the vector opens with a `true`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE).expect("Nat suite must elaborate and kernel-check");
    let bodied: Vec<bool> = e
        .psi()
        .bindings
        .iter()
        .map(|b| matches!(b, GlobalBinding::Tm { body: Some(_), .. }))
        .collect();
    assert_eq!(
        bodied,
        vec![true, false, false, false, false, true, false, false, false, false]
    );
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

/// Renamed 2026-08-17: the rejection is still the gate's, but the *message* is
/// the elaborator's precise one (issues/check-fallback-discards-expected-type.md).
#[test]
fn a_wrong_lemma_use_is_rejected_naming_both_statements() {
    // sym applied with swapped endpoints: types don't line up.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        "theorem bogus(a: Nat, b: Nat, p: a = b): b = a { @sym(b, a, p) }",
    );
    let Err(ElabError::Elab { msg, .. }) = r else { panic!("expected a rejection, got {r:?}") };
    assert!(msg.contains("this has type `a = b`, but `b = a` is expected here"), "{msg}");
}

#[test]
fn unbound_name_is_an_elab_error() {
    let mut e = Elaborator::new();
    let r = e.elab_source("theorem nope(n: Nat): n = n { mystery(n) }");
    assert!(matches!(r, Err(ElabError::Elab { .. })), "got {r:?}");
}
