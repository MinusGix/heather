//! Acceptance for issues/match-recursion.md: the unified `match`, where a
//! structurally guarded **self-call** is the induction hypothesis. `add` is
//! an ordinary recursive function and `add_zero` is an ordinary recursive
//! *theorem* — literally the same language, no `induction`/`rec` keyword, no
//! `Succ(k, ih)` binder.
//!
//! The lowering builds `elim_Nat`, so the guardedness analysis is untrusted:
//! everything here still passes the kernel's `check_type` + `check_term`, and
//! the analysis can only reject.

use heather_elab::{ElabError, Elaborator};

// The stage-1/stage-2 suite, rewritten with self-calls throughout.
const NAT_SUITE_REC: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k) => Succ(add(k, n)),
    }
}

theorem add_zero(n: Nat): add(n, 0) = n {
    match n {
        Zero => refl,
        Succ(k) => cong_succ(add_zero(k)),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m {
        Zero => refl,
        Succ(k) => cong_succ(add_succ(k, n)),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m {
        Zero => sym(add_zero(n)),
        Succ(k) => trans(cong_succ(add_comm(k, n)), sym(add_succ(n, k))),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a {
        Zero => refl,
        Succ(k) => cong_succ(add_assoc(k, b, c)),
    }
}
"#;

#[test]
fn nat_suite_recursive_style() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE_REC)
        .expect("recursive-style Nat suite must elaborate and kernel-check");
    // prelude's 3 + the suite's 4 theorems, all landed as Ψ-globals.
    assert_eq!(e.psi().bindings.len(), 7);
}

#[test]
fn recursive_add_still_computes() {
    // The self-call really did lower to `elim_Nat`: concrete arithmetic
    // reduces, so `refl` alone proves 2 + 2 = 4.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE_REC).expect("suite");
    e.elab_source("theorem two_plus_two(): add(2, 2) = 4 { refl }")
        .expect("2 + 2 = 4 by refl");
}

#[test]
fn both_spellings_agree() {
    // The explicit-ih arm remains the low-level fallback, and the two
    // spellings coexist in one file.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat {
            match m { Zero => n, Succ(k, ih) => Succ(ih) }
        }
        fn add2(m: Nat, n: Nat) -> Nat {
            match m { Zero => n, Succ(k) => Succ(add2(k, n)) }
        }
        theorem same(m: Nat, n: Nat): add(m, n) = add2(m, n) {
            match m { Zero => refl, Succ(k) => cong_succ(same(k, n)) }
        }
        "#,
    )
    .expect("both spellings elaborate, and agree pointwise");
}

// -- the guardedness analysis rejects ---------------------------------------

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

#[test]
fn unguarded_self_call_rejected() {
    // No enclosing match: nothing to descend on.
    let msg = elab_err("fn loop(n: Nat) -> Nat { loop(n) }");
    assert!(msg.contains("not structurally guarded"), "{msg}");
}

#[test]
fn non_descending_self_call_rejected() {
    // Passing the scrutinee itself back is the classic non-terminating loop.
    let msg = elab_err(
        "fn loop(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k) => loop(m, n) } }",
    );
    assert!(msg.contains("must descend"), "{msg}");
}

#[test]
fn varying_argument_rejected() {
    // The documented MVP limitation: a non-decreasing argument that changes
    // would need the motive to generalize it. Rejected with that explanation,
    // not left to the kernel.
    let msg = elab_err(
        "fn loop(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k) => loop(k, Succ(n)) } }",
    );
    assert!(msg.contains("unchanged"), "{msg}");
}

#[test]
fn shadowing_cannot_fake_a_guard() {
    // The analysis compares binders, not names: an inner `k` that is not the
    // predecessor does not count as descending.
    let msg = elab_err(
        r#"
        fn loop(m: Nat) -> Nat {
            match m {
                Zero => 0,
                Succ(k) => match m as λ z => Nat { Zero => 0, Succ(k, ih) => loop(k) },
            }
        }
        "#,
    );
    assert!(msg.contains("must descend"), "{msg}");
}

#[test]
fn arity_is_checked() {
    let msg = elab_err(
        "fn loop(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k) => loop(k) } }",
    );
    assert!(msg.contains("must pass all 2 argument"), "{msg}");
}

#[test]
fn self_name_is_not_a_value() {
    let msg = elab_err("fn loop(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => loop } }");
    assert!(msg.contains("saturated recursive call"), "{msg}");
}
