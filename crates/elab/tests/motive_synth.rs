//! Stage-2 motive synthesis (issues/elab-stage2-metas.md): the `match` arms
//! of the Nat suite drop their explicit `as λ z => M` motives. The elaborator
//! recovers the dependent motive by abstracting the (variable) scrutinee out
//! of the checking-position expected type; the kernel still gates every
//! declaration, so a wrong synthesized motive would be a rejection, not a
//! silent pass.

use heather_elab::Elaborator;

// The arithmetic lemmas, all `match`es motive-less. Lemma endpoints are still
// supplied explicitly (via `@`) so this file isolates motive synthesis from
// implicit-argument inference (which `implicit_args.rs` covers).
const NAT_SUITE_NO_MOTIVE: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k, ih) => Succ(ih),
    }
}

theorem add_zero(n: Nat): add(n, 0) = n {
    match n {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(k, 0), k, ih),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(k, Succ(n)), Succ(add(k, n)), ih),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m {
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
    match a {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(add(k, b), c), add(k, add(b, c)), ih),
    }
}
"#;

#[test]
fn nat_suite_motives_synthesized() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE_NO_MOTIVE)
        .expect("motive-less Nat suite must elaborate and kernel-check");
}

#[test]
fn non_dependent_motive_still_works() {
    // A match whose expected type does not mention the scrutinee: the
    // synthesized motive is non-dependent and the kernel accepts it.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        "theorem const_zero(n: Nat): 0 = 0 { match n { Zero => refl, Succ(k, ih) => ih } }",
    )
    .expect("non-dependent motive");
}
