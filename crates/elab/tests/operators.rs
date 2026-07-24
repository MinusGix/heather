//! Acceptance for issues/surface-operators.md: infix operators (`+` → `add`),
//! method-call syntax (`p.sym()`, `add_succ(n, k).sym()`), and `calc` blocks,
//! all desugaring (in the parser) to ordinary `Call`s — no kernel or
//! elaborator change. The whole Nat suite is written in the ergonomic surface
//! and still kernel-checked declaration by declaration; `add_comm`'s `Succ`
//! arm is the `calc` block from surface-v1 §1 (modulo `.cong_succ()` for the
//! function-value `.cong(Succ)`, which awaits the trait/function-value layer).

use heather_elab::Elaborator;

// `+` for `add`, methods for the prelude lemmas, and a `calc` chain — the
// surface the sketches use freely.
const NAT_SUITE_ERGONOMIC: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k, ih) => Succ(ih),
    }
}

theorem add_zero(n: Nat): n + 0 == n {
    match n {
        Zero => refl,
        Succ(k, ih) => ih.cong_succ(),
    }
}

theorem add_succ(m: Nat, n: Nat): m + Succ(n) == Succ(m + n) {
    match m {
        Zero => refl,
        Succ(k, ih) => ih.cong_succ(),
    }
}

theorem add_comm(m: Nat, n: Nat): m + n == n + m {
    match m {
        Zero => add_zero(n).sym(),
        Succ(k, ih) => calc {
            Succ(k) + n
                == Succ(k + n) := refl,
                == Succ(n + k) := ih.cong_succ(),
                == n + Succ(k) := add_succ(n, k).sym(),
        },
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): (a + b) + c == a + (b + c) {
    match a {
        Zero => refl,
        Succ(k, ih) => ih.cong_succ(),
    }
}
"#;

#[test]
fn nat_suite_ergonomic() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE_ERGONOMIC)
        .expect("operator/method/calc Nat suite must elaborate and kernel-check");
    assert_eq!(e.psi().bindings.len(), 7);
}

#[test]
fn plus_desugars_to_add_in_types_and_terms() {
    // `+` in both the statement (`n + 0 == n`) and the proof term reduces to
    // `add`, so `refl` still closes `2 + 2 == 4`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem two_two(): 2 + 2 == 4 { refl }
        "#,
    )
    .expect("`+` is `add`, so `2 + 2 == 4` holds by refl");
}

#[test]
fn method_style_matches_call_style() {
    // `p.sym()` and `sym(p)` elaborate to the same thing: both prove `b == a`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        theorem via_method(a: Nat, b: Nat, p: a == b): b == a { p.sym() }
        theorem via_call(a: Nat, b: Nat, p: a == b): b == a { sym(p) }
        "#,
    )
    .expect("method and call spellings both check");
}

#[test]
fn calc_single_step_is_just_the_proof() {
    // A one-step calc is definitionally its proof; `refl` closes `2+2 == 4`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem two_two(): 2 + 2 == 4 { calc { 2 + 2 == 4 := refl } }
        "#,
    )
    .expect("single-step calc");
}

#[test]
fn incoherent_calc_chain_is_kernel_rejected() {
    // A calc step whose proof does not connect the stated endpoints must be
    // rejected — by the kernel, via the `trans` the block lowers to.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem bad(n: Nat): n + 0 == n {
            calc {
                n + 0
                    == n + 1 := refl,
                    == n := refl,
            }
        }
        "#,
    );
    assert!(r.is_err(), "an incoherent calc chain must not check, got {r:?}");
}
