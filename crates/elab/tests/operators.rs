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

theorem add_zero(n: Nat): n + 0 = n {
    match n {
        Zero => refl,
        Succ(k, ih) => ih.cong_succ(),
    }
}

theorem add_succ(m: Nat, n: Nat): m + Succ(n) = Succ(m + n) {
    match m {
        Zero => refl,
        Succ(k, ih) => ih.cong_succ(),
    }
}

theorem add_comm(m: Nat, n: Nat): m + n = n + m {
    match m {
        Zero => add_zero(n).sym(),
        Succ(k, ih) => calc {
            Succ(k) + n
                = Succ(k + n) := refl,
                = Succ(n + k) := ih.cong_succ(),
                = n + Succ(k) := add_succ(n, k).sym(),
        },
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): (a + b) + c = a + (b + c) {
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
    // The `fn` counts too: it is a *defined* Ψ-global since
    // issues/simulate-conversion-cost.md.
    assert_eq!(e.psi().bindings.len(), 9);
}

#[test]
fn plus_desugars_to_add_in_types_and_terms() {
    // `+` in both the statement (`n + 0 = n`) and the proof term reduces to
    // `add`, so `refl` still closes `2 + 2 = 4`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem two_two(): 2 + 2 = 4 { refl }
        "#,
    )
    .expect("`+` is `add`, so `2 + 2 = 4` holds by refl");
}

#[test]
fn method_style_matches_call_style() {
    // `p.sym()` and `sym(p)` elaborate to the same thing: both prove `b = a`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        theorem via_method(a: Nat, b: Nat, p: a = b): b = a { p.sym() }
        theorem via_call(a: Nat, b: Nat, p: a = b): b = a { sym(p) }
        "#,
    )
    .expect("method and call spellings both check");
}

#[test]
fn calc_single_step_is_just_the_proof() {
    // A one-step calc is definitionally its proof; `refl` closes `2+2 = 4`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem two_two(): 2 + 2 = 4 { calc { 2 + 2 = 4 := refl } }
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
        theorem bad(n: Nat): n + 0 = n {
            calc {
                n + 0
                    = n + 1 := refl,
                    = n := refl,
            }
        }
        "#,
    );
    assert!(r.is_err(), "an incoherent calc chain must not check, got {r:?}");
}

// -- `<=` (issues/comparison-operators.md) ---------------------------------

// The order kit, cut down to what a comparison test needs: the boolean
// decision, the *proposition* named over it, and enough of the kit to prove
// something with. Lifted from lib/ir_v1.hthr, which is where the real ones
// live; the elaborator has no `Le` of its own and `<=` names one by ordinary
// global lookup, exactly like `+` names `add`.
const ORDER_KIT: &str = r#"
inductive Bool { False, True }

fn leb(n: Nat) -> Nat -> Bool {
    match n {
        Zero => λ (m: Nat) => True,
        Succ(k) => λ (m: Nat) => match m { Zero => False, Succ(l) => leb(k)(l) },
    }
}

fn Le(n: Nat, m: Nat) -> Type { leb(n)(m) = True }

fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
"#;

fn with_order_kit(src: &str) -> Result<(), String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!("{ORDER_KIT}{src}");
    e.elab_source(&src).map_err(|err| err.render(&src))
}

#[test]
fn le_states_and_proves_an_ordering() {
    // The kit's own shapes, written with `<=`: a statement, a hypothesis, and
    // a recursive proof whose body never mentions the operator.
    with_order_kit(
        r#"
        theorem le_refl(n: Nat): n <= n { match n { Zero => refl, Succ(k) => le_refl(k) } }
        theorem two_le_five(): 2 <= 5 { refl }
        theorem le_hyp(n: Nat, m: Nat, h: n <= m): n <= m { h }
        "#,
    )
    .expect("`<=` states and proves an ordering");
}

#[test]
fn le_is_the_proposition_and_not_the_boolean() {
    // The whole design point. `n <= m` is `Le(n, m)`, the Type — so it is
    // interchangeable with the spelled-out `Le(n, m)` in both directions, and
    // it unfolds by δ to the reflection equation. If `<=` had desugared to
    // `leb`, `h` would be a `Bool` and none of these three would check.
    with_order_kit(
        r#"
        theorem to_named(n: Nat, m: Nat, h: n <= m): Le(n, m) { h }
        theorem from_named(n: Nat, m: Nat, h: Le(n, m)): n <= m { h }
        theorem unfolds(n: Nat, m: Nat, h: n <= m): leb(n)(m) = True { h }
        "#,
    )
    .expect("`<=` is `Le`, transparently");

    // …and the negative control on the other side: the boolean itself is not
    // a proof of the proposition. `leb` stays callable by name precisely
    // because the two are different things.
    let e = with_order_kit("theorem bool_is_not_a_proof(n: Nat, m: Nat): n <= m { leb(n)(m) }")
        .expect_err("a Bool must not inhabit the proposition");
    assert!(e.contains("NotConvertible"), "should die in the kernel, not the parser: {e}");
}

#[test]
fn comparison_binds_looser_than_arithmetic() {
    // `0 + n <= m` is `Le(add(0, n), m)`, not `add(0, Le(n, m))` — so it is
    // definitionally the `n <= m` hypothesis and passes straight through.
    with_order_kit("theorem loose(n: Nat, m: Nat, h: 0 + n <= m): n <= m { h }")
        .expect("`<=` binds looser than `+`");
}

#[test]
fn chained_comparisons_are_a_parse_error() {
    // Non-associative at its own level, with a message that says so rather
    // than whatever the caller would have raised at the dangling operator.
    for src in ["a <= b <= c", "a <= b == c"] {
        let stmt = format!("theorem t(a: Nat, b: Nat, c: Nat, h: {src}): 0 = 0 {{ refl }}");
        let e = with_order_kit(&stmt).expect_err("a chained comparison must not parse");
        assert!(e.contains("do not chain"), "{src}: {e}");
    }
}

#[test]
fn generics_and_le_share_a_file() {
    // The lexer worry: `<=` is a two-byte token, and `<` opens a
    // type-argument list. A file with both — a generic record, a generic `fn`,
    // an explicit type application, and a comparison — parses.
    with_order_kit(
        r#"
        record Boxed<A> { v: A }
        fn unbox<A>(b: Boxed<A>) -> A { b.v }
        theorem boxed_le(n: Nat, m: Nat, h: n <= m): unbox<Nat>(Boxed<Nat> { v: n }) <= m { h }
        "#,
    )
    .expect("generics and `<=` coexist");
}

// -- the growth invariant, from the operators side --------------------------
//
// `+`/`<=` stopped being a parser desugaring in the operators-onto-classes
// round (docs/operators-onto-classes-design.md): the symbol survives into the
// AST and the elaborator resolves it. Everything above is the pin — the whole
// Nat suite written in `+`, with `ORDER_KIT`'s own `add`/`Le`, and **no
// designation anywhere** — and it passes unchanged because the ladder's third
// rung *is* the table this file's first paragraph described. The two tests
// below make that explicit rather than incidental.

#[test]
fn the_symbol_resolves_to_the_files_own_name() {
    // A file whose `add` is its own, and a `+` that means it. If the ladder
    // were name-first-designation-second — or if a designation could reach in
    // from another module — this is the term that would change.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }\n\
         theorem written(x: Nat, y: Nat): x + y = add(x, y) { refl }\n\
         theorem computed(): 2 + 2 = 4 { refl }\n",
    )
    .expect("`+` names this file's own `add`");
}

#[test]
fn a_symbol_with_no_name_behind_it_says_so() {
    // `*` has no designation and no `mul` in scope. Before this round the
    // message was `unbound name \`mul\``, which named something nobody wrote.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let err = e
        .elab_source("theorem t(x: Nat): x * x = x { refl }")
        .expect_err("`*` means nothing here");
    let msg = format!("{err}");
    assert!(msg.contains("`*` has no meaning here"), "{msg}");
    assert!(msg.contains("mul"), "{msg}");
}
