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
    // issues/simulate-conversion-cost.md, and so does the prelude's
    // `CollectionLiteral#tycode_fn`
    // (`docs/per-instantiation-type-codes-design.md` §2) together with the
    // `3·nfields + 1 = 7` projection definitions its dependent spine now gets
    // (`docs/telescoped-record-projections-design.md` §3).
    assert_eq!(e.psi().bindings.len(), 17);
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

#[test]
fn prefix_negation_is_carrier_directed() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        inductive Sign { Pos(n: Nat), Neg(n: Nat) }
        fn flip(a: Sign) -> Sign {
            match a { Pos(n) => Neg(n), Neg(n) => Pos(n) }
        }
        designation prefix - at Sign := flip
        theorem open(a: Sign): -a = flip(a) { refl }
        theorem closed(): -Pos(2) = Neg(2) { refl }
        theorem nested(a: Sign): --a = a {
            match a { Pos(n) => refl, Neg(n) => refl }
        }
        "#,
    )
    .expect("a prefix designation resolves from its operand's carrier");
}

#[test]
fn infix_subtraction_is_carrier_directed() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn cut(a, b: Nat) -> Nat {
            match a { Zero => Zero, Succ(k) => match b { Zero => Succ(k), Succ(l) => cut(k, l) } }
        }
        designation - at Nat := cut
        theorem open(a, b: Nat): a - b = cut(a, b) { refl }
        theorem closed(): 5 - 2 = 3 { refl }
        "#,
    )
    .expect("an infix designation resolves from its left operand's carrier");
}

#[test]
fn numerals_use_the_expected_carriers_instance() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        class Numeral<A> { ofNat: Nat -> A }
        inductive Wrap { W(n: Nat) }
        instance Numeral<Wrap> { ofNat := W }
        fn three() -> Wrap { 3 }
        theorem computes(): three() = W(3) { refl }
        fn generic<A: Numeral>() -> A { 1 }
        theorem generic_computes(): generic<Wrap>() = W(1) { refl }
        "#,
    )
    .expect("numerals should resolve at concrete and constrained open carriers");
}

#[test]
fn a_missing_numeral_instance_names_the_carrier_goal() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = r#"
        class Numeral<A> { ofNat: Nat -> A }
        inductive Empty { E }
        fn bad() -> Empty { 2 }
    "#;
    let err = e.elab_source(src).expect_err("a carrier with no numeral instance must refuse");
    let msg = err.render(src);
    assert!(msg.contains("no instance for `Numeral<Empty>`"), "{msg}");
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
    // Rejected at the gate, not by the parser, and the message says which two
    // things were confused (issues/check-fallback-discards-expected-type.md).
    assert!(
        e.contains("this has type `Bool`, but `leb(n, m) = True` is expected here"),
        "should die in the kernel, not the parser: {e}"
    );
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

// -- calc chains: the composed behavior (issues/calc-equational-chains.md) --
//
// The desugaring above is 2026-07-24; what these pin is 2026-08-18's finding
// (docs/calc-equational-chains-design.md): because every emitted `trans` pins
// its endpoints BY NAME, each step proof is a checking position at the stated
// equation — so the result-only deferral reaches into a step and the terse
// `cong(p)` works there, exactly as far as the LGG's wall
// (docs/congruence-in-inference-position-design.md §1.1/§1.2) and no further.

// `add` and the two lemmas the chains lean on; the scrutinees below are
// neutral (open variables), so nothing reduces away the step annotations.
const CALC_KIT: &str = r#"
fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
theorem add_zero(n: Nat): n + 0 = n {
    match n { Zero => refl, Succ(k, ih) => cong_succ(ih) }
}
theorem add_succ(m: Nat, n: Nat): m + Succ(n) = Succ(m + n) {
    match m { Zero => refl, Succ(k, ih) => cong_succ(ih) }
}
"#;

fn with_calc_kit(src: &str) -> Result<(), String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = format!("{CALC_KIT}{src}");
    e.elab_source(&src).map_err(|err| err.render(&src))
}

#[test]
fn calc_step_is_a_checking_position_for_terse_cong() {
    // The §1.1 clearance, by construction: the step states both endpoints, so
    // `cong(ih)` generalizes where the same site inside a hand-written
    // `trans(...)` chain was refused before 2026-08-18.
    with_calc_kit(
        r#"
        theorem add_comm(m: Nat, n: Nat): m + n = n + m {
            match m {
                Zero => sym(add_zero(n)),
                Succ(k, ih) => calc {
                    Succ(k) + n
                        = Succ(k + n) := refl,
                        = Succ(n + k) := cong(ih),
                        = n + Succ(k) := sym(add_succ(n, k)),
                },
            }
        }
        "#,
    )
    .expect("terse cong inside a calc step");
}

#[test]
fn calc_block_checks_in_inference_position() {
    // The block itself under `sym(...)`: no expected type reaches the calc,
    // and it still elaborates, because the named endpoints on the emitted
    // `trans` are what type the steps — including the checking-only `refl`
    // and the deferred `cong`. If the endpoints ever stopped being pinned,
    // this is the test that notices.
    with_calc_kit(
        r#"
        theorem flipped(k: Nat, n: Nat, ih: k + n = n + k): n + Succ(k) = Succ(k) + n {
            sym(calc {
                Succ(k) + n
                    = Succ(k + n) := refl,
                    = Succ(n + k) := cong(ih),
                    = n + Succ(k) := sym(add_succ(n, k)),
            })
        }
        "#,
    )
    .expect("a calc block needs no expected type");
}

#[test]
fn computation_level_context_stays_walled_inside_calc() {
    // Negative control for the design's scope guard: a §1.2 site — the
    // context (`isucc`) appears in NEITHER side's spelling, only after a δι
    // step — fails inside a calc step with the same refusal as outside one.
    // Calc changes where the expected type comes from, not what it says. If
    // this starts passing, the LGG grew; re-measure before believing it.
    let e = with_calc_kit(
        r#"
        inductive Int { OfNat(n: Nat), NegSucc(n: Nat) }
        fn isucc(a: Int) -> Int {
            match a {
                OfNat(n) => OfNat(Succ(n)),
                NegSucc(n) => match n { Zero => OfNat(0), Succ(k) => NegSucc(k) },
            }
        }
        fn addNat(a: Int, n: Nat) -> Int {
            match n { Zero => a, Succ(k, ih) => isucc(ih) }
        }
        theorem addNat_zero_l(n: Nat): addNat(OfNat(0), n) = OfNat(n) {
            match n {
                Zero => refl,
                Succ(k, ih) => calc {
                    addNat(OfNat(0), Succ(k)) = OfNat(Succ(k)) := cong(ih),
                },
            }
        }
        "#,
    )
    .expect_err("a computation-level context must still be refused");
    assert!(e.contains("cannot generalize"), "the LGG's refusal, not another error: {e}");
}

#[test]
fn the_author_states_the_reduct_as_a_refl_step() {
    // ...and the calc-native way THROUGH the wall: one refl step to the
    // reduct, after which both sides spell the context and the terse `cong`
    // generalizes. The conversion fact is stated by the human, not inferred.
    with_calc_kit(
        r#"
        inductive Int { OfNat(n: Nat), NegSucc(n: Nat) }
        fn isucc(a: Int) -> Int {
            match a {
                OfNat(n) => OfNat(Succ(n)),
                NegSucc(n) => match n { Zero => OfNat(0), Succ(k) => NegSucc(k) },
            }
        }
        fn addNat(a: Int, n: Nat) -> Int {
            match n { Zero => a, Succ(k, ih) => isucc(ih) }
        }
        theorem addNat_zero_l(n: Nat): addNat(OfNat(0), n) = OfNat(n) {
            match n {
                Zero => refl,
                Succ(k, ih) => calc {
                    addNat(OfNat(0), Succ(k))
                        = isucc(addNat(OfNat(0), k)) := refl,
                        = isucc(OfNat(k))            := cong(ih),
                        = OfNat(Succ(k))             := refl,
                },
            }
        }
        "#,
    )
    .expect("a refl step to the reduct clears the wall by hand");
}

#[test]
fn a_hole_in_a_step_is_a_goal_at_the_steps_equation() {
    // The justification seam: the slot after `:=` is an ordinary expression
    // position, so a `?hole` there raises a goal named and typed by the step,
    // discharged by `on` at the declaration block — which is what a future
    // tactic form will consume, with no change to calc.
    with_calc_kit(
        r#"
        theorem succ_comm(k: Nat, n: Nat, ih: k + n = n + k): Succ(k) + n = n + Succ(k) {
            calc {
                Succ(k) + n
                    = Succ(k + n) := refl,
                    = Succ(n + k) := ?mid,
                    = n + Succ(k) := sym(add_succ(n, k)),
            }
            on ?mid := cong(ih);
        }
        "#,
    )
    .expect("a step discharges through a named goal");
}
