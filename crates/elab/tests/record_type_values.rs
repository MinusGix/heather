//! Acceptance for record types as `Val -> Type` function values, against the
//! sketch of `issues/record-types-as-type-valued-functions.md` and
//! `docs/language/record-type-values.md` §5. Sibling round:
//! `crates/elab/tests/constructor_values.rs` — same disambiguator (the expected
//! type selects the reading), pointed the other way.
//!
//! The axes `docs/testing-generated-terms.md` asks for are varied on purpose:
//! the value argument is a *literal* in one test and a *neutral* in the next,
//! the element type is **open** in `an_open_element_type_comes_along`, every
//! positive test occupies a *checking* position that is then used (projected
//! from, transported along) rather than merely elaborated, and §5's negative
//! controls pin the constructor reading where it still wins.

use heather_elab::{ElabError, Elaborator};

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

// The issue's two failing spellings, and the control they were measured
// against. `BoxedT` is the named wrapper; `λ (v: Nat) => Boxed(v)` is the
// anonymous one; both flow into a `Nat -> Type` consumer.
//
// Elaborating them is not the test — *inhabiting* them is. `all_boxed` proves
// `AllOf(BoxedT)`, which can only be checked if the term the new arm produced
// is the record's lowered type and not something else that happens to sit at
// `Type`.
#[test]
fn a_record_type_is_a_type_valued_function() {
    elab(
        r#"
        record Boxed(v: Nat) { pf: v = v, }

        fn BoxedT(v: Nat) -> Type { Boxed(v) }
        fn AllOf(dom: Nat -> Type) -> Type { (n: Nat) -> dom(n) }

        fn UseNamed() -> Type { AllOf(BoxedT) }
        fn UseLambda() -> Type { AllOf(λ (v: Nat) => Boxed(v)) }

        theorem all_named(): AllOf(BoxedT) { λ n => Boxed { pf: refl } }
        theorem all_lambda(): AllOf(λ (v: Nat) => Boxed(v)) { λ n => Boxed { pf: refl } }

        // the wrapper is the record type, at a *literal* and at a *neutral*
        // value argument
        theorem at_literal(): BoxedT(3) { Boxed { pf: refl } }
        theorem at_neutral(v: Nat): BoxedT(v) { Boxed { pf: refl } }

        // …and convertible with the type-position spelling in both directions
        fn mk(v: Nat) -> Boxed(v) { Boxed { pf: refl } }
        theorem same(v: Nat): BoxedT(v) { mk(v) }
        theorem same_back(v: Nat): Boxed(v) { at_neutral(v) }
        "#,
    );
}

// **The payoff**, in miniature: `lib/certgen/ir_v1.hthr`'s `RefinesOn(dom: Val -> Type,
// …)`. The domain is a record *value*, the hypothesis is an inhabitant of it,
// and the proof projects a field off that hypothesis and transports along it.
//
// Both halves of that sentence were broken before this round in ways the
// routing arm alone does not fix (docs/language/record-type-values.md §4): `d.shape` is
// a projection off a type that arrived as `El` of a β-redex, and `sym(d.shape)`
// unifies an implicit endpoint against an `El`-wrapped `Id`.
#[test]
fn a_record_domain_can_be_projected_and_transported() {
    elab(
        r#"
        fn pos(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => 1 } }

        record Shaped(e: Nat) { a: Nat, shape: e = Succ(a), }

        fn HoldsOn(dom: Nat -> Type) -> Type { (n: Nat) -> dom(n) -> pos(n) = 1 }

        theorem shaped_is_positive(): HoldsOn(λ (e: Nat) => Shaped(e))
        { λ n d => j(sym(d.shape), λ z q => pos(z) = 1, refl) }

        // the domain is genuinely inhabited, so the statement is not vacuous
        theorem three_is_shaped(): Shaped(3) { Shaped { a: 2, shape: refl } }
        theorem applied(): pos(3) = 1 { shaped_is_positive()(3, three_is_shaped()) }
        "#,
    );
}

// The **open element type** axis. `Boxed<A>` is monomorphized per
// instantiation, so `Boxed` itself is not a `Type -> Type` value (the issue's
// scope fence) — but `Boxed<A>(v)` with `A` a declaration's own open parameter
// is a `Nat -> Type` value, and that is the case that hid three of the five
// defects docs/testing-generated-terms.md counts.
#[test]
fn an_open_element_type_comes_along() {
    elab(
        r#"
        record Boxed<A>(v: Nat) { val: A, pf: v = v, }

        fn AllOf(dom: Nat -> Type) -> Type { (n: Nat) -> dom(n) }

        // open: `A` is this declaration's parameter, not a written type
        fn OpenT<A>(v: Nat) -> Type { Boxed<A>(v) }
        fn OpenAll<A>() -> Type { AllOf(λ (v: Nat) => Boxed<A>(v)) }

        // closed instantiations of the same declaration, used
        fn NatT(v: Nat) -> Type { Boxed<Nat>(v) }
        fn at_nat(v: Nat) -> NatT(v) { Boxed { val: 7, pf: refl } }
        theorem projected(v: Nat): at_nat(v).val = 7 { refl }

        inductive Bool { True, False }
        fn BoolT(v: Nat) -> Type { Boxed<Bool>(v) }
        fn at_bool(v: Nat) -> BoolT(v) { Boxed { val: True, pf: refl } }
        theorem bool_projected(v: Nat): at_bool(v).val = True { refl }
        theorem open_matches(v: Nat): OpenT<Nat>(v) { at_nat(v) }
        "#,
    );
}

// A value parameter that appears **only inside a field's type** — the exact
// shape the old diagnostic complained about. At `Type` there is nothing to
// infer: the argument is written, and the type former reads it directly.
#[test]
fn a_field_determined_value_parameter_is_no_obstacle_at_a_universe() {
    elab(
        r#"
        record Eqn(x: Nat, y: Nat) { pf: x = y, }

        fn EqnT(x: Nat, y: Nat) -> Type { Eqn(x, y) }
        fn Diag(dom: Nat -> Type) -> Type { (n: Nat) -> dom(n) }

        theorem diag(): Diag(λ (n: Nat) => Eqn(n, n)) { λ n => Eqn { pf: refl } }
        theorem named(n: Nat): EqnT(n, n) { Eqn { pf: refl } }
        fn eqn(n: Nat) -> EqnT(n, n) { Eqn { pf: refl } }
        theorem field(n: Nat): eqn(n).pf = refl { refl }
        "#,
    );
}

// §5 negative controls, part 1: **the constructor reading still wins** wherever
// the expected type is the record itself. Nothing about the universe arm is
// reachable from these positions, and each spelling below is one the
// constructor round owns.
#[test]
fn the_constructor_reading_still_wins_at_the_record() {
    elab(
        r#"
        record Boxed(v: Nat) { pf: v = v, }

        // a record literal, and the positional constructor spelling
        fn mk(v: Nat) -> Boxed(v) { Boxed { pf: refl } }
        fn mk_positional(v: Nat) -> Boxed(v) { Boxed(refl) }
        theorem agree(v: Nat): mk(v) = mk_positional(v) { refl }

        // unsaturated, η-expanded against an expected Π
        // (docs/language/constructor-function-values.md §2)
        fn mk_fn(v: Nat) -> (v = v) -> Boxed(v) { Boxed }
        theorem eta(v: Nat): mk_fn(v)(refl) = Boxed(refl) { refl }
        "#,
    );
}

// §5 negative controls, part 2: the diagnostics. The point of the round is not
// only that the good spellings check — it is that a *bad* one is now measured
// against the record's value-parameter telescope instead of against the
// constructor's inability to infer.
#[test]
fn rejections() {
    // Too many value arguments, at `Type`: the telescope's message, not
    // "cannot infer the value argument(s) of `Boxed`".
    let msg = elab_err(
        r#"
        record Boxed(v: Nat) { pf: v = v, }
        fn Bad(v: Nat) -> Type { Boxed(v, v) }
        "#,
    );
    assert!(msg.contains("takes 1 value argument(s), found 2"), "{msg}");
    assert!(!msg.contains("cannot infer"), "{msg}");

    // A declaration with *no* value parameters, applied. `try_valparam_ty`
    // declines on an empty telescope, so this message is the routing arm's own.
    let msg = elab_err(
        r#"
        inductive Plain { A, B }
        fn Bad() -> Type { Plain(0) }
        "#,
    );
    assert!(msg.contains("takes 0 value argument(s), found 1"), "{msg}");
    assert!(msg.contains("write it bare"), "{msg}");

    // Not enough value arguments is the same telescope message.
    let msg = elab_err(
        r#"
        record Eqn(x: Nat, y: Nat) { pf: x = y, }
        fn Bad(n: Nat) -> Type { Eqn(n) }
        "#,
    );
    assert!(msg.contains("takes 2 value argument(s), found 1"), "{msg}");

    // The boundary stays where the constructor round put it: **inference**
    // position is still unsupported, and still says so in the constructor's
    // voice, because in that position no expected type has selected a reading.
    let msg = elab_err(
        r#"
        record Boxed(v: Nat) { pf: v = v, }
        fn Bad(v: Nat) -> Nat { let T = Boxed(v); 0 }
        "#,
    );
    assert!(msg.contains("infer"), "{msg}");

    // A level mismatch is still a level mismatch: `Type<1>` is not where a
    // level-0 record lands (docs/language/surface-universe.md §6).
    let msg = elab_err(
        r#"
        record Boxed(v: Nat) { pf: v = v, }
        fn Bad(v: Nat) -> Type<1> { Boxed(v) }
        "#,
    );
    assert!(msg.contains("non-cumulative"), "{msg}");
}

// A local binder shadowing the declaration's name keeps its ordinary meaning:
// the routing arm consults `shadowed` before it consults `inductives`, so a
// `Nat -> Type` *parameter* called `Boxed` is called, not lowered.
#[test]
fn a_shadowing_binder_is_still_a_call() {
    elab(
        r#"
        record Boxed(v: Nat) { pf: v = v, }

        fn Under(Boxed: Nat -> Type, n: Nat) -> Type { Boxed(n) }
        fn IsZero(v: Nat) -> Type { v = 0 }

        theorem used(): Under(IsZero, 0) { refl }
        "#,
    );
}
