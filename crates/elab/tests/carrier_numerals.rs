//! Carrier anchors through nested operator notation. No standard-library
//! imports: a second carrier exercises the protocol without an Int special case.

use heather_elab::Elaborator;

const KIT: &str = r#"
class Numeral<A> { ofNat: Nat -> A }
inductive Sign { Pos(n: Nat), Neg(n: Nat) }
instance Numeral<Sign> { ofNat := Pos }
fn flip(a: Sign) -> Sign {
    match a { Pos(n) => Neg(n), Neg(n) => Pos(n) }
}
fn pick(a: Sign, b: Sign) -> Sign { a }
fn add(a: Nat, b: Nat) -> Nat {
    match a { Zero => b, Succ(n, ih) => Succ(ih) }
}
designation prefix - at Sign := flip
designation + at Sign := pick
designation + at Nat := add
fn as_sign(a: Sign) -> Sign { a }
"#;

fn check(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(KIT).expect("numeral carrier kit");
    if let Err(error) = e.elab_source(src) {
        panic!("{}", error.render(src));
    }
}

#[test]
fn expected_carrier_reaches_negative_numerals_at_checking_boundaries() {
    check(r#"
fn direct() -> Sign { -1 }
fn argument() -> Sign { as_sign(-1) }
fn nested() -> Sign { as_sign(--1) }
fn arithmetic() -> Sign { -(1 + -2) }
fn local() -> Sign { let a: Sign = -1; a }
fn value_call(f: Sign -> Sign) -> Sign { f(-1) }
record Box { value: Sign }
fn record_value() -> Box { Box { value: -1 } }
fn generic<A: Numeral>() -> A { 3 }
fn generic_call<A: Numeral>(f: A -> A) -> A { f(3) }
fn generic_op<A: Numeral>(op as +: A -> A -> A) -> A { 1 + 2 }
theorem direct_value(): direct() = Neg(1) { refl }
theorem argument_value(): argument() = Neg(1) { refl }
theorem nested_value(): nested() = Pos(1) { refl }
theorem arithmetic_value(): arithmetic() = Neg(1) { refl }
theorem local_value(): local() = Neg(1) { refl }
theorem value_call_value(): value_call(as_sign) = Neg(1) { refl }
theorem field_value(): record_value().value = Neg(1) { refl }
theorem generic_value(): generic<Sign>() = Pos(3) { refl }
theorem generic_call_value(): generic_call<Sign>(as_sign) = Pos(3) { refl }
theorem generic_op_value(): generic_op<Sign>(pick) = Pos(1) { refl }
"#);
}

#[test]
fn nested_operand_supplies_the_carrier_in_inference_position() {
    check(r#"
fn under_prefix(a: Sign) -> Sign { let b = -(1 + a); b }
fn left_nested(a: Sign) -> Sign { let b = (1 + a) + 2; b }
fn right_nested(a: Sign) -> Sign { let b = 1 + (2 + a); b }
fn nested_prefix(a: Sign) -> Sign { let b = -(-1 + a); b }
fn named_anchor() -> Sign { let b = -(1 + as_sign(Pos(2))); b }
theorem under_prefix_value(a: Sign): under_prefix(a) = Neg(1) { refl }
theorem left_nested_value(a: Sign): left_nested(a) = Pos(1) { refl }
theorem right_nested_value(a: Sign): right_nested(a) = Pos(1) { refl }
theorem nested_prefix_value(a: Sign): nested_prefix(a) = Pos(1) { refl }
theorem named_anchor_value(): named_anchor() = Neg(1) { refl }
"#);
}

#[test]
fn an_anchored_left_endpoint_checks_a_literal_right_endpoint() {
    check(r#"
theorem positive(a: Sign): 1 + a = 1 { refl }
theorem negative(a: Sign): -(1 + a) = -1 { refl }
theorem anchored_right(a: Sign): -1 = -(1 + a) { refl }
theorem concrete_right(): -1 = Neg(1) { refl }
"#);
}

#[test]
fn a_result_only_generic_call_waits_for_a_real_carrier_anchor() {
    check(r#"
fn one<A: Numeral>() -> A { 1 }
fn identity<A>(x: A) -> A { x }
fn expected_call() -> Sign { -(1 + one()) }
fn indirect_call() -> Sign { -(1 + identity(one())) }
fn anchored_call(a: Sign) -> Sign { let b = -(1 + one() + a); b }
fn indirect_anchor(a: Sign) -> Sign { let b = -(1 + identity(one()) + a); b }
theorem expected_equation(): 1 + one() = Pos(1) { refl }
theorem indirect_equation(): 1 + identity(one()) = Pos(1) { refl }
theorem expected_value(): expected_call() = Neg(1) { refl }
theorem indirect_value(): indirect_call() = Neg(1) { refl }
theorem anchored_value(a: Sign): anchored_call(a) = Neg(1) { refl }
theorem indirect_anchor_value(a: Sign): indirect_anchor(a) = Neg(1) { refl }
"#);
}

#[test]
fn nat_defaults_and_fin_indices_keep_their_intrinsic_reading() {
    check(r#"
instance Numeral<Nat> { ofNat := Succ }
fn inferred() -> Nat { let n = 3; n }
fn inferred_sum() -> Nat { let n = 1 + 2; n }
fn checked() -> Nat { 3 }
fn index(n: Nat) -> Fin(Succ(Succ(n))) { 1 }
theorem default_value(): inferred() = 3 { refl }
theorem default_sum_value(): inferred_sum() = 3 { refl }
theorem checked_value(): checked() = 3 { refl }
theorem index_value(): index(0) = FS(FZ) { refl }
"#);
}

#[test]
fn numeral_checking_preserves_refusals_and_resolution_diagnostics() {
    for (src, diagnostic) in [
        ("theorem false_value(): as_sign(-1) = Pos(1) { refl }", "kernel rejected"),
        ("fn no_coercion(n: Nat) -> Sign { as_sign(-n) }", "nothing designates `-` at `Nat`"),
        ("fn named_call() -> Sign { as_sign(add(1, 2)) }", "has type `Nat`"),
        ("fn conflicting(a: Sign, n: Nat) -> Sign { 1 + (a + n) }", "has type `Nat`"),
        ("fn out_of_bounds() -> Fin(1) { 1 }", "not an index"),
        (r#"
inductive Empty { E }
fn stay(a: Empty) -> Empty { a }
designation prefix - at Empty := stay
fn missing() -> Empty { -1 }
"#, "no instance for `Numeral<Empty>`"),
    ] {
        let mut e = Elaborator::with_prelude().expect("prelude");
        e.elab_source(KIT).expect("numeral carrier kit");
        let error = e.elab_source(src).expect_err("invalid numeral use must refuse");
        let message = error.render(src);
        assert!(message.contains(diagnostic), "{message}");
        assert!(!message.contains("parse error"), "{message}");
    }
}
