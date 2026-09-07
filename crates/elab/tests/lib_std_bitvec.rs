//! Public fixed-width bitvectors and their generic arithmetic/bit-operation
//! kit. The carrier is exercised at closed and open widths; closed numerals
//! alone would miss an index or motive that was accidentally specialized.
//!
//! The fast lane keeps the ungated module check, the width/open-carrier
//! probe, and the open law kit. The three closed computational cross-products
//! are stable exhaustive acceptance and use the `slow_acceptance_` prefix.

use heather_elab::{ElabError, Elaborator};
use std::sync::Mutex;

mod support;

static ELAB_LOCK: Mutex<()> = Mutex::new(());

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const BITVEC: &str = include_str!("../../../lib/std/bitvec.hthr");

fn run(extra: &str) -> Result<(), String> {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let mut e = Elaborator::with_prelude().expect("prelude");
    let mut prefix_error = None;
    let mut load = |e: &mut Elaborator| {
        for (name, src) in [
            ("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION),
            ("pair", PAIR), ("list", LIST), ("algebra", ALGEBRA), ("int", INT),
            ("bitvec", BITVEC),
        ] {
            if let Err(err) = e.elab_module_source(name, src) {
                prefix_error = Some(format!("{name}: {}", err.render(src)));
                break;
            }
        }
    };
    if extra.is_empty() {
        load(&mut e);
    } else {
        support::with_decl_cache(&mut e, load);
    }
    if let Some(err) = prefix_error {
        return Err(err);
    }
    if !extra.is_empty() {
        let report_metrics = std::env::var_os("HEATHER_VALUE_METRICS").is_some();
        if report_metrics {
            e.enable_value_metrics();
        }
        let src = format!("import bitvec;\nimport bool;\nimport logic;\n{extra}");
        if let Err(err) = e.elab_module_source("probe", &src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
        if report_metrics {
            eprintln!("bitvec probe value metrics: {:?}", e.value_metrics().unwrap());
        }
    }
    Ok(())
}

fn ok(src: &str) { run(src).unwrap_or_else(|e| panic!("expected this to check: {e}")); }

fn bad(src: &str) {
    assert!(run(src).is_err(), "expected this to be refused:\n{src}");
}

#[test]
fn the_bitvec_module_checks() { ok(""); }

/// `from_bits(64, [...])` spelling `value`, least-significant bit first — an
/// independent statement of the bits `ofNat` must produce.
fn bit_vector_literal(value: u64) -> String {
    let bits: Vec<&str> = (0..64)
        .map(|i| if (value >> i) & 1 == 1 { "True" } else { "False" })
        .collect();
    format!("from_bits(64, [{}])", bits.join(", "))
}

/// `ofNat` at machine width costs the width, not the literal's magnitude
/// (issues/bitvec-ofnat-large-literals.md). Each literal is checked against
/// an independently written bit vector, and round-trips through `toNat`; the
/// controls flip one bit of the expected vector and must be refused for the
/// right reason (a conversion failure, not exhausted fuel, which is what the
/// magnitude-recursive definition produced at these arguments).
#[test]
fn of_nat_at_machine_width_costs_the_width_not_the_magnitude() {
    const ASYMMETRIC: u64 = 0x0123_4567_89AB_CDEF;
    const HIGH_BIT: u64 = 0x8000_0000_0000_0001;
    let mut src = String::from("import nat;\n");
    for (name, value) in [
        ("asymmetric", ASYMMETRIC),
        ("high_bit", HIGH_BIT),
        ("saturated", u64::MAX),
        ("mid", 70_000),
    ] {
        src.push_str(&format!(
            "theorem {name}_bits(): ofNat(64, {value}) = {} {{ refl }}\n\
             theorem {name}_round_trip(): toNat(64, ofNat(64, {value})) = {value} {{ refl }}\n",
            bit_vector_literal(value),
        ));
    }
    // Truncation modulo the width survives the top-down reading.
    src.push_str(
        "theorem truncates(): ofNat(8, 261) = ofNat(8, 5) { refl }\n\
         theorem truncates_to_nat(): toNat(8, ofNat(8, 261)) = 5 { refl }\n\
         theorem powers_are_one_run(): nat::pow(2, 63) = 9223372036854775808 { refl }\n\
         theorem doubling_is_one_run(): nat::twice(9223372036854775807) = 18446744073709551614 { refl }\n\
         theorem run_scrutinee_chain(): nat::mul(2, 65536) = 131072 { refl }\n\
         theorem doubling_chain_under_a_consumer(): nat::leb(nat::pow(2, 40), 1099511627776) = True { refl }\n",
    );
    ok(&src);

    for (value, flipped) in [(ASYMMETRIC, 0), (HIGH_BIT, 63), (u64::MAX, 31)] {
        let src = format!(
            "theorem wrong(): ofNat(64, {value}) = {} {{ refl }}",
            bit_vector_literal(value ^ (1 << flipped)),
        );
        let msg = run(&src).expect_err("a flipped bit must be refused");
        assert!(msg.contains("NotConvertible"), "{msg}");
    }
    let msg = run("theorem wrong(): toNat(64, ofNat(64, 81985529216486895)) = 81985529216486896 { refl }")
        .expect_err("an off-by-one round trip must be refused");
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn widths_include_zero_machine_sizes_and_a_neutral() {
    ok(r#"
fn w0() -> BitVec(0) { zero(0) }
fn w1() -> BitVec(1) { one(1) }
fn w8() -> BitVec(8) { zero(8) }
fn w16() -> BitVec(16) { all_ones(16) }
fn w32() -> BitVec(32) { complement(32, zero(32)) }
fn w64() -> BitVec(64) { shift_left(64, one(64), 63) }
fn neutral(n: Nat, x, y: BitVec(n)) -> BitVec(n) {
    bxor(n, add(n, x, y), shift_right(n, band(n, x, y), n))
}
theorem z0(): w0() = from_bits(0, []) { refl }
theorem z1(): toNat(1, w1()) = 1 { refl }
"#);
}

#[test]
fn slow_acceptance_bitwise_shape_and_conversion_compute() {
    ok(r#"
fn five() -> BitVec(3) { from_bits(3, [True, False, True]) }
theorem value(): toNat(3, five()) = 5 { refl }
theorem not5(): complement(3, five()) = from_bits(3, [False, True, False]) { refl }
theorem and5(): band(3, five(), from_bits(3, [True, True, False])) =
                from_bits(3, [True, False, False]) { refl }
theorem or5(): bor(3, five(), from_bits(3, [False, True, False])) =
               from_bits(3, [True, True, True]) { refl }
theorem xor5(): bxor(3, five(), from_bits(3, [True, True, False])) =
                from_bits(3, [False, True, True]) { refl }
theorem wraps_construct(): toNat(8, ofNat(8, 300)) = 44 { refl }
theorem signed_minus_one(): toInt(4, ofNat(4, 15)) = NegSucc(0) { refl }
fn equal_byte(a, b: BitVec(8)) -> Bool {
    match bitvec::eq_dec(8, a, b) { Inl(_) => True, Inr(_) => False }
}
theorem byte_eq_yes(): equal_byte(ofNat(8, 137), ofNat(8, 137)) = True { refl }
theorem byte_eq_no(): equal_byte(ofNat(8, 137), ofNat(8, 139)) = False { refl }
"#);
    bad("theorem wrong(): toNat(3, from_bits(3, [True, False, True])) = 6 { refl }");
}

#[test]
fn slow_acceptance_arithmetic_is_modulo_the_width_and_reports_alu_conditions() {
    if std::env::var_os("HEATHER_VALUE_METRICS").is_some() {
        ok(r#"
theorem carry_bit_machine_width_only():
    carry_add_bit(64, all_ones(64), one(64)) = True { refl }
"#);
    }
    ok(r#"
theorem add_wrap(): toNat(4, add(4, ofNat(4, 14), ofNat(4, 3))) = 1 { refl }
theorem sub_wrap(): toNat(4, sub(4, ofNat(4, 3), ofNat(4, 5))) = 14 { refl }
theorem neg_wrap(): toNat(4, neg(4, ofNat(4, 1))) = 15 { refl }
theorem mul_wrap(): toNat(4, mul(4, ofNat(4, 4), ofNat(4, 5))) = 4 { refl }
theorem carry(): carry_add(4, ofNat(4, 14), ofNat(4, 3)) { trivial }
theorem borrow(): borrow_sub(4, ofNat(4, 3), ofNat(4, 5)) { trivial }
theorem ov_add(): signed_overflow_add(4, ofNat(4, 7), ofNat(4, 1)) = True { refl }
theorem ov_sub(): signed_overflow_sub(4, ofNat(4, 8), ofNat(4, 1)) = True { refl }
theorem width_zero_add(): add(0, zero(0), zero(0)) = zero(0) { refl }
theorem carry_bit_yes(): carry_add_bit(4, ofNat(4, 14), ofNat(4, 3)) = True { refl }
theorem carry_bit_no(): carry_add_bit(4, ofNat(4, 1), ofNat(4, 1)) = False { refl }
theorem borrow_bit_yes(): borrow_sub_bit(4, ofNat(4, 3), ofNat(4, 5)) = True { refl }
theorem borrow_bit_no(): borrow_sub_bit(4, ofNat(4, 5), ofNat(4, 3)) = False { refl }
theorem borrow_bit_machine_width():
    borrow_sub_bit(64, zero(64), one(64)) = True { refl }
theorem carry_bit_machine_width():
    carry_add_bit(64, all_ones(64), one(64)) = True { refl }
"#);
    bad("theorem no_carry(): carry_add(4, ofNat(4, 1), ofNat(4, 1)) { trivial }");
}

#[test]
fn slow_acceptance_slicing_extension_concat_and_shifts_compute() {
    ok(r#"
fn lo() -> BitVec(3) { from_bits(3, [True, False, True]) }
fn hi() -> BitVec(2) { from_bits(2, [False, True]) }
theorem cat(): concat(3, 2, lo(), hi()) =
               from_bits(5, [True, False, True, False, True]) { refl }
theorem cut(): slice(1, 3, 1, concat(3, 2, lo(), hi())) =
               from_bits(3, [False, True, False]) { refl }
theorem zext(): zero_extend(3, 2, lo()) =
                from_bits(5, [True, False, True, False, False]) { refl }
theorem sext(): sign_extend(2, 2, lo()) =
                from_bits(5, [True, False, True, True, True]) { refl }
theorem shl(): shift_left(4, ofNat(4, 3), 2) = ofNat(4, 12) { refl }
theorem shr(): shift_right(4, ofNat(4, 12), 2) = ofNat(4, 3) { refl }
theorem ashr(): arithmetic_shift_right(4, ofNat(4, 12), 2) = ofNat(4, 15) { refl }
"#);
}

#[test]
fn laws_hold_at_open_values_and_widths() {
    ok(r#"
theorem xself(n: Nat, x: BitVec(n)): bxor(n, x, x) = zero(n) { xor_self(n, x) }
theorem add_is_commutative(n: Nat, x, y: BitVec(n)): add(n, x, y) = add(n, y, x) {
    add_comm(n, x, y)
}
theorem cancel(n: Nat, x, y: BitVec(n)): sub(n, add(n, x, y), y) = x {
    add_sub_cancel(n, x, y)
}
theorem updated(n: Nat, x: BitVec(n), i: Fin(n), b: Bool):
    get(n, set(n, x, i, b), i) = b { get_set_same(n, x, i, b) }
theorem low(n, m: Nat, x: BitVec(n), y: BitVec(m)):
    take_low(n, m, concat(n, m, x, y)) = x { split_concat_low(n, m, x, y) }
theorem high(n, m: Nat, x: BitVec(n), y: BitVec(m)):
    drop_low(n, m, concat(n, m, x, y)) = y { split_concat_high(n, m, x, y) }
theorem zround(n, m: Nat, x: BitVec(n)):
    truncate(n, m, zero_extend(n, m, x)) = x { truncate_zero_extend(n, m, x) }
theorem sround(n, m: Nat, x: BitVec(Succ(n))):
    truncate(Succ(n), m, sign_extend(n, m, x)) = x { truncate_sign_extend(n, m, x) }
theorem ext(n: Nat, x, y: BitVec(n), at: (i: Fin(n)) -> get(n, x, i) = get(n, y, i)):
    x = y { extensionality(n, x, y, at) }
theorem equality_is_decidable(n: Nat, x, y: BitVec(n)): x = y ∨ x ≠ y {
    bitvec::eq_dec(n, x, y)
}

theorem carry_equiv(n: Nat, x, y: BitVec(n)):
    (carry_add_bit(n, x, y) = True) ↔ carry_add(n, x, y)
{ carry_add_bit_true_iff(n, x, y) }

theorem carry_forward(n: Nat, x, y: BitVec(n),
    h: carry_add_bit(n, x, y) = True): carry_add(n, x, y)
{ carry_add_of_bit_true(n, x, y, h) }

theorem carry_backward64(x, y: BitVec(64), h: carry_add(64, x, y)):
    carry_add_bit(64, x, y) = True
{ carry_add_bit_of_carry(64, x, y, h) }

theorem borrow_equiv(n: Nat, x, y: BitVec(n)):
    (borrow_sub_bit(n, x, y) = True) ↔ borrow_sub(n, x, y)
{ borrow_sub_bit_true_iff(n, x, y) }

theorem borrow_forward(n: Nat, x, y: BitVec(n),
    h: borrow_sub_bit(n, x, y) = True): borrow_sub(n, x, y)
{ borrow_sub_of_bit_true(n, x, y, h) }

theorem borrow_backward64(x, y: BitVec(64), h: borrow_sub(64, x, y)):
    borrow_sub_bit(64, x, y) = True
{ borrow_sub_bit_of_borrow(64, x, y, h) }
"#);
    bad("theorem fake(n: Nat, x: BitVec(n)): bxor(n, x, x) = zero(n) { refl }");
}

#[test]
fn add_commutativity_covers_width_and_carry_boundaries() {
    ok(r#"
theorem width_zero(): add(0, zero(0), zero(0)) = add(0, zero(0), zero(0)) {
    add_comm(0, zero(0), zero(0))
}
theorem width_one(): add(1, zero(1), one(1)) = add(1, one(1), zero(1)) {
    add_comm(1, zero(1), one(1))
}
theorem machine_width(left, right: BitVec(64)):
    add(64, left, right) = add(64, right, left) {
    add_comm(64, left, right)
}
theorem carry_out():
    add(8, all_ones(8), one(8)) = add(8, one(8), all_ones(8)) {
    add_comm(8, all_ones(8), one(8))
}
theorem unequal_high_bits():
    add(8, ofNat(8, 128), ofNat(8, 3)) =
    add(8, ofNat(8, 3), ofNat(8, 128)) {
    add_comm(8, ofNat(8, 128), ofNat(8, 3))
}
"#);
    bad(r#"
theorem commutativity_is_not_absorption(n: Nat, left, right: BitVec(n)):
    add(n, left, right) = left {
    add_comm(n, left, right)
}
"#);
}

#[test]
fn open_symbolic_bitvector_wrappers_stop_at_matching_definition_heads() {
    // These transparent wrappers used to normalize their structural bodies
    // completely before conversion compared them with the definition exposed
    // after one delta step: producer failed at width 5, consumer at width 8.
    // Both now rendezvous at the matching global head at machine width.
    ok(r#"
fn produce(n: Nat, left, right: BitVec(n)) -> BitVec(n) {
    band(n, left, right)
}
fn is_zero(n: Nat) -> BitVec(n) -> Bool {
    match n as λ k => BitVec(k) -> Bool {
        Zero => λ x => True,
        Succ(k, ih) => λ x => bool::not(head_bit(k, x)) && ih(tail_bits(k, x)),
    }
}
fn consume(n: Nat, value: BitVec(n)) -> Bool { is_zero(n, value) }
fn ignore(n: Nat, left, right: BitVec(n)) -> Bool { False }

theorem direct(left, right: BitVec(64)):
    band(64, left, right) = band(64, left, right) { refl }
theorem unused(left, right: BitVec(64)): ignore(64, left, right) = False { refl }
theorem producer_sixty_four(left, right: BitVec(64)):
    produce(64, left, right) = band(64, left, right) { refl }
theorem consumer_sixty_four(value: BitVec(64)):
    consume(64, value) = is_zero(64, value) { refl }
"#);
}
