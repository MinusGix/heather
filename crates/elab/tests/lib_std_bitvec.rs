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
         theorem hex_spelling(): ofNat(64, 0x0123_4567_89AB_CDEF) = ofNat(64, 81985529216486895) { refl }\n\
         theorem hex_high_bit(): toNat(64, ofNat(64, 0x8000_0000_0000_0001)) = 9223372036854775809 { refl }\n\
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
    // A radix spelling is the same literal: one hex digit off is refused.
    let msg = run("theorem wrong(): ofNat(64, 0x0123_4567_89AB_CDEE) = ofNat(64, 81985529216486895) { refl }")
        .expect_err("a hex digit off must be refused");
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

/// `from_bits(width, [...])` spelling the low `width` bits of `value`,
/// least-significant first.
fn bit_vector_literal_at(width: u32, value: u128) -> String {
    let bits: Vec<&str> = (0..width)
        .map(|i| if (value >> i) & 1 == 1 { "True" } else { "False" })
        .collect();
    format!("from_bits({width}, [{}])", bits.join(", "))
}

/// The ripple operations are equal to `add`/`sub`/`neg` at an open width and
/// open operands (issues/bitvec-bounded-add-sub.md), the incoming carry and
/// borrow mean the extra unit they add or remove, and the transport lemmas
/// move a fact between the two spellings in both directions. The controls
/// are a misstated theorem and a bare `refl` between the two definitions at
/// open operands: the equation is a theorem, not a computation.
#[test]
fn ripple_arithmetic_equals_add_and_sub_at_open_widths_and_operands() {
    ok(r#"
import nat;
theorem ripple_add_is_add(n: Nat, x, y: BitVec(n)):
    ripple_add(n, x, y) = bitvec::add(n, x, y) { ripple_add_eq_add(n, x, y) }
theorem ripple_sub_is_sub(n: Nat, x, y: BitVec(n)):
    ripple_sub(n, x, y) = bitvec::sub(n, x, y) { ripple_sub_eq_sub(n, x, y) }
theorem ripple_neg_is_neg(n: Nat, x: BitVec(n)):
    ripple_neg(n, x) = bitvec::neg(n, x) { ripple_neg_eq_neg(n, x) }
theorem carry_in_meaning(n: Nat, x, y: BitVec(n), c: Bool):
    add_bits(n, x, y, c) = iterate_increment(n, x, toNat(n, y) + bit_value(c))
{ add_bits_spec(n, x, y, c) }
theorem borrow_in_meaning(n: Nat, x, y: BitVec(n), c: Bool):
    sub_bits(n, x, y, c) = iterate_decrement(n, toNat(n, y) + bit_value(c), x)
{ sub_bits_spec(n, x, y, c) }
theorem machine_width_add(x, y: BitVec(64)):
    ripple_add(64, x, y) = bitvec::add(64, x, y) { ripple_add_eq_add(64, x, y) }
theorem machine_width_sub(x, y: BitVec(64)):
    ripple_sub(64, x, y) = bitvec::sub(64, x, y) { ripple_sub_eq_sub(64, x, y) }
theorem width_zero_carry(x, y: BitVec(0), c: Bool): add_bits(0, x, y, c) = zero(0) { refl }
theorem transport_forward(n: Nat, x, y, r: BitVec(n), h: ripple_add(n, x, y) = r):
    bitvec::add(n, x, y) = r { add_eq_of_ripple_add(n, x, y, r, h) }
theorem transport_backward(n: Nat, x, y, r: BitVec(n), h: bitvec::sub(n, x, y) = r):
    ripple_sub(n, x, y) = r { ripple_sub_eq_of_sub(n, x, y, r, h) }
theorem transport_neg(n: Nat, x, r: BitVec(n), h: ripple_neg(n, x) = r):
    bitvec::neg(n, x) = r { neg_eq_of_ripple_neg(n, x, r, h) }
theorem inherited_comm(n: Nat, x, y: BitVec(n)):
    ripple_add(n, x, y) = ripple_add(n, y, x) { ripple_add_comm(n, x, y) }
theorem inherited_cancel(n: Nat, x, y: BitVec(n)):
    ripple_sub(n, ripple_add(n, x, y), y) = x { ripple_add_sub_cancel(n, x, y) }
theorem congruence(n: Nat, x, y, z: BitVec(n), p: x = y):
    ripple_add(n, x, z) = ripple_add(n, y, z) { cong_ripple_add(n, p, refl) }
theorem consumer_transport(n: Nat, x, y: BitVec(n)):
    sign_bit(n, ripple_add(n, x, y)) = sign_bit(n, bitvec::add(n, x, y))
{ j(ripple_add_eq_add(n, x, y), λ z q => sign_bit(n, ripple_add(n, x, y)) = sign_bit(n, z), refl) }
"#);
    bad(r#"
theorem misstated(n: Nat, x, y: BitVec(n)):
    ripple_add(n, x, y) = bitvec::add(n, y, x) { ripple_add_eq_add(n, x, y) }
"#);
    let msg = run(r#"
theorem not_by_computation(n: Nat, x, y: BitVec(n)):
    ripple_add(n, x, y) = bitvec::add(n, x, y) { refl }
"#)
    .expect_err("the two definitions are not convertible at open operands");
    assert!(msg.contains("NotConvertible"), "{msg}");
}

/// The ripple's closed cost is the width, not the operand
/// (issues/bitvec-bounded-add-sub.md): every machine-width case below —
/// wraparound, underflow, the high-bit boundary, mixed bits, and the
/// full-width negative-offset pattern a sign-extended displacement produces —
/// is checked against an independently written bit vector and against the
/// `ofNat` literal, and the canonical `add`/`sub`/`neg` facts are proved by
/// transporting the ripple's `refl`. Small widths compare the ripple with
/// the old definitions directly, but only at small counts: `add(8, _, 248)`
/// is 248 increments and already costs gigabytes, which is the very
/// iteration this issue removes. The controls flip one bit or miss by one
/// and must be refused as `NotConvertible`, not as exhausted fuel.
#[test]
fn ripple_add_and_sub_cost_the_width_not_the_magnitude() {
    const M: u128 = 1 << 64;
    const ASYMMETRIC: u128 = 0x0123_4567_89AB_CDEF;
    const REVERSED: u128 = 0xFEDC_BA98_7654_3210;
    const HIGH: u128 = 1 << 63;
    const ADDRESS: u128 = 0x0000_7FFF_FFFF_F000;
    const MINUS_EIGHT: u128 = M - 8;
    let of = |v: u128| format!("ofNat(64, {v})");
    let mut src = String::from("import nat;\n");
    for (name, expr, value) in [
        ("neg_offset_add", format!("ripple_add(64, {}, {})", of(ADDRESS), of(MINUS_EIGHT)), ADDRESS - 8),
        ("neg_offset_sub", format!("ripple_sub(64, {}, {})", of(ADDRESS), of(MINUS_EIGHT)), ADDRESS + 8),
        ("neg_rel32_from_zero", format!("ripple_sub(64, zero(64), {})", of(0x1234)), M - 0x1234),
        ("neg_rel32", format!("ripple_neg(64, {})", of(0x1234)), M - 0x1234),
        ("wrap", "ripple_add(64, all_ones(64), one(64))".to_string(), 0),
        ("underflow", "ripple_sub(64, zero(64), one(64))".to_string(), M - 1),
        ("saturated_pair", "ripple_add(64, all_ones(64), all_ones(64))".to_string(), M - 2),
        ("high_bit_up", format!("ripple_add(64, {}, one(64))", of(HIGH - 1)), HIGH),
        ("high_bit_down", format!("ripple_sub(64, {}, one(64))", of(HIGH)), HIGH - 1),
        ("high_bit_double", format!("ripple_add(64, {}, {})", of(HIGH), of(HIGH)), 0),
        ("mixed_add", format!("ripple_add(64, {}, {})", of(ASYMMETRIC), of(REVERSED)), (ASYMMETRIC + REVERSED) % M),
        ("mixed_sub", format!("ripple_sub(64, {}, {})", of(ASYMMETRIC), of(REVERSED)), (M + ASYMMETRIC - REVERSED) % M),
        ("magnitude_small", format!("ripple_add(64, {}, {})", of(ADDRESS), of(1024)), ADDRESS + 1024),
        ("magnitude_huge", format!("ripple_add(64, {}, {})", of(ADDRESS), of(HIGH)), ADDRESS + HIGH),
    ] {
        src.push_str(&format!(
            "theorem {name}(): {expr} = {} {{ refl }}\n\
             theorem {name}_of_nat(): {expr} = {} {{ refl }}\n",
            bit_vector_literal_at(64, value), of(value),
        ));
    }
    src.push_str(&format!(
        "theorem canonical_add(): bitvec::add(64, {a}, {b}) = {r} {{ add_eq_of_ripple_add(64, {a}, {b}, {r}, refl) }}\n\
         theorem canonical_sub(): bitvec::sub(64, {a}, {b}) = {s} {{ sub_eq_of_ripple_sub(64, {a}, {b}, {s}, refl) }}\n\
         theorem canonical_neg(): bitvec::neg(64, {c}) = {n} {{ neg_eq_of_ripple_neg(64, {c}, {n}, refl) }}\n\
         theorem neg_offset_is_old_sub(): ripple_add(64, {a}, {b}) = bitvec::sub(64, {a}, {e}) {{ refl }}\n\
         theorem minus_one_is_old_sub(): ripple_add(64, {a}, {m}) = bitvec::sub(64, {a}, one(64)) {{ refl }}\n\
         theorem sub_minus_one_is_old_add(): ripple_sub(64, {a}, {m}) = bitvec::add(64, {a}, one(64)) {{ refl }}\n",
        a = of(ADDRESS), b = of(MINUS_EIGHT), r = of(ADDRESS - 8), s = of(ADDRESS + 8),
        c = of(0x1234), n = of(M - 0x1234), e = of(8), m = of(M - 1),
    ));
    src.push_str(&format!(
        "theorem w32_neg_offset(): ripple_add(32, ofNat(32, 2147479552), ofNat(32, 4294967288)) = ofNat(32, 2147479544) {{ refl }}\n\
         theorem w32_wrap(): ripple_add(32, all_ones(32), one(32)) = zero(32) {{ refl }}\n\
         theorem w32_high(): ripple_sub(32, ofNat(32, 2147483648), one(32)) = {} {{ refl }}\n",
        bit_vector_literal_at(32, (1 << 31) - 1),
    ));
    src.push_str(
        "theorem w0_add(): ripple_add(0, zero(0), zero(0)) = bitvec::add(0, zero(0), zero(0)) { refl }\n\
         theorem w0_sub(): ripple_sub(0, zero(0), zero(0)) = bitvec::sub(0, zero(0), zero(0)) { refl }\n\
         theorem w1_wrap(): ripple_add(1, one(1), one(1)) = bitvec::add(1, one(1), one(1)) { refl }\n\
         theorem w1_underflow(): ripple_sub(1, zero(1), one(1)) = bitvec::sub(1, zero(1), one(1)) { refl }\n\
         theorem w8_wrap(): ripple_add(8, ofNat(8, 250), ofNat(8, 9)) = bitvec::add(8, ofNat(8, 250), ofNat(8, 9)) { refl }\n\
         theorem w8_underflow(): ripple_sub(8, ofNat(8, 3), ofNat(8, 5)) = bitvec::sub(8, ofNat(8, 3), ofNat(8, 5)) { refl }\n\
         theorem w8_high_bit(): ripple_add(8, ofNat(8, 127), one(8)) = bitvec::add(8, ofNat(8, 127), one(8)) { refl }\n\
         theorem w8_neg_offset(): ripple_add(8, ofNat(8, 100), ofNat(8, 248)) = bitvec::sub(8, ofNat(8, 100), ofNat(8, 8)) { refl }\n\
         theorem w8_mixed(): ripple_add(8, ofNat(8, 0x5A), ofNat(8, 0xA7)) = ofNat(8, 1) { refl }\n\
         theorem w8_neg(): ripple_neg(8, ofNat(8, 1)) = bitvec::neg(8, ofNat(8, 1)) { refl }\n\
         theorem w1_wrap_value(): toNat(1, ripple_add(1, one(1), one(1))) = 0 { refl }\n\
         theorem w8_wrap_value(): toNat(8, ripple_add(8, ofNat(8, 250), ofNat(8, 9))) = 3 { refl }\n\
         theorem w8_underflow_value(): toNat(8, ripple_sub(8, ofNat(8, 3), ofNat(8, 5))) = 254 { refl }\n\
         theorem w8_neg_offset_value(): toNat(8, ripple_add(8, ofNat(8, 100), ofNat(8, 248))) = 92 { refl }\n\
         theorem w8_signed(): toInt(8, ripple_sub(8, zero(8), ofNat(8, 5))) = NegSucc(4) { refl }\n",
    );
    ok(&src);

    for (name, wrong) in [
        ("flipped_bit", format!(
            "ripple_add(64, {}, {}) = {}",
            of(ADDRESS), of(MINUS_EIGHT), bit_vector_literal_at(64, (ADDRESS - 8) ^ (1 << 40)))),
        ("off_by_one", format!("ripple_sub(64, zero(64), one(64)) = {}", of(M - 2))),
        ("transported_wrong", format!(
            "bitvec::add(64, {a}, {b}) = {r} {{ add_eq_of_ripple_add(64, {a}, {b}, {r}, refl) }}",
            a = of(ADDRESS), b = of(MINUS_EIGHT), r = of((ADDRESS - 8) ^ (1 << 40)))),
        ("small_width", "ripple_add(8, ofNat(8, 250), ofNat(8, 9)) = ofNat(8, 4)".to_string()),
    ] {
        let src = if wrong.contains('{') {
            format!("theorem {name}(): {wrong}")
        } else {
            format!("theorem {name}(): {wrong} {{ refl }}")
        };
        let msg = run(&src).expect_err("a wrong result must be refused");
        assert!(msg.contains("NotConvertible"), "{name}: {msg}");
    }

    // Working-set evidence (docs/benchmarking.md): the counters separate width
    // from magnitude — the same width-64 ripple at a small and at a huge
    // operand, the width-32 ripple, and the old `add` at a count of eight.
    if std::env::var_os("HEATHER_VALUE_METRICS").is_some() {
        for (label, probe) in [
            ("ripple_add w64 operand 2^10", format!("ripple_add(64, {}, {}) = {}", of(ADDRESS), of(1024), of(ADDRESS + 1024))),
            ("ripple_add w64 operand 2^63", format!("ripple_add(64, {}, {}) = {}", of(ADDRESS), of(HIGH), of(ADDRESS + HIGH))),
            ("ripple_sub w64 operand -8", format!("ripple_sub(64, {}, {}) = {}", of(ADDRESS), of(MINUS_EIGHT), of(ADDRESS + 8))),
            ("ripple_add w32 operand 2^31", "ripple_add(32, ofNat(32, 2147479552), ofNat(32, 2147483648)) = ofNat(32, 4294963200)".to_string()),
            ("old add w64 count 8", format!("bitvec::add(64, {}, {}) = {}", of(ADDRESS), of(8), of(ADDRESS + 8))),
        ] {
            eprintln!("bitvec probe: {label}");
            ok(&format!("import nat;\ntheorem t(): {probe} {{ refl }}\n"));
        }
    }
}

/// Structural consumers over a computed width-64 producer. Until 2026-09-07
/// every one of these exhausted fuel or gigabytes while the same consumer
/// over an `ofNat` literal was cheap: conversion drove the δ-unfoldings
/// from outside one definition at a time, and each step replayed the
/// consumer's whole stuck spine over the producer (cubic in the width, then
/// exponential once the replays' throwaway memos evicted the shared ones).
/// A side with no defined head to meet now unfolds transparently inside the
/// machine (`Eval::delta_whnf`), and these check in seconds under the
/// ordinary rail (issues/bitvec-closed-reduction-cost.md). A *negative*
/// `toInt` at width 64 is `int::sub(OfNat(2^63 - 5), OfNat(2^64))`, which
/// was unary magnitude arithmetic until `int::add` became the payload
/// operations by sign case (issues/int-arithmetic-over-nat-primitives.md):
/// now one synchronous `subNatNat` descent the kernel cancels in a step.
/// `signed_overflow_add` is stated with a count-one right operand: it goes
/// through the old `add`, whose `iterate_increment` over a `2^63` count is
/// the excessive unary computation the resource-diagnostic clause of
/// issues/bitvec-closed-reduction-cost.md still owns (a stack overflow, not
/// `OutOfFuel`).
#[test]
fn consumers_over_computed_machine_width_producers_cost_the_width() {
    const M: u128 = 1 << 64;
    const HIGH: u128 = 1 << 63;
    const ADDRESS: u128 = 0x0000_7FFF_FFFF_F000;
    let of = |v: u128| format!("ofNat(64, {v})");
    let high_sum = format!("ripple_add(64, {}, {})", of(5), of(HIGH - 5));
    let src = format!(
        "import nat;\n\
         theorem sign_of_sum(): sign_bit(64, {high_sum}) = True {{ refl }}\n\
         theorem value_of_sum(): toNat(64, {high_sum}) = {HIGH} {{ refl }}\n\
         theorem signed_value_of_sum(): toInt(64, ripple_add(64, {a}, {b})) = OfNat({}) {{ refl }}\n\
         theorem signed_value_of_difference(): toInt(64, ripple_sub(64, zero(64), {c})) = NegSucc(99) {{ refl }}\n\
         theorem signed_value_of_high_sum(): toInt(64, {high_sum}) = NegSucc({}) {{ refl }}\n\
         theorem complement_of_sum(): complement(64, {high_sum}) = {} {{ refl }}\n\
         theorem sum_of_sums(): ripple_add(64, ripple_add(64, {a}, {b}), ripple_sub(64, {c}, one(64))) = {} {{ refl }}\n\
         theorem carry_of_sum(): carry_add_bit(64, ripple_add(64, all_ones(64), zero(64)), one(64)) = True {{ refl }}\n\
         theorem borrow_of_difference(): borrow_sub_bit(64, ripple_sub(64, {a}, {a}), one(64)) = True {{ refl }}\n\
         theorem overflow_of_difference(): signed_overflow_add(64, ripple_sub(64, {h}, one(64)), one(64)) = True {{ refl }}\n\
         theorem sum_below_its_negation(): unsigned_lt_bit(64, {a}, ripple_neg(64, {a})) = True {{ refl }}\n\
         theorem boundary_unsigned(): unsigned_lt_bit(64, zero(64), {h}) = True {{ refl }}\n\
         theorem boundary_signed(): signed_lt_bit(64, {h}, zero(64)) = True {{ refl }}\n\
         theorem value_of_old_add(): toNat(64, bitvec::add(64, {a}, ofNat(64, 8))) = {} {{ refl }}\n",
        ADDRESS + 1024,
        HIGH - 1,
        bit_vector_literal_at(64, (M - 1) ^ HIGH),
        of(ADDRESS + 1024 + 99),
        ADDRESS + 8,
        a = of(ADDRESS), b = of(1024), c = of(100), h = of(HIGH),
    );
    ok(&src);

    for (name, wrong) in [
        ("sign_of_sum", format!("sign_bit(64, {high_sum}) = False")),
        ("value_of_sum", format!("toNat(64, {high_sum}) = {}", HIGH + 1)),
        ("sum_of_sums", format!(
            "ripple_add(64, ripple_add(64, {a}, {b}), ripple_sub(64, {c}, one(64))) = {}",
            of(ADDRESS + 1024 + 100), a = of(ADDRESS), b = of(1024), c = of(100))),
        ("boundary_unsigned", format!("unsigned_lt_bit(64, {}, zero(64)) = True", of(HIGH))),
    ] {
        let msg = run(&format!("import nat;\ntheorem {name}(): {wrong} {{ refl }}"))
            .expect_err("a wrong consumer result must be refused");
        assert!(msg.contains("NotConvertible"), "{name}: {msg}");
    }
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
