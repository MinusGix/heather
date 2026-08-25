//! Public fixed-width bitvectors and their generic arithmetic/bit-operation
//! kit. The carrier is exercised at closed and open widths; closed numerals
//! alone would miss an index or motive that was accidentally specialized.

use heather_elab::{ElabError, Elaborator};
use std::sync::Mutex;

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
    for (name, src) in [
        ("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION),
        ("pair", PAIR), ("list", LIST), ("algebra", ALGEBRA), ("int", INT),
        ("bitvec", BITVEC),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(format!("{name}: {}", err.render(src)));
        }
    }
    if !extra.is_empty() {
        let src = format!("import bitvec;\nimport bool;\nimport logic;\n{extra}");
        if let Err(err) = e.elab_module_source("probe", &src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
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
fn bitwise_shape_and_conversion_compute() {
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
"#);
    bad("theorem wrong(): toNat(3, from_bits(3, [True, False, True])) = 6 { refl }");
}

#[test]
fn arithmetic_is_modulo_the_width_and_reports_alu_conditions() {
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
"#);
    bad("theorem no_carry(): carry_add(4, ofNat(4, 1), ofNat(4, 1)) { trivial }");
}

#[test]
fn slicing_extension_concat_and_shifts_compute() {
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
"#);
    bad("theorem fake(n: Nat, x: BitVec(n)): bxor(n, x, x) = zero(n) { refl }");
}
