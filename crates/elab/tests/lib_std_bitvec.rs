//! Public fixed-width bitvectors and their generic arithmetic/bit-operation
//! kit. The carrier is exercised at closed and open widths; closed numerals
//! alone would miss an index or motive that was accidentally specialized.
//!
//! The fast lane keeps the ungated module check, the width/open-carrier
//! probe, and the open law kit. The three closed computational cross-products
//! are stable exhaustive acceptance and use the `slow_acceptance_` prefix.

use heather_elab::{ElabError, Elaborator, SemanticImage};
use std::sync::{Mutex, OnceLock};

use crate::support;

static ELAB_LOCK: Mutex<()> = Mutex::new(());

static BASE: OnceLock<SemanticImage> = OnceLock::new();

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const BITVEC: &str = include_str!("../../../lib/std/bitvec.hthr");

/// The first nine modules of `semantic_x86_warmup.rs`'s list, in its order,
/// so the on-disk image keys this file reads are the ones the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION),
    ("pair", PAIR), ("list", LIST), ("algebra", ALGEBRA), ("int", INT),
    ("bitvec", BITVEC),
];

fn run(extra: &str) -> Result<(), String> {
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    if extra.is_empty() {
        // The ungated front-to-back check of the module itself: deliberately
        // source-only, so the full suite still checks this exact prefix
        // against the real kernel once.
        let mut e = Elaborator::with_prelude().expect("prelude");
        for &(name, src) in MODULES {
            if let Err(err) = e.elab_module_source(name, src) {
                return Err(format!("{name}: {}", err.render(src)));
            }
        }
        return Ok(());
    }
    // Every probe forks a fresh elaborator from one kernel-checked semantic
    // image of the prefix instead of re-elaborating nine modules per case.
    let mut e = BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator();
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
    Ok(())
}

fn ok(src: &str) { run(src).unwrap_or_else(|e| panic!("expected this to check: {e}")); }

fn bad(src: &str) {
    assert!(run(src).is_err(), "expected this to be refused:\n{src}");
}

#[test]
fn the_bitvec_module_checks() { ok(""); }

/// Use the public record and its generated type code too: a synthetic Vec
/// alone misses the cost of unfolding library result types during probing.
#[test]
fn valuation_lookup_dispatch_cost_does_not_follow_result_width() {
    use heather_elab::stats;
    let _guard = ELAB_LOCK.lock().unwrap_or_else(|p| p.into_inner());
    let mut e = BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator();
    e.set_kernel_workers(1);
    let mut body = "values(width, 201)".to_string();
    for i in (0..=200).rev() {
        let id = if i == 0 { "id".to_string() } else { format!("id_{i}") };
        body = format!("match {id} {{ Zero => values(width, {i}), Succ(id_{}) => {body} }}", i + 1);
    }
    let setup = format!("import bitvec;\nfn lookup(values: (width: Nat) -> Nat -> BitVec(width)) -> (width: Nat) -> Nat -> BitVec(width) {{ λ width id => {body} }}");
    e.elab_module_source("lookup_setup", &setup).unwrap_or_else(|err| panic!("{}", err.render(&setup)));
    let mut source = String::from("import bitvec; import lookup_setup;\n");
    for width in ["1", "8", "64", "w"] {
        let open = if width == "w" { "w: Nat, " } else { "" };
        for id in [0, 8, 51, 200, 201, 250] {
            source.push_str(&format!("theorem at_{width}_{id}({open}values: (width: Nat) -> Nat -> BitVec(width)): lookup(values)({width}, {id}) = values({width}, {}) {{ refl }}\n", id.min(201)));
        }
    }
    source.push_str("theorem successor(values: (width: Nat) -> Nat -> BitVec(width)): lookup(values)(64, Succ(Succ(49))) = values(64, 51) { refl }\n");
    e.enable_item_timings();
    e.elab_module_source("lookup_probe", &source).unwrap_or_else(|err| panic!("{}", err.render(&source)));
    let rows = e.take_item_timings();
    stats::disable();
    for width in ["1", "8", "64", "w"] {
        let count = |id| rows.iter().find(|r| r.item.rsplit("::").next() == Some(format!("at_{width}_{id}").as_str())).expect("measured lookup").kernel.eval_steps;
        let counts: Vec<_> = [0, 8, 51, 200, 201, 250].into_iter().map(count).collect();
        eprintln!("BitVec lookup width {width}, ids 0/8/51/200/201/250: {counts:?}");
        for id in [8, 51, 200] {
            assert_eq!(count(id) - count(0), 2 * id as u64,
                "result type preparation leaked into case dispatch: {counts:?}");
        }
        assert_eq!(count(201), count(250), "the default arm must stop dispatch");
    }
    let refusal = "import bitvec; import lookup_setup; theorem wrong(values: (width: Nat) -> Nat -> BitVec(width)): lookup(values)(64, 51) = values(64, 50) { refl }";
    assert!(e.elab_module_source("lookup_wrong", refusal).is_err(), "wrong port accepted");
}

/// `from_bits(64, [...])` spelling `value`, least-significant bit first — an
/// independent statement of the bits `ofNat` must produce.
fn bit_vector_literal(value: u64) -> String {
    let bits: Vec<&str> = (0..64)
        .map(|i| if (value >> i) & 1 == 1 { "True" } else { "False" })
        .collect();
    format!("@BitVec::from_bits(64, [{}])", bits.join(", "))
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
            "theorem {name}_bits(): @BitVec::ofNat(64, {value}) = {} {{ refl }}\n\
             theorem {name}_round_trip(): @BitVec::toNat(64, @BitVec::ofNat(64, {value})) = {value} {{ refl }}\n",
            bit_vector_literal(value),
        ));
    }
    // Truncation modulo the width survives the top-down reading.
    src.push_str(
        "theorem truncates(): @BitVec::ofNat(8, 261) = @BitVec::ofNat(8, 5) { refl }\n\
         theorem truncates_to_nat(): @BitVec::toNat(8, @BitVec::ofNat(8, 261)) = 5 { refl }\n\
         theorem powers_are_one_run(): nat::Nat::pow(2, 63) = 9223372036854775808 { refl }\n\
         theorem doubling_is_one_run(): nat::Nat::twice(9223372036854775807) = 18446744073709551614 { refl }\n\
         theorem run_scrutinee_chain(): nat::Nat::mul(2, 65536) = 131072 { refl }\n\
         theorem hex_spelling(): @BitVec::ofNat(64, 0x0123_4567_89AB_CDEF) = @BitVec::ofNat(64, 81985529216486895) { refl }\n\
         theorem hex_high_bit(): @BitVec::toNat(64, @BitVec::ofNat(64, 0x8000_0000_0000_0001)) = 9223372036854775809 { refl }\n\
         theorem doubling_chain_under_a_consumer(): nat::Nat::leb(nat::Nat::pow(2, 40), 1099511627776) = True { refl }\n",
    );
    ok(&src);

    for (value, flipped) in [(ASYMMETRIC, 0), (HIGH_BIT, 63), (u64::MAX, 31)] {
        let src = format!(
            "theorem wrong(): @BitVec::ofNat(64, {value}) = {} {{ refl }}",
            bit_vector_literal(value ^ (1 << flipped)),
        );
        let msg = run(&src).expect_err("a flipped bit must be refused");
        assert!(msg.contains("NotConvertible"), "{msg}");
    }
    let msg = run("theorem wrong(): @BitVec::toNat(64, @BitVec::ofNat(64, 81985529216486895)) = 81985529216486896 { refl }")
        .expect_err("an off-by-one round trip must be refused");
    assert!(msg.contains("NotConvertible"), "{msg}");
    // A radix spelling is the same literal: one hex digit off is refused.
    let msg = run("theorem wrong(): @BitVec::ofNat(64, 0x0123_4567_89AB_CDEE) = @BitVec::ofNat(64, 81985529216486895) { refl }")
        .expect_err("a hex digit off must be refused");
    assert!(msg.contains("NotConvertible"), "{msg}");
}

/// `ofNat` where its consumers meet it. The rails above check the definition
/// against a written-out vector; these check that the *bitwise and arithmetic*
/// operations still see what they saw, and vary the two axes a respelling of a
/// recursion loses first (`docs/testing-generated-terms.md`): a **neutral**
/// argument, where the recursion is on the width and the low bit is whatever
/// `odd_bit` is stuck at, and a **checking** position — the fold in the type a
/// proof is checked against, not only in a value being computed.
#[test]
fn of_nat_meets_its_consumers() {
    // No `import nat`: `add` is declared in both modules, and this file's
    // subject is `bitvec`'s.
    ok(r#"
theorem xor_of_two(): @BitVec::bxor(64, @BitVec::ofNat(64, 0x0123_4567_89AB_CDEF), @BitVec::ofNat(64, 0xFFFF_FFFF_FFFF_FFFF))
      = @BitVec::ofNat(64, 0xFEDC_BA98_7654_3210) { refl }
theorem add_of_two(): @BitVec::add(8, @BitVec::ofNat(8, 200), @BitVec::ofNat(8, 100)) = @BitVec::ofNat(8, 44) { refl }
theorem against_a_literal():
    @BitVec::ofNat(8, 0xC0) = @BitVec::from_bits(8, [False, False, False, False, False, False, True, True]) { refl }
theorem into_nat(): @BitVec::toNat(8, @BitVec::ofNat(8, 0xC0)) = 192 { refl }
// A neutral argument: the width still drives the recursion, so the low bit
// reduces to the argument's parity with nothing closed anywhere.
theorem open_low_bit(x: Nat): @BitVec::head_bit(7, @BitVec::ofNat(8, Succ(Succ(x)))) = BitVec::odd_bit(x) { refl }
"#);
    // The negative control at the consumer: one bit off is a conversion
    // failure and not exhausted fuel.
    let msg = run("theorem wrong(): @BitVec::bxor(64, @BitVec::ofNat(64, 1), @BitVec::ofNat(64, 0)) = @BitVec::ofNat(64, 3) { refl }")
        .expect_err("a differing word must be refused");
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn widths_include_zero_machine_sizes_and_a_neutral() {
    ok(r#"
fn w0() -> BitVec(0) { @BitVec::zero(0) }
fn w1() -> BitVec(1) { @BitVec::one(1) }
fn w8() -> BitVec(8) { @BitVec::zero(8) }
fn w16() -> BitVec(16) { @BitVec::all_ones(16) }
fn w32() -> BitVec(32) { @BitVec::complement(32, @BitVec::zero(32)) }
fn w64() -> BitVec(64) { @BitVec::shift_left(64, @BitVec::one(64), 63) }
fn neutral(n: Nat, x, y: BitVec(n)) -> BitVec(n) {
    @BitVec::bxor(n, @BitVec::add(n, x, y), @BitVec::shift_right(n, @BitVec::band(n, x, y), n))
}
theorem z0(): w0() = @BitVec::from_bits(0, []) { refl }
theorem z1(): @BitVec::toNat(1, w1()) = 1 { refl }
"#);
}

#[test]
fn slow_acceptance_bitwise_shape_and_conversion_compute() {
    ok(r#"
fn five() -> BitVec(3) { @BitVec::from_bits(3, [True, False, True]) }
theorem value(): @BitVec::toNat(3, five()) = 5 { refl }
theorem not5(): @BitVec::complement(3, five()) = @BitVec::from_bits(3, [False, True, False]) { refl }
theorem and5(): @BitVec::band(3, five(), @BitVec::from_bits(3, [True, True, False])) =
                @BitVec::from_bits(3, [True, False, False]) { refl }
theorem or5(): @BitVec::bor(3, five(), @BitVec::from_bits(3, [False, True, False])) =
               @BitVec::from_bits(3, [True, True, True]) { refl }
theorem xor5(): @BitVec::bxor(3, five(), @BitVec::from_bits(3, [True, True, False])) =
                @BitVec::from_bits(3, [False, True, True]) { refl }
theorem wraps_construct(): @BitVec::toNat(8, @BitVec::ofNat(8, 300)) = 44 { refl }
theorem signed_minus_one(): @BitVec::toInt(4, @BitVec::ofNat(4, 15)) = NegSucc(0) { refl }
fn equal_byte(a, b: BitVec(8)) -> Bool {
    match @bitvec::BitVec::eq_dec(8, a, b) { Inl(_) => True, Inr(_) => False }
}
theorem byte_eq_yes(): equal_byte(@BitVec::ofNat(8, 137), @BitVec::ofNat(8, 137)) = True { refl }
theorem byte_eq_no(): equal_byte(@BitVec::ofNat(8, 137), @BitVec::ofNat(8, 139)) = False { refl }
"#);
    bad("theorem wrong(): @BitVec::toNat(3, @BitVec::from_bits(3, [True, False, True])) = 6 { refl }");
}

#[test]
fn slow_acceptance_arithmetic_is_modulo_the_width_and_reports_alu_conditions() {
    if std::env::var_os("HEATHER_VALUE_METRICS").is_some() {
        ok(r#"
theorem carry_bit_machine_width_only():
    @BitVec::carry_add_bit(64, @BitVec::all_ones(64), @BitVec::one(64)) = True { refl }
"#);
    }
    ok(r#"
theorem add_wrap(): @BitVec::toNat(4, @BitVec::add(4, @BitVec::ofNat(4, 14), @BitVec::ofNat(4, 3))) = 1 { refl }
theorem sub_wrap(): @BitVec::toNat(4, @BitVec::sub(4, @BitVec::ofNat(4, 3), @BitVec::ofNat(4, 5))) = 14 { refl }
theorem neg_wrap(): @BitVec::toNat(4, @BitVec::neg(4, @BitVec::ofNat(4, 1))) = 15 { refl }
theorem mul_wrap(): @BitVec::toNat(4, @BitVec::mul(4, @BitVec::ofNat(4, 4), @BitVec::ofNat(4, 5))) = 4 { refl }
theorem carry(): @BitVec::carry_add(4, @BitVec::ofNat(4, 14), @BitVec::ofNat(4, 3)) { trivial }
theorem borrow(): @BitVec::borrow_sub(4, @BitVec::ofNat(4, 3), @BitVec::ofNat(4, 5)) { trivial }
theorem ov_add(): @BitVec::signed_overflow_add(4, @BitVec::ofNat(4, 7), @BitVec::ofNat(4, 1)) = True { refl }
theorem ov_sub(): @BitVec::signed_overflow_sub(4, @BitVec::ofNat(4, 8), @BitVec::ofNat(4, 1)) = True { refl }
theorem width_zero_add(): @BitVec::add(0, @BitVec::zero(0), @BitVec::zero(0)) = @BitVec::zero(0) { refl }
theorem carry_bit_yes(): @BitVec::carry_add_bit(4, @BitVec::ofNat(4, 14), @BitVec::ofNat(4, 3)) = True { refl }
theorem carry_bit_no(): @BitVec::carry_add_bit(4, @BitVec::ofNat(4, 1), @BitVec::ofNat(4, 1)) = False { refl }
theorem borrow_bit_yes(): @BitVec::borrow_sub_bit(4, @BitVec::ofNat(4, 3), @BitVec::ofNat(4, 5)) = True { refl }
theorem borrow_bit_no(): @BitVec::borrow_sub_bit(4, @BitVec::ofNat(4, 5), @BitVec::ofNat(4, 3)) = False { refl }
theorem borrow_bit_machine_width():
    @BitVec::borrow_sub_bit(64, @BitVec::zero(64), @BitVec::one(64)) = True { refl }
theorem carry_bit_machine_width():
    @BitVec::carry_add_bit(64, @BitVec::all_ones(64), @BitVec::one(64)) = True { refl }
"#);
    bad("theorem no_carry(): @BitVec::carry_add(4, @BitVec::ofNat(4, 1), @BitVec::ofNat(4, 1)) { trivial }");
}

#[test]
fn slow_acceptance_slicing_extension_concat_and_shifts_compute() {
    ok(r#"
fn lo() -> BitVec(3) { @BitVec::from_bits(3, [True, False, True]) }
fn hi() -> BitVec(2) { @BitVec::from_bits(2, [False, True]) }
theorem cat(): @BitVec::concat(3, 2, lo(), hi()) =
               @BitVec::from_bits(5, [True, False, True, False, True]) { refl }
theorem cut(): (@BitVec::concat(3, 2, lo(), hi())).slice(1, 3, 1) =
               @BitVec::from_bits(3, [False, True, False]) { refl }
theorem zext(): @BitVec::zero_extend(3, 2, lo()) =
                @BitVec::from_bits(5, [True, False, True, False, False]) { refl }
theorem sext(): @BitVec::sign_extend(2, 2, lo()) =
                @BitVec::from_bits(5, [True, False, True, True, True]) { refl }
theorem shl(): @BitVec::shift_left(4, @BitVec::ofNat(4, 3), 2) = @BitVec::ofNat(4, 12) { refl }
theorem shr(): @BitVec::shift_right(4, @BitVec::ofNat(4, 12), 2) = @BitVec::ofNat(4, 3) { refl }
theorem ashr(): @BitVec::arithmetic_shift_right(4, @BitVec::ofNat(4, 12), 2) = @BitVec::ofNat(4, 15) { refl }
"#);
}

#[test]
fn laws_hold_at_open_values_and_widths() {
    ok(r#"
theorem xself(n: Nat, x: BitVec(n)): @BitVec::bxor(n, x, x) = @BitVec::zero(n) { BitVec::xor_self(n, x) }
theorem add_is_commutative(n: Nat, x, y: BitVec(n)): @BitVec::add(n, x, y) = @BitVec::add(n, y, x) {
    BitVec::add_comm(n, x, y)
}
theorem cancel(n: Nat, x, y: BitVec(n)): @BitVec::sub(n, @BitVec::add(n, x, y), y) = x {
    BitVec::add_sub_cancel(n, x, y)
}
theorem updated(n: Nat, x: BitVec(n), i: Fin(n), b: Bool):
    @BitVec::get(n, @BitVec::set(n, x, i, b), i) = b { BitVec::get_set_same(n, x, i, b) }
theorem low(n, m: Nat, x: BitVec(n), y: BitVec(m)):
    (@BitVec::concat(n, m, x, y)).take_low(n, m) = x { BitVec::split_concat_low(n, m, x, y) }
theorem high(n, m: Nat, x: BitVec(n), y: BitVec(m)):
    (@BitVec::concat(n, m, x, y)).drop_low(n, m) = y { BitVec::split_concat_high(n, m, x, y) }
theorem zround(n, m: Nat, x: BitVec(n)):
    (@BitVec::zero_extend(n, m, x)).truncate(n, m) = x { BitVec::truncate_zero_extend(n, m, x) }
theorem sround(n, m: Nat, x: BitVec(Succ(n))):
    (@BitVec::sign_extend(n, m, x)).truncate(Succ(n), m) = x { BitVec::truncate_sign_extend(n, m, x) }
theorem ext(n: Nat, x, y: BitVec(n), at: (i: Fin(n)) -> @BitVec::get(n, x, i) = @BitVec::get(n, y, i)):
    x = y { BitVec::extensionality(n, x, y, at) }
theorem equality_is_decidable(n: Nat, x, y: BitVec(n)): x = y ∨ x ≠ y {
    @bitvec::BitVec::eq_dec(n, x, y)
}
theorem value_round_trip(n: Nat, x: BitVec(n)): @BitVec::ofNat(n, @BitVec::toNat(n, x)) = x { BitVec::ofNat_toNat(n, x) }

theorem carry_equiv(n: Nat, x, y: BitVec(n)):
    (@BitVec::carry_add_bit(n, x, y) = True) ↔ @BitVec::carry_add(n, x, y)
{ BitVec::carry_add_bit_true_iff(n, x, y) }

theorem carry_forward(n: Nat, x, y: BitVec(n),
    h: @BitVec::carry_add_bit(n, x, y) = True): @BitVec::carry_add(n, x, y)
{ BitVec::carry_add_of_bit_true(n, x, y, h) }

theorem carry_backward64(x, y: BitVec(64), h: @BitVec::carry_add(64, x, y)):
    @BitVec::carry_add_bit(64, x, y) = True
{ BitVec::carry_add_bit_of_carry(64, x, y, h) }

theorem borrow_equiv(n: Nat, x, y: BitVec(n)):
    (@BitVec::borrow_sub_bit(n, x, y) = True) ↔ @BitVec::borrow_sub(n, x, y)
{ BitVec::borrow_sub_bit_true_iff(n, x, y) }

theorem borrow_forward(n: Nat, x, y: BitVec(n),
    h: @BitVec::borrow_sub_bit(n, x, y) = True): @BitVec::borrow_sub(n, x, y)
{ BitVec::borrow_sub_of_bit_true(n, x, y, h) }

theorem borrow_backward64(x, y: BitVec(64), h: @BitVec::borrow_sub(64, x, y)):
    @BitVec::borrow_sub_bit(64, x, y) = True
{ BitVec::borrow_sub_bit_of_borrow(64, x, y, h) }
"#);
    bad("theorem fake(n: Nat, x: BitVec(n)): @BitVec::bxor(n, x, x) = @BitVec::zero(n) { refl }");
    // The section is not `refl` at an open vector.
    bad("theorem fake(n: Nat, x: BitVec(n)): @BitVec::ofNat(n, @BitVec::toNat(n, x)) = x { refl }");
    // The value's bound and the number's round trip below it; `<` is `nat`'s,
    // so these import it (nothing here says `add`).
    ok(r#"
import nat;
theorem value_bounded(n: Nat, x: BitVec(n)): @BitVec::toNat(n, x) < nat::Nat::pow(2, n) { BitVec::toNat_lt_pow(n, x) }
theorem number_round_trip(n, k: Nat, h: k < nat::Nat::pow(2, n)): @BitVec::toNat(n, @BitVec::ofNat(n, k)) = k {
    BitVec::toNat_ofNat(n, k, h)
}
"#);
    bad("import nat;\ntheorem fake(n: Nat, x: BitVec(n)): toNat(n, x) < nat::Nat::pow(2, n) { trivial }");
}

#[test]
fn add_commutativity_covers_width_and_carry_boundaries() {
    ok(r#"
theorem width_zero(): @BitVec::add(0, @BitVec::zero(0), @BitVec::zero(0)) = @BitVec::add(0, @BitVec::zero(0), @BitVec::zero(0)) {
    BitVec::add_comm(0, @BitVec::zero(0), @BitVec::zero(0))
}
theorem width_one(): @BitVec::add(1, @BitVec::zero(1), @BitVec::one(1)) = @BitVec::add(1, @BitVec::one(1), @BitVec::zero(1)) {
    BitVec::add_comm(1, @BitVec::zero(1), @BitVec::one(1))
}
theorem machine_width(left, right: BitVec(64)):
    @BitVec::add(64, left, right) = @BitVec::add(64, right, left) {
    BitVec::add_comm(64, left, right)
}
theorem carry_out():
    @BitVec::add(8, @BitVec::all_ones(8), @BitVec::one(8)) = @BitVec::add(8, @BitVec::one(8), @BitVec::all_ones(8)) {
    BitVec::add_comm(8, @BitVec::all_ones(8), @BitVec::one(8))
}
theorem unequal_high_bits():
    @BitVec::add(8, @BitVec::ofNat(8, 128), @BitVec::ofNat(8, 3)) =
    @BitVec::add(8, @BitVec::ofNat(8, 3), @BitVec::ofNat(8, 128)) {
    BitVec::add_comm(8, @BitVec::ofNat(8, 128), @BitVec::ofNat(8, 3))
}
"#);
    bad(r#"
theorem commutativity_is_not_absorption(n: Nat, left, right: BitVec(n)):
    @BitVec::add(n, left, right) = left {
    BitVec::add_comm(n, left, right)
}
"#);
}

/// `from_bits(width, [...])` spelling the low `width` bits of `value`,
/// least-significant first.
fn bit_vector_literal_at(width: u32, value: u128) -> String {
    let bits: Vec<&str> = (0..width)
        .map(|i| if (value >> i) & 1 == 1 { "True" } else { "False" })
        .collect();
    format!("@BitVec::from_bits({width}, [{}])", bits.join(", "))
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
    @BitVec::ripple_add(n, x, y) = @bitvec::BitVec::add(n, x, y) { BitVec::ripple_add_eq_add(n, x, y) }
theorem ripple_sub_is_sub(n: Nat, x, y: BitVec(n)):
    @BitVec::ripple_sub(n, x, y) = @bitvec::BitVec::sub(n, x, y) { BitVec::ripple_sub_eq_sub(n, x, y) }
theorem ripple_neg_is_neg(n: Nat, x: BitVec(n)):
    @BitVec::ripple_neg(n, x) = @bitvec::BitVec::neg(n, x) { BitVec::ripple_neg_eq_neg(n, x) }
theorem iter_add_is_add(n: Nat, x, y: BitVec(n)):
    @BitVec::iter_add(n, x, y) = @bitvec::BitVec::add(n, x, y) { BitVec::iter_add_eq_add(n, x, y) }
theorem iter_sub_is_sub(n: Nat, x, y: BitVec(n)):
    @BitVec::iter_sub(n, x, y) = @bitvec::BitVec::sub(n, x, y) { BitVec::iter_sub_eq_sub(n, x, y) }
theorem iter_neg_is_neg(n: Nat, x: BitVec(n)):
    @BitVec::iter_neg(n, x) = @bitvec::BitVec::neg(n, x) { BitVec::iter_neg_eq_neg(n, x) }
theorem iter_transport_forward(n: Nat, x, y, r: BitVec(n), h: @BitVec::iter_add(n, x, y) = r):
    @bitvec::BitVec::add(n, x, y) = r { BitVec::add_eq_of_iter_add(n, x, y, r, h) }
theorem iter_transport_backward(n: Nat, x, y, r: BitVec(n), h: @bitvec::BitVec::sub(n, x, y) = r):
    @BitVec::iter_sub(n, x, y) = r { BitVec::iter_sub_eq_of_sub(n, x, y, r, h) }
theorem iter_transport_neg(n: Nat, x, r: BitVec(n), h: @BitVec::iter_neg(n, x) = r):
    @bitvec::BitVec::neg(n, x) = r { BitVec::neg_eq_of_iter_neg(n, x, r, h) }
theorem zero_offset_is_not_computation(n: Nat, x, y: BitVec(n), h: @BitVec::toNat(n, y) = 0):
    @bitvec::BitVec::add(n, x, y) = x { BitVec::add_of_toNat_zero(n, x, y, h) }
theorem carry_in_meaning(n: Nat, x, y: BitVec(n), c: Bool):
    @BitVec::add_bits(n, x, y, c) = @BitVec::iterate_increment(n, x, @BitVec::toNat(n, y) + Nat::of_bit(c))
{ BitVec::add_bits_spec(n, x, y, c) }
theorem borrow_in_meaning(n: Nat, x, y: BitVec(n), c: Bool):
    @BitVec::sub_bits(n, x, y, c) = @BitVec::iterate_decrement(n, @BitVec::toNat(n, y) + Nat::of_bit(c), x)
{ BitVec::sub_bits_spec(n, x, y, c) }
theorem machine_width_add(x, y: BitVec(64)):
    @BitVec::ripple_add(64, x, y) = @bitvec::BitVec::add(64, x, y) { BitVec::ripple_add_eq_add(64, x, y) }
theorem machine_width_sub(x, y: BitVec(64)):
    @BitVec::ripple_sub(64, x, y) = @bitvec::BitVec::sub(64, x, y) { BitVec::ripple_sub_eq_sub(64, x, y) }
theorem width_zero_carry(x, y: BitVec(0), c: Bool): @BitVec::add_bits(0, x, y, c) = @BitVec::zero(0) { refl }
theorem transport_forward(n: Nat, x, y, r: BitVec(n), h: @BitVec::ripple_add(n, x, y) = r):
    @bitvec::BitVec::add(n, x, y) = r { BitVec::add_eq_of_ripple_add(n, x, y, r, h) }
theorem transport_backward(n: Nat, x, y, r: BitVec(n), h: @bitvec::BitVec::sub(n, x, y) = r):
    @BitVec::ripple_sub(n, x, y) = r { BitVec::ripple_sub_eq_of_sub(n, x, y, r, h) }
theorem transport_neg(n: Nat, x, r: BitVec(n), h: @BitVec::ripple_neg(n, x) = r):
    @bitvec::BitVec::neg(n, x) = r { BitVec::neg_eq_of_ripple_neg(n, x, r, h) }
theorem inherited_comm(n: Nat, x, y: BitVec(n)):
    @BitVec::ripple_add(n, x, y) = @BitVec::ripple_add(n, y, x) { BitVec::ripple_add_comm(n, x, y) }
theorem inherited_cancel(n: Nat, x, y: BitVec(n)):
    @BitVec::ripple_sub(n, @BitVec::ripple_add(n, x, y), y) = x { BitVec::ripple_add_sub_cancel(n, x, y) }
theorem congruence(n: Nat, x, y, z: BitVec(n), p: x = y):
    @BitVec::ripple_add(n, x, z) = @BitVec::ripple_add(n, y, z) { BitVec::cong_ripple_add(n, p, refl) }
theorem consumer_transport(n: Nat, x, y: BitVec(n)):
    @BitVec::sign_bit(n, @BitVec::ripple_add(n, x, y)) = @BitVec::sign_bit(n, @bitvec::BitVec::add(n, x, y))
{ j(BitVec::ripple_add_eq_add(n, x, y), λ z q => @BitVec::sign_bit(n, @BitVec::ripple_add(n, x, y)) = @BitVec::sign_bit(n, z), refl) }
"#);
    bad(r#"
theorem misstated(n: Nat, x, y: BitVec(n)):
    @BitVec::ripple_add(n, x, y) = @bitvec::BitVec::add(n, y, x) { BitVec::ripple_add_eq_add(n, x, y) }
"#);
    let msg = run(r#"
theorem not_by_computation(n: Nat, x, y: BitVec(n)):
    @BitVec::iter_add(n, x, y) = @bitvec::BitVec::add(n, x, y) { refl }
"#)
    .expect_err("the two definitions are not convertible at open operands");
    assert!(msg.contains("NotConvertible"), "{msg}");
    ok(r#"
theorem ripple_is_add_by_definition(n: Nat, x, y: BitVec(n)):
    @BitVec::ripple_add(n, x, y) = @bitvec::BitVec::add(n, x, y) { refl }
"#);
}

/// `add` and `sub` are distinct, and how the kernel says so depends on the
/// width. Both are ripples that agree on every sum bit and differ only in the
/// column carry (`carry_majority` against `borrow_next`), so at width 8 over
/// open operands the difference is found in a few columns and reported as
/// `NotConvertible`, while at width 64 the budget runs out first. That is why
/// the stale-source control in `function_ir_x86.rs` accepts either refusal.
/// Before docs/bitvec-width-bounded-defaults-design.md the two had different
/// heads (`iterate_increment` against `iterate_decrement`) and both widths
/// were immediate.
#[test]
fn add_and_sub_differ() {
    let msg = run("theorem narrow(x, y: BitVec(8)): @bitvec::BitVec::add(8, x, y) = @bitvec::BitVec::sub(8, x, y) { refl }")
        .expect_err("add and sub are not the same operation");
    assert!(msg.contains("NotConvertible"), "{msg}");
    let msg = run("theorem wide(x, y: BitVec(64)): @bitvec::BitVec::add(64, x, y) = @bitvec::BitVec::sub(64, x, y) { refl }")
        .expect_err("add and sub are not the same operation");
    assert!(msg.contains("OutOfFuel") || msg.contains("NotConvertible"), "{msg}");
}

/// The ripple's closed cost is the width, not the operand
/// (issues/bitvec-bounded-add-sub.md): every machine-width case below —
/// wraparound, underflow, the high-bit boundary, mixed bits, and the
/// full-width negative-offset pattern a sign-extended displacement produces —
/// is checked against an independently written bit vector and against the
/// `ofNat` literal, and the canonical `add`/`sub`/`neg` facts are proved by
/// transporting the ripple's `refl` — since
/// [[bitvec-width-bounded-defaults]] those transports are definitional.
/// Small widths compare the ripple with the iterated definitions
/// (`iter_add`/`iter_sub`/`iter_neg`) directly, but only at small counts:
/// `iter_add(8, _, 248)` is 248 increments and already costs gigabytes,
/// which is the very iteration `add` no longer performs. The controls flip one bit or miss by one
/// and must be refused as `NotConvertible`, not as exhausted fuel.
#[test]
fn ripple_add_and_sub_cost_the_width_not_the_magnitude() {
    const M: u128 = 1 << 64;
    const ASYMMETRIC: u128 = 0x0123_4567_89AB_CDEF;
    const REVERSED: u128 = 0xFEDC_BA98_7654_3210;
    const HIGH: u128 = 1 << 63;
    const ADDRESS: u128 = 0x0000_7FFF_FFFF_F000;
    const MINUS_EIGHT: u128 = M - 8;
    let of = |v: u128| format!("@BitVec::ofNat(64, {v})");
    let mut src = String::from("import nat;\n");
    for (name, expr, value) in [
        ("neg_offset_add", format!("@BitVec::ripple_add(64, {}, {})", of(ADDRESS), of(MINUS_EIGHT)), ADDRESS - 8),
        ("neg_offset_sub", format!("@BitVec::ripple_sub(64, {}, {})", of(ADDRESS), of(MINUS_EIGHT)), ADDRESS + 8),
        ("neg_rel32_from_zero", format!("@BitVec::ripple_sub(64, @BitVec::zero(64), {})", of(0x1234)), M - 0x1234),
        ("neg_rel32", format!("@BitVec::ripple_neg(64, {})", of(0x1234)), M - 0x1234),
        ("wrap", "@BitVec::ripple_add(64, @BitVec::all_ones(64), @BitVec::one(64))".to_string(), 0),
        ("underflow", "@BitVec::ripple_sub(64, @BitVec::zero(64), @BitVec::one(64))".to_string(), M - 1),
        ("saturated_pair", "@BitVec::ripple_add(64, @BitVec::all_ones(64), @BitVec::all_ones(64))".to_string(), M - 2),
        ("high_bit_up", format!("@BitVec::ripple_add(64, {}, @BitVec::one(64))", of(HIGH - 1)), HIGH),
        ("high_bit_down", format!("@BitVec::ripple_sub(64, {}, @BitVec::one(64))", of(HIGH)), HIGH - 1),
        ("high_bit_double", format!("@BitVec::ripple_add(64, {}, {})", of(HIGH), of(HIGH)), 0),
        ("mixed_add", format!("@BitVec::ripple_add(64, {}, {})", of(ASYMMETRIC), of(REVERSED)), (ASYMMETRIC + REVERSED) % M),
        ("mixed_sub", format!("@BitVec::ripple_sub(64, {}, {})", of(ASYMMETRIC), of(REVERSED)), (M + ASYMMETRIC - REVERSED) % M),
        ("magnitude_small", format!("@BitVec::ripple_add(64, {}, {})", of(ADDRESS), of(1024)), ADDRESS + 1024),
        ("magnitude_huge", format!("@BitVec::ripple_add(64, {}, {})", of(ADDRESS), of(HIGH)), ADDRESS + HIGH),
    ] {
        src.push_str(&format!(
            "theorem {name}(): {expr} = {} {{ refl }}\n\
             theorem {name}_of_nat(): {expr} = {} {{ refl }}\n",
            bit_vector_literal_at(64, value), of(value),
        ));
    }
    src.push_str(&format!(
        "theorem canonical_add(): @bitvec::BitVec::add(64, {a}, {b}) = {r} {{ BitVec::add_eq_of_ripple_add(64, {a}, {b}, {r}, refl) }}\n\
         theorem canonical_sub(): @bitvec::BitVec::sub(64, {a}, {b}) = {s} {{ BitVec::sub_eq_of_ripple_sub(64, {a}, {b}, {s}, refl) }}\n\
         theorem canonical_neg(): @bitvec::BitVec::neg(64, {c}) = {n} {{ BitVec::neg_eq_of_ripple_neg(64, {c}, {n}, refl) }}\n\
         theorem neg_offset_is_old_sub(): @BitVec::ripple_add(64, {a}, {b}) = @bitvec::BitVec::iter_sub(64, {a}, {e}) {{ refl }}\n\
         theorem minus_one_is_old_sub(): @BitVec::ripple_add(64, {a}, {m}) = @bitvec::BitVec::iter_sub(64, {a}, @BitVec::one(64)) {{ refl }}\n\
         theorem sub_minus_one_is_old_add(): @BitVec::ripple_sub(64, {a}, {m}) = @bitvec::BitVec::iter_add(64, {a}, @BitVec::one(64)) {{ refl }}\n",
        a = of(ADDRESS), b = of(MINUS_EIGHT), r = of(ADDRESS - 8), s = of(ADDRESS + 8),
        c = of(0x1234), n = of(M - 0x1234), e = of(8), m = of(M - 1),
    ));
    src.push_str(&format!(
        "theorem w32_neg_offset(): @BitVec::ripple_add(32, @BitVec::ofNat(32, 2147479552), @BitVec::ofNat(32, 4294967288)) = @BitVec::ofNat(32, 2147479544) {{ refl }}\n\
         theorem w32_wrap(): @BitVec::ripple_add(32, @BitVec::all_ones(32), @BitVec::one(32)) = @BitVec::zero(32) {{ refl }}\n\
         theorem w32_high(): @BitVec::ripple_sub(32, @BitVec::ofNat(32, 2147483648), @BitVec::one(32)) = {} {{ refl }}\n",
        bit_vector_literal_at(32, (1 << 31) - 1),
    ));
    src.push_str(
        "theorem w0_add(): @BitVec::ripple_add(0, @BitVec::zero(0), @BitVec::zero(0)) = @bitvec::BitVec::iter_add(0, @BitVec::zero(0), @BitVec::zero(0)) { refl }\n\
         theorem w0_sub(): @BitVec::ripple_sub(0, @BitVec::zero(0), @BitVec::zero(0)) = @bitvec::BitVec::iter_sub(0, @BitVec::zero(0), @BitVec::zero(0)) { refl }\n\
         theorem w1_wrap(): @BitVec::ripple_add(1, @BitVec::one(1), @BitVec::one(1)) = @bitvec::BitVec::iter_add(1, @BitVec::one(1), @BitVec::one(1)) { refl }\n\
         theorem w1_underflow(): @BitVec::ripple_sub(1, @BitVec::zero(1), @BitVec::one(1)) = @bitvec::BitVec::iter_sub(1, @BitVec::zero(1), @BitVec::one(1)) { refl }\n\
         theorem w8_wrap(): @BitVec::ripple_add(8, @BitVec::ofNat(8, 250), @BitVec::ofNat(8, 9)) = @bitvec::BitVec::iter_add(8, @BitVec::ofNat(8, 250), @BitVec::ofNat(8, 9)) { refl }\n\
         theorem w8_underflow(): @BitVec::ripple_sub(8, @BitVec::ofNat(8, 3), @BitVec::ofNat(8, 5)) = @bitvec::BitVec::iter_sub(8, @BitVec::ofNat(8, 3), @BitVec::ofNat(8, 5)) { refl }\n\
         theorem w8_high_bit(): @BitVec::ripple_add(8, @BitVec::ofNat(8, 127), @BitVec::one(8)) = @bitvec::BitVec::iter_add(8, @BitVec::ofNat(8, 127), @BitVec::one(8)) { refl }\n\
         theorem w8_neg_offset(): @BitVec::ripple_add(8, @BitVec::ofNat(8, 100), @BitVec::ofNat(8, 248)) = @bitvec::BitVec::iter_sub(8, @BitVec::ofNat(8, 100), @BitVec::ofNat(8, 8)) { refl }\n\
         theorem w8_mixed(): @BitVec::ripple_add(8, @BitVec::ofNat(8, 0x5A), @BitVec::ofNat(8, 0xA7)) = @BitVec::ofNat(8, 1) { refl }\n\
         theorem w8_neg(): @BitVec::ripple_neg(8, @BitVec::ofNat(8, 1)) = @bitvec::BitVec::iter_neg(8, @BitVec::ofNat(8, 1)) { refl }\n\
         theorem w1_wrap_value(): @BitVec::toNat(1, @BitVec::ripple_add(1, @BitVec::one(1), @BitVec::one(1))) = 0 { refl }\n\
         theorem w8_wrap_value(): @BitVec::toNat(8, @BitVec::ripple_add(8, @BitVec::ofNat(8, 250), @BitVec::ofNat(8, 9))) = 3 { refl }\n\
         theorem w8_underflow_value(): @BitVec::toNat(8, @BitVec::ripple_sub(8, @BitVec::ofNat(8, 3), @BitVec::ofNat(8, 5))) = 254 { refl }\n\
         theorem w8_neg_offset_value(): @BitVec::toNat(8, @BitVec::ripple_add(8, @BitVec::ofNat(8, 100), @BitVec::ofNat(8, 248))) = 92 { refl }\n\
         theorem w8_signed(): @BitVec::toInt(8, @BitVec::ripple_sub(8, @BitVec::zero(8), @BitVec::ofNat(8, 5))) = NegSucc(4) { refl }\n",
    );
    ok(&src);

    for (name, wrong) in [
        ("flipped_bit", format!(
            "@BitVec::ripple_add(64, {}, {}) = {}",
            of(ADDRESS), of(MINUS_EIGHT), bit_vector_literal_at(64, (ADDRESS - 8) ^ (1 << 40)))),
        ("off_by_one", format!("@BitVec::ripple_sub(64, @BitVec::zero(64), @BitVec::one(64)) = {}", of(M - 2))),
        ("transported_wrong", format!(
            "@bitvec::BitVec::add(64, {a}, {b}) = {r} {{ BitVec::add_eq_of_ripple_add(64, {a}, {b}, {r}, refl) }}",
            a = of(ADDRESS), b = of(MINUS_EIGHT), r = of((ADDRESS - 8) ^ (1 << 40)))),
        ("small_width", "@BitVec::ripple_add(8, @BitVec::ofNat(8, 250), @BitVec::ofNat(8, 9)) = @BitVec::ofNat(8, 4)".to_string()),
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
            ("ripple_add w64 operand 2^10", format!("@BitVec::ripple_add(64, {}, {}) = {}", of(ADDRESS), of(1024), of(ADDRESS + 1024))),
            ("ripple_add w64 operand 2^63", format!("@BitVec::ripple_add(64, {}, {}) = {}", of(ADDRESS), of(HIGH), of(ADDRESS + HIGH))),
            ("ripple_sub w64 operand -8", format!("@BitVec::ripple_sub(64, {}, {}) = {}", of(ADDRESS), of(MINUS_EIGHT), of(ADDRESS + 8))),
            ("ripple_add w32 operand 2^31", "@BitVec::ripple_add(32, @BitVec::ofNat(32, 2147479552), @BitVec::ofNat(32, 2147483648)) = @BitVec::ofNat(32, 4294963200)".to_string()),
            ("old add w64 count 8", format!("@bitvec::BitVec::add(64, {}, {}) = {}", of(ADDRESS), of(8), of(ADDRESS + 8))),
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
/// `toInt` at width 64 is `int::Int::sub(OfNat(2^63 - 5), OfNat(2^64))`, which
/// was unary magnitude arithmetic until `int::Int::add` became the payload
/// operations by sign case (issues/int-arithmetic-over-nat-primitives.md):
/// now one synchronous `subNatNat` descent the kernel cancels in a step.
/// `signed_overflow_add` and `signed_lt_bit` over two computed sign-1
/// operands were the cases this rail had to state around: they went through
/// `add`, whose `iterate_increment` asked for `2^63` steps. Since
/// issues/bitvec-width-bounded-defaults.md `add` *is* the ripple, so they are
/// ordinary `refl`s here; `signed_value_of_high_sum` already covered the
/// negative width-64 `toInt` of a ripple sum and is left where it is.
#[test]
fn consumers_over_computed_machine_width_producers_cost_the_width() {
    const M: u128 = 1 << 64;
    const HIGH: u128 = 1 << 63;
    const ADDRESS: u128 = 0x0000_7FFF_FFFF_F000;
    let of = |v: u128| format!("@BitVec::ofNat(64, {v})");
    let high_sum = format!("@BitVec::ripple_add(64, {}, {})", of(5), of(HIGH - 5));
    let src = format!(
        "import nat;\n\
         theorem sign_of_sum(): @BitVec::sign_bit(64, {high_sum}) = True {{ refl }}\n\
         theorem value_of_sum(): @BitVec::toNat(64, {high_sum}) = {HIGH} {{ refl }}\n\
         theorem signed_value_of_sum(): @BitVec::toInt(64, @BitVec::ripple_add(64, {a}, {b})) = OfNat({}) {{ refl }}\n\
         theorem signed_value_of_difference(): @BitVec::toInt(64, @BitVec::ripple_sub(64, @BitVec::zero(64), {c})) = NegSucc(99) {{ refl }}\n\
         theorem signed_value_of_high_sum(): @BitVec::toInt(64, {high_sum}) = NegSucc({}) {{ refl }}\n\
         theorem complement_of_sum(): @BitVec::complement(64, {high_sum}) = {} {{ refl }}\n\
         theorem sum_of_sums(): @BitVec::ripple_add(64, @BitVec::ripple_add(64, {a}, {b}), @BitVec::ripple_sub(64, {c}, @BitVec::one(64))) = {} {{ refl }}\n\
         theorem carry_of_sum(): @BitVec::carry_add_bit(64, @BitVec::ripple_add(64, @BitVec::all_ones(64), @BitVec::zero(64)), @BitVec::one(64)) = True {{ refl }}\n\
         theorem borrow_of_difference(): @BitVec::borrow_sub_bit(64, @BitVec::ripple_sub(64, {a}, {a}), @BitVec::one(64)) = True {{ refl }}\n\
         theorem overflow_of_difference(): @BitVec::signed_overflow_add(64, @BitVec::ripple_sub(64, {h}, @BitVec::one(64)), @BitVec::one(64)) = True {{ refl }}\n\
         theorem sum_below_its_negation(): @BitVec::unsigned_lt_bit(64, {a}, @BitVec::ripple_neg(64, {a})) = True {{ refl }}\n\
         theorem boundary_unsigned(): @BitVec::unsigned_lt_bit(64, @BitVec::zero(64), {h}) = True {{ refl }}\n\
         theorem boundary_signed(): @BitVec::signed_lt_bit(64, {h}, @BitVec::zero(64)) = True {{ refl }}\n\
         theorem value_of_small_offset_add(): @BitVec::toNat(64, @bitvec::BitVec::add(64, {a}, @BitVec::ofNat(64, 8))) = {} {{ refl }}\n\
         theorem overflow_of_two_high_sums(): @BitVec::signed_overflow_add(64, {high_sum}, {high_sum}) = True {{ refl }}\n\
         theorem signed_lt_at_the_boundary(): @BitVec::signed_lt_bit(64, {high_sum}, @BitVec::zero(64)) = True {{ refl }}\n\
         theorem signed_lt_of_computed_pair(): @BitVec::signed_lt_bit(64, {high_sum}, @BitVec::ripple_add(64, {a}, {b})) = True {{ refl }}\n",
        ADDRESS + 1024,
        HIGH - 1,
        bit_vector_literal_at(64, (M - 1) ^ HIGH),
        of(ADDRESS + 1024 + 99),
        ADDRESS + 8,
        a = of(ADDRESS), b = of(1024), c = of(100), h = of(HIGH),
    );
    ok(&src);

    for (name, wrong) in [
        ("sign_of_sum", format!("@BitVec::sign_bit(64, {high_sum}) = False")),
        ("value_of_sum", format!("@BitVec::toNat(64, {high_sum}) = {}", HIGH + 1)),
        ("sum_of_sums", format!(
            "@BitVec::ripple_add(64, @BitVec::ripple_add(64, {a}, {b}), @BitVec::ripple_sub(64, {c}, @BitVec::one(64))) = {}",
            of(ADDRESS + 1024 + 100), a = of(ADDRESS), b = of(1024), c = of(100))),
        ("boundary_unsigned", format!("@BitVec::unsigned_lt_bit(64, {}, @BitVec::zero(64)) = True", of(HIGH))),
    ] {
        let msg = run(&format!("import nat;\ntheorem {name}(): {wrong} {{ refl }}"))
            .expect_err("a wrong consumer result must be refused");
        assert!(msg.contains("NotConvertible"), "{name}: {msg}");
    }
}

/// Closed order facts stated as the *specification* and discharged by
/// `decide` (issues/reflection-through-decide-instances.md,
/// docs/reflection-through-decide-instances-design.md): the `Decide`
/// instances keyed at `unsigned_lt`/`unsigned_le`/`signed_lt`/`signed_le` run
/// the ripple borrow or `int::Int::le_dec` over `toInt`, and resolution builds
/// them before the derived `Le` instances that fit the same goals by
/// unfolding. The literal cases were already within reach of the derived
/// route; the *computed*-operand cases are the ones the head-keyed instances
/// and the candidate order exist for — the unfolding candidate exhausted
/// gigabytes over these operands. The refusal controls are false
/// specifications: refused by the kernel, reported at the `decide`, naming
/// the instance that decided them.
#[test]
fn closed_order_specifications_are_discharged_by_decide() {
    const HIGH: u128 = 1 << 63;
    let of = |v: u128| format!("@BitVec::ofNat(64, {v})");
    let high_sum = format!("@BitVec::ripple_add(64, {}, {})", of(5), of(HIGH - 5));
    let above = format!("@BitVec::ripple_add(64, {}, {})", of(HIGH), of(1));
    let one_sum = format!("@BitVec::ripple_add(64, {}, {})", of(0), of(1));
    ok(&format!(
        "import nat;\nimport int;\n\
         theorem unsigned_boundary(): @BitVec::unsigned_lt(64, {z}, {h}) {{ decide }}\n\
         theorem unsigned_le_boundary(): @BitVec::unsigned_le(64, {h}, {h}) {{ decide }}\n\
         theorem signed_boundary(): @BitVec::signed_lt(64, {h}, {z}) {{ decide }}\n\
         theorem signed_le_boundary(): @BitVec::signed_le(64, {h}, {m}) {{ decide }}\n\
         theorem composed(): @BitVec::unsigned_lt(64, {z}, @BitVec::one(64)) ∧ ¬@BitVec::signed_lt(64, {z}, {h}) {{ decide }}\n\
         theorem computed_unsigned(): @BitVec::unsigned_lt(64, {high_sum}, {above}) {{ decide }}\n\
         theorem computed_unsigned_le(): @BitVec::unsigned_le(64, {high_sum}, {above}) {{ decide }}\n\
         theorem computed_signed(): @BitVec::signed_lt(64, {high_sum}, {one_sum}) {{ decide }}\n\
         theorem computed_signed_le(): @BitVec::signed_le(64, {high_sum}, {one_sum}) {{ decide }}\n",
        z = "@BitVec::zero(64)", h = of(HIGH), m = of(HIGH - 1),
    ));
    for (name, wrong, instance) in [
        ("unsigned_false", format!("@BitVec::unsigned_lt(64, {}, @BitVec::zero(64))", of(HIGH)), "bitvec::BitVec::unsigned_lt::Decide"),
        ("unsigned_false_computed", format!("@BitVec::unsigned_lt(64, {above}, {high_sum})"), "bitvec::BitVec::unsigned_lt::Decide"),
        ("signed_false", format!("@BitVec::signed_lt(64, @BitVec::zero(64), {})", of(HIGH)), "bitvec::BitVec::signed_lt::Decide"),
        ("signed_le_false", format!("@BitVec::signed_le(64, {}, {})", of(HIGH - 1), of(HIGH)), "bitvec::BitVec::signed_le::Decide"),
        ("narrow_false", "@BitVec::unsigned_le(4, @BitVec::ofNat(4, 9), @BitVec::ofNat(4, 3))".to_string(), "bitvec::BitVec::unsigned_le::Decide"),
    ] {
        let msg = run(&format!("import nat;\nimport int;\ntheorem {name}(): {wrong} {{ decide }}"))
            .expect_err("a false specification must be refused");
        assert!(msg.contains("NotConvertible"), "{name}: {msg}");
        assert!(msg.contains("`decide` resolved `Decide<"), "{name}: {msg}");
        assert!(msg.contains(instance), "{name}: {msg}");
    }
}

/// The iterated form's depth, and the pair that separates it from the
/// width-bounded `add`. `iter_add` builds `increment(n, ih)` with `ih` the
/// *pending* elimination of the previous increment, so forcing the result's
/// head bit re-enters the evaluator natively once per unit of the count — a
/// depth the syntax does not show and the fuel does not bound. A depth budget
/// beside the fuel makes that an ordinary refusal
/// (docs/native-depth-budget-design.md, issues/kernel-native-depth-budget.md).
///
/// The same computation through `add` succeeds, because `add` is the ripple
/// (docs/bitvec-width-bounded-defaults-design.md). The refusal is a property
/// of the definition, not of the arguments.
#[test]
fn nested_scrutinee_values_are_refused_rather_than_aborting() {
    const HIGH: u128 = 1 << 63;
    let high_sum = format!("@BitVec::ripple_add(64, @BitVec::ofNat(64, 5), @BitVec::ofNat(64, {}))", HIGH - 5);
    for (name, goal) in [
        (
            "iterated_sum_of_two_high_sums",
            format!("@BitVec::sign_bit(64, @bitvec::BitVec::iter_add(64, {high_sum}, {high_sum})) = False"),
        ),
        (
            "iterated_add_over_a_deep_count",
            "@BitVec::toNat(64, @bitvec::BitVec::iter_add(64, @BitVec::ofNat(64, 0), @BitVec::ofNat(64, 4096))) = 4096".to_string(),
        ),
    ] {
        let msg = run(&format!("import nat;\ntheorem {name}(): {goal} {{ refl }}"))
            .expect_err("an excessive computation must be refused, not abort the process");
        assert!(msg.contains("OutOfFuel"), "{name}: {msg}");
    }
    // The headline of issues/bitvec-width-bounded-defaults.md: the same two
    // computations through the width-bounded `add` are ordinary successes.
    ok(&format!(
        "import nat;\n\
         theorem sum_of_two_high_sums(): @BitVec::sign_bit(64, @bitvec::BitVec::add(64, {high_sum}, {high_sum})) = False {{ refl }}\n\
         theorem add_over_a_deep_count(): @BitVec::toNat(64, @bitvec::BitVec::add(64, @BitVec::ofNat(64, 0), @BitVec::ofNat(64, 4096))) = 4096 {{ refl }}\n"
    ));
}

#[test]
fn open_symbolic_bitvector_wrappers_stop_at_matching_definition_heads() {
    // These transparent wrappers used to normalize their structural bodies
    // completely before conversion compared them with the definition exposed
    // after one delta step: producer failed at width 5, consumer at width 8.
    // Both now rendezvous at the matching global head at machine width.
    ok(r#"
fn produce(n: Nat, left, right: BitVec(n)) -> BitVec(n) {
    @BitVec::band(n, left, right)
}
fn is_zero(n: Nat) -> BitVec(n) -> Bool {
    match n as λ k => BitVec(k) -> Bool {
        Zero => λ x => True,
        Succ(k, ih) => λ x => bool::Bool::not(@BitVec::head_bit(k, x)) && ih(@BitVec::tail_bits(k, x)),
    }
}
fn consume(n: Nat, value: BitVec(n)) -> Bool { is_zero(n, value) }
fn ignore(n: Nat, left, right: BitVec(n)) -> Bool { False }

theorem direct(left, right: BitVec(64)):
    @BitVec::band(64, left, right) = @BitVec::band(64, left, right) { refl }
theorem unused(left, right: BitVec(64)): ignore(64, left, right) = False { refl }
theorem producer_sixty_four(left, right: BitVec(64)):
    produce(64, left, right) = @BitVec::band(64, left, right) { refl }
theorem consumer_sixty_four(value: BitVec(64)):
    consume(64, value) = is_zero(64, value) { refl }
"#);
}
