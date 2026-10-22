//! `lib/std/float/arith.hthr` — arithmetic on floats
//! (`docs/floating-point-design.md` §7.1 and §14, roadmap submilestone
//! `float-arith`).
//!
//!  1. literal operations compute by evaluation at binary16 and E5M2: sums,
//!     products and quotients in several modes (`1/3` through the binary long
//!     division), a fused multiply-add that differs from a multiply then an
//!     add, overflow, the signs of exact zeros, and the special values
//!     (division by zero, `0/0`, `∞ - ∞`, `0 · ∞`), and conversion between
//!     the two formats; and at binary32, whose half-unit counts are past
//!     `2^96` (`issues/kernel-wide-run-comparison.md`): a sum on a tie to
//!     even, a rounded product, the long division of `1/3` toward zero and
//!     to nearest, and a quotient of two floats
//!     (`issues/computed-argument-reevaluated-in-rounding.md`);
//!  2. the value, sign and error theorems hold at an open format, mode and
//!     operands, the relation unfolds at a literal mode in a checking
//!     position, and binary long division agrees with `div`/`mod` at an open
//!     numerator;
//!  3. negative controls: a value theorem cited for the wrong value, a wrong
//!     sign of a product and of `x - x`, a wrong literal quotient, a binary32
//!     product rounded the wrong way, a quotient
//!     claimed finite at `0/0`, and `Float::div` at a format with no NaN,
//!     whose default evidence cannot be built.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra.hthr")),
    ("int", include_str!("../../../lib/std/int.hthr")),
    ("omega", include_str!("../../../lib/std/omega.hthr")),
    ("ring", include_str!("../../../lib/std/ring.hthr")),
    ("relation", include_str!("../../../lib/std/relation.hthr")),
    (
        "relation_props",
        include_str!("../../../lib/std/relation_props.hthr"),
    ),
    (
        "algebra_rel",
        include_str!("../../../lib/std/algebra_rel.hthr"),
    ),
    ("order", include_str!("../../../lib/std/order.hthr")),
    ("semiring", include_str!("../../../lib/std/semiring.hthr")),
    (
        "ordered_field",
        include_str!("../../../lib/std/ordered_field.hthr"),
    ),
    ("rat", include_str!("../../../lib/std/rat.hthr")),
    ("dyadic", include_str!("../../../lib/std/float/dyadic.hthr")),
    ("float", include_str!("../../../lib/std/float/float.hthr")),
    ("round", include_str!("../../../lib/std/float/round.hthr")),
    ("error", include_str!("../../../lib/std/float/error.hthr")),
    ("arith", include_str!("../../../lib/std/float/arith.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn check(e: &mut Elaborator, name: &str, src: &str) {
    if let Err(err) = e.elab_module_source(name, src) {
        panic!("{}", err.render(src));
    }
}

fn refused(name: &str, src: &str) {
    let mut e = base();
    assert!(
        e.elab_module_source(name, src).is_err(),
        "{name} should be refused"
    );
}

// binary16 has qmin = -24, so 1 is significand 1024 at biased exponent 14;
// E5M2 has qmin = -16 and its largest float is 7 · 2^13 = 57344.
const IMPORTS: &str = "import logic; import bool; import nat; import option; import int; import omega; import rat;
    import dyadic; import float; import round; import error; import arith; import relation_props; import algebra_rel; import ordered_field;
fn val_or({F: Format}, r: Float(F), d: Rat) → Rat { match r { Fin(f) => f.val(), Inf(_, _) => d, NaN(_) => d } }
fn neg_bit({F: Format}, r: Float(F)) → Bool { match r { Fin(f) => f.neg, Inf(n, _) => n, NaN(_) => False } }
fn h16(neg: Bool, m, b: Nat, ok: binary16().canonical(m, b).IsTrue()) → Finite(binary16()) { Finite(neg, m, b, ok) }
fn q8(neg: Bool, m, b: Nat, ok: e5m2().canonical(m, b).IsTrue()) → Finite(e5m2()) { Finite(neg, m, b, ok) }
fn one() → Finite(binary16()) { h16(False, 1024, 14, trivial) }
fn three() → Finite(binary16()) { h16(False, 1536, 15, trivial) }
fn pz() → Finite(binary16()) { Finite::zero(binary16(), False) }
fn nz() → Finite(binary16()) { Finite::zero(binary16(), True) }
fn pinf() → Float(binary16()) { Inf(False, trivial) }
fn s32(neg: Bool, m, b: Nat, ok: binary32().canonical(m, b).IsTrue()) → Finite(binary32()) { Finite(neg, m, b, ok) }
fn one32() → Finite(binary32()) { s32(False, 8388608, 126, trivial) }
fn next32() → Finite(binary32()) { s32(False, 8388609, 126, trivial) }
fn half_ulp32() → Finite(binary32()) { s32(False, 8388608, 102, trivial) }
";

// binary32 has qmin = -149: 1 is significand 2^23 at biased exponent 126, its
// ulp is 2^-23 and `half_ulp32` is 2^-24, so `1 + 2^-24` is a tie. A value's
// half-unit count is about 2^150, past where comparing differently built
// numerals used to run out of fuel.
const BINARY32: &str = "
theorem tie(): Rat::Same(val_or(one32().add(half_ulp32()), 99), 1) { refl }
// (1 + 2^-23)^2 = 1 + 2^-22 + 2^-46.
theorem sq(): Rat::Same(val_or(next32().mul(next32()), 99), Rat(8388610, 8388608)) { refl }
// 1/3 = 0x0.AAAAAA…: 0xAAAAAA · 2^-25 truncated.
theorem third(): Rat::Same(val_or(binary32().round_rat(TowardZero, Rat(1, 3)), 99), Rat(11184810, 33554432)) { refl }
// To nearest the next bit is 1 and the rest nonzero, so it rounds up. The
// rounding reads the half-unit count at each of its steps; these two ran out
// of fuel while each read evaluated the long division again
// (issues/computed-argument-reevaluated-in-rounding.md).
theorem third_near(): Rat::Same(val_or(binary32().round_rat(NearestEven, Rat(1, 3)), 99), Rat(11184811, 33554432)) { refl }
// The quotient of two binary32 floats: `2^45 / (3 · 2^45)` unreduced.
fn three32() → Finite(binary32()) { s32(False, 12582912, 127, trivial) }
theorem div_third(): Rat::Same(val_or(one32().div(three32()), 99), Rat(11184811, 33554432)) { refl }
";

const LITERAL: &str = "
// Sums, products and quotients.
theorem two(): Rat::Same(val_or(one().add(one()), 99), 2) { refl }
theorem nine(): Rat::Same(val_or(three().mul(three()), 99), 9) { refl }
theorem third(): Rat::Same(val_or(one().div(three()), 99), Rat(1365, 4096)) { refl }
theorem third_up(): Rat::Same(val_or(one().div(three(), mode := TowardPos), 99), Rat(1366, 4096)) { refl }
theorem third_neg(): Rat::Same(val_or((-one()).div(three(), mode := TowardZero), 99), Rat(-1365, 4096)) { refl }
theorem minus(): Rat::Same(val_or(three().sub(one()), 99), 2) { refl }

// One rounding: (1 + 2^-10)² - (1 + 2^-9) is 2^-20 by fma and 0 by a
// multiply then a subtraction.
theorem fused(): Rat::Same(val_or(h16(False, 1025, 14, trivial).fma(h16(False, 1025, 14, trivial), h16(True, 1026, 14, trivial)), 99), Rat(1, 1048576)) { refl }
theorem unfused(): Rat::Same(val_or(Float::add(h16(False, 1025, 14, trivial).mul(h16(False, 1025, 14, trivial)), Float::Fin(h16(True, 1026, 14, trivial))), 99), 0) { refl }

// Overflow at E5M2: infinity to nearest, the largest float toward zero.
theorem ovf(): (q8(False, 7, 29, trivial).add(q8(False, 7, 29, trivial))).is_inf() = True { refl }
theorem ovf_z(): Rat::Same(val_or(q8(False, 7, 29, trivial).add(q8(False, 7, 29, trivial), mode := TowardZero), 99), 57344) { refl }

// Signs of exact zeros.
theorem diff_pos(): neg_bit(one().sub(one())) = False { refl }
theorem diff_neg(): neg_bit(one().sub(one(), mode := TowardNeg)) = True { refl }
theorem nz_nz(): neg_bit(nz().add(nz())) = True { refl }
theorem pz_nz(): neg_bit(pz().add(nz())) = False { refl }
theorem prod_zero(): neg_bit((-one()).mul(pz())) = True { refl }
theorem quot_zero(): neg_bit(nz().div(three())) = True { refl }
theorem tiny_neg(): neg_bit(h16(True, 1, 0, trivial).mul(h16(False, 1, 0, trivial))) = True { refl }

// Special values.
theorem by_zero(): Float::div(Float::Fin(one()), Float::Fin(pz())) = Inf(False, trivial) { refl }
theorem by_neg_zero(): Float::div(Float::Fin(one()), Float::Fin(nz())) = Inf(True, trivial) { refl }
theorem zero_zero(): (Float::div(Float::Fin(pz()), Float::Fin(pz()))).is_nan() = True { refl }
theorem inf_inf(): (Float::sub(pinf(), Inf(False, trivial))).is_nan() = True { refl }
theorem zero_inf(): (Float::mul(Float::Fin(nz()), Inf(False, trivial))).is_nan() = True { refl }
theorem over_inf(): neg_bit(Float::div(Float::Fin(-one()), Inf(False, trivial))) = True { refl }
theorem e4m3_by_zero(): (Float::div(Float::Fin(Finite::min_normal(e4m3())), Float::Fin(Finite::zero(e4m3(), False)))).is_nan() = True { refl }

// Conversion: binary16's 1/3 is 5/16 in E5M2, E5M2's 5/16 is exact in
// binary16, and a zero keeps its sign.
theorem narrow(): Rat::Same(val_or(h16(False, 1365, 12, trivial).convert(e5m2()), 99), Rat(5, 16)) { refl }
theorem widen(): Rat::Same(val_or(q8(False, 5, 12, trivial).convert(binary16()), 99), Rat(5, 16)) { refl }
theorem neg_zero(): neg_bit(nz().convert(e5m2())) = True { refl }
theorem inf_to_e4m3(): (Float::convert(pinf(), e4m3())).is_nan() = True { refl }

// Binary long division at a quotient `div`'s state machine cannot reach.
theorem long(): (4611686018427400249).ldiv(1000003).quot() = 4611672183410 { refl }
";

const OPEN: &str = "
// Value theorems at an open format, mode and operands.
theorem add_ok({F: Format}, a, b: Finite(F), mode: Mode): RoundsTo(F, mode, a.val() + b.val(), a.add(b, mode := mode)) { Finite::add_correct(a, b, mode) }
theorem sub_ok({F: Format}, a, b: Finite(F), mode: Mode): RoundsTo(F, mode, a.val() -b.val(), a.sub(b, mode := mode)) { Finite::sub_correct(a, b, mode) }
theorem mul_ok({F: Format}, a, b: Finite(F), mode: Mode): RoundsTo(F, mode, a.val() * b.val(), a.mul(b, mode := mode)) { Finite::mul_correct(a, b, mode) }
theorem fma_ok({F: Format}, a, b, c: Finite(F), mode: Mode): RoundsTo(F, mode, a.val() * b.val() + c.val(), a.fma(b, c, mode := mode)) { Finite::fma_correct(a, b, c, mode) }
theorem div_ok({F: Format}, a, b: Finite(F), mode: Mode): RoundsTo(F, mode, a.val() * b.val().recip(), a.div(b, mode := mode)) { Finite::div_correct(a, b, mode) }
theorem cvt_ok({F: Format}, f: Finite(F), G: Format, mode: Mode): RoundsTo(G, mode, f.val(), f.convert(G, mode := mode)) { Finite::convert_correct(f, G, mode) }

// The relation unfolds at a literal mode over a neutral result, in checking position.
theorem near_sum(a, b, r: Finite(binary16()), is: a.add(b) = Fin(r)): Finite::Nearest(a.val() + b.val(), r) {
    let h: RoundsTo(binary16(), NearestEven, a.val() + b.val(), Fin(r)) = j(is, λ v _ => RoundsTo(binary16(), NearestEven, a.val() + b.val(), v), Finite::add_correct(a, b, NearestEven));
    h.left.left
}

// Signs.
theorem mul_xor({F: Format}, a, b: Finite(F), mode: Mode): (a.mul(b, mode := mode)).SignIs(a.neg.xor(b.neg)) { Finite::mul_sign(a, b, mode) }
theorem div_xor({F: Format}, a, b: Finite(F), mode: Mode): (a.div(b, mode := mode)).SignIs(a.neg.xor(b.neg)) { Finite::div_sign(a, b, mode) }
theorem cvt_keeps({F: Format}, f: Finite(F), G: Format, mode: Mode): (f.convert(G, mode := mode)).SignIs(f.neg) { Finite::convert_sign(f, G, mode) }
theorem self_diff({F: Format}, a: Finite(F)): a.sub(a) = Fin(Finite::zero(F, False)) { Finite::sub_self(a, NearestEven) }
theorem self_diff_down({F: Format}, a: Finite(F)): a.sub(a, mode := TowardNeg) = Fin(Finite::zero(F, True)) { Finite::sub_self(a, TowardNeg) }
theorem cancel({F: Format}, a, b: Finite(F), z: a.val() + b.val() ≈ 0, s: a.neg = True, t: b.neg = True):
    (a.add(b)).SignIs(True)
{
    let at = Finite::add_zero(a, b, NearestEven, z);
    let sg: (NearestEven.sum_zero_neg(a.neg, b.neg) = True) = j(sym(s), λ u _ => NearestEven.sum_zero_neg(u, b.neg) = True, j(sym(t), λ w _ => NearestEven.sum_zero_neg(True, w) = True, refl));
    j(sym(at), λ v _ => v.SignIs(True), sg)
}

// Error bounds for a finite result.
theorem add_err({F: Format}, a, b, r: Finite(F), mode: Mode, is: a.add(b, mode := mode) = Fin(r),
    range: (a.val() + b.val()).abs() <= (Finite::max_finite(F)).val(), normal: (Finite::min_normal(F)).val() <= (a.val() + b.val()).abs()):
    ∃ d: Rat, d.abs() <= F.u(mode) ∧ r.val() ≈ (a.val() + b.val()) * (1 + d)
{
    Finite::add_model(a, b, r, mode, is, range, normal)
}
theorem div_err({F: Format}, a, b, r: Finite(F), mode: Mode, is: a.div(b, mode := mode) = Fin(r), range: (a.quot(b)).abs() <= (Finite::max_finite(F)).val()):
    (r.val() -a.quot(b)).abs() <= F.u(mode) * (a.quot(b)).abs() + F.eta(mode)
{
    F.bound_of(mode, a.quot(b), a.div(b, mode := mode), r, is, Finite::div_correct(a, b, mode), range)
}
theorem commutes({F: Format}, a, b: Finite(F), mode: Mode): Float::Same(a.add(b, mode := mode), b.add(a, mode := mode)) { Finite::add_comm(a, b, mode) }
theorem exact_back({F: Format}, f: Finite(F), mode: Mode): Float::Same(f.convert(F, mode := mode), Fin(f)) { Finite::convert_exact(f, F, mode, f, f.val().same_refl()) }

// Special values at open operands.
theorem nan_in({F: Format}, x: Float(F), h: F.specials.has_nan().IsTrue(), mode: Mode): (x.add(NaN(h), mode := mode)).is_nan() = True { (Float::add_nan(x, h, mode)).left }
theorem opp({F: Format}, n: Bool, h1, h2: F.specials.has_inf().IsTrue()): (Float::add(Inf(n, h1), Inf(!n, h2))).is_nan() = True { Float::add_inf_opp(n, h1, h2, NearestEven) }
theorem zero_times({F: Format}, b: Finite(F), z: b.mag = 0, n: Bool, h: F.specials.has_inf().IsTrue()): (Float::mul(Inf(n, h), Fin(b))).is_nan() = True { Float::mul_zero_inf(b, z, n, h, NearestEven) }

// Binary long division is division.
theorem ldiv_is_div(n: Nat, d: Pos<Nat>): n.ldiv(d).quot() = n.div(d) { n.ldiv_div(d) }
";

#[test]
fn operations_compute_on_literal_formats() {
    let mut e = base();
    check(&mut e, "arith_literal", &format!("{IMPORTS}{LITERAL}"));
}

#[test]
fn operations_compute_at_binary32() {
    let mut e = base();
    check(&mut e, "arith_binary32", &format!("{IMPORTS}{BINARY32}"));
}

#[test]
fn theorems_hold_at_open_operands() {
    let mut e = base();
    check(&mut e, "arith_open", &format!("{IMPORTS}{OPEN}"));
}

#[test]
fn a_wrong_claim_is_refused() {
    for (i, bad) in [
        "theorem bad({F: Format}, a, b: Finite(F), mode: Mode): RoundsTo(F, mode, a.val() -b.val(), a.add(b, mode := mode)) { Finite::add_correct(a, b, mode) }",
        "theorem bad({F: Format}, a, b: Finite(F), mode: Mode): (a.mul(b, mode := mode)).SignIs(a.neg) { Finite::mul_sign(a, b, mode) }",
        "theorem bad({F: Format}, a: Finite(F)): a.sub(a) = Fin(Finite::zero(F, True)) { Finite::sub_self(a, NearestEven) }",
        "theorem bad(): Rat::Same(val_or(one().div(three()), 99), Rat(1366, 4096)) { refl }",
        "theorem bad(): (Float::div(Float::Fin(pz()), Float::Fin(pz()))).is_finite() = True { refl }",
        "theorem bad(): neg_bit(one().sub(one())) = True { refl }",
        "theorem bad(): Rat::Same(val_or(next32().mul(next32()), 99), Rat(8388611, 8388608)) { refl }",
        "fn bad(x, y: Float(e2m1())) → Float(e2m1()) { Float::div(x, y) }",
    ]
    .iter()
    .enumerate()
    {
        refused(&format!("arith_bad_{i}"), &format!("{IMPORTS}{bad}"));
    }
}
