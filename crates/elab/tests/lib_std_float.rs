//! `lib/std/float/dyadic.hthr` and `lib/std/float/float.hthr` — dyadic
//! rationals, and binary floating-point formats with their finite values
//! (`docs/floating-point-design.md` §3–§4, roadmap submilestone
//! `float-values`).
//!
//!  1. the closure check: a client builds literal floats, evaluates their
//!     values and every standard format's largest finite value, compares
//!     floats, and resolves the order kit at `Finite(F)` and the ring kit at
//!     `Dyadic`;
//!  2. the law kit is *there*, named one by one;
//!  3. negative controls: a non-canonical significand is refused (below
//!     `2^(prec - 1)` above the least exponent, and too wide), E4M3's NaN
//!     pattern is not a finite value, E4M3 has no infinity, and the two zeros
//!     are value-same but not equal.

use std::cell::OnceCell;
use std::sync::Mutex;

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
    (
        "ordered_field",
        include_str!("../../../lib/std/ordered_field.hthr"),
    ),
    ("semiring", include_str!("../../../lib/std/semiring.hthr")),
    ("rat", include_str!("../../../lib/std/rat.hthr")),
    ("dyadic", include_str!("../../../lib/std/float/dyadic.hthr")),
    ("float", include_str!("../../../lib/std/float/float.hthr")),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn base() -> Elaborator {
    BASE.with(|base| {
        base.get_or_init(|| {
            let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            support::semantic_test_base(MODULES).semantic_image()
        })
        .elaborator()
    })
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

const IMPORTS: &str = "import logic; import bool; import nat; import int; import omega; import rat;
    import dyadic; import float; import relation_props; import algebra_rel; import ordered_field;\n";

const CLIENT: &str = "
// Literal floats are canonical by evaluation.
fn one32() → Finite(binary32()) { Finite(False, 8388608, 126, trivial) }
fn half32() → Finite(binary32()) { Finite(False, 8388608, 125, trivial) }
fn tiny16() → Finite(binary16()) { Finite(True, 3, 0, trivial) }

theorem one32_val(): Rat::Same(one32().val(), 1) { refl }
theorem half32_lt_one(): half32() < one32() { trivial }
theorem neg_lt(): -one32() < half32() { trivial }
theorem tiny16_val(): Rat::Same(tiny16().val(), Rat(-3, 16777216)) { refl }

// Each standard format's largest finite value.
theorem max32(): Rat::Same((Finite::max_finite(binary32())).val(), Rat::ofInt(OfNat(16777215) * OfNat(Nat::pow(2, 104)))) { refl }
theorem max16(): Rat::Same((Finite::max_finite(binary16())).val(), 65504) { refl }
theorem max_bf16(): Rat::Same((Finite::max_finite(bfloat16())).val(), Rat::ofInt(OfNat(255) * OfNat(Nat::pow(2, 120)))) { refl }
theorem max_e4m3(): Rat::Same((Finite::max_finite(e4m3())).val(), 448) { refl }
theorem max_e5m2(): Rat::Same((Finite::max_finite(e5m2())).val(), 57344) { refl }
theorem max_e3m2(): Rat::Same((Finite::max_finite(e3m2())).val(), 28) { refl }
theorem max_e2m3(): Rat::Same((Finite::max_finite(e2m3())).val(), Rat(15, 2)) { refl }
theorem max_e2m1(): Rat::Same((Finite::max_finite(e2m1())).val(), 6) { refl }

// The least subnormal and least normal.
theorem min_sub32(): Rat::Same((Finite::min_subnormal(binary32())).val(), Rat(1, Nat::pow(2, 149), den_pos := Nat::pow_pos(a := 2, n := 149, pa := trivial))) { refl }
theorem min_norm32(): Rat::Same((Finite::min_normal(binary32())).val(), Rat(1, Nat::pow(2, 126))) { refl }

// The zeros are value-same.
theorem zeros_same(): Finite::zero(binary32(), False) ≈ Finite::zero(binary32(), True) { refl }

// E4M3 has no infinity: a float of that format is never infinite.
theorem e4m3_not_inf(x: Float(e4m3())): x.is_inf() = False { x.not_inf(refl) }

// Constructors build at a literal format and at an open one, and the methods
// compute through them.
fn inf32() → Float(binary32()) { Inf(False, trivial) }
theorem inf32_is_inf(): inf32().is_inf() = True { refl }
fn wrap({F: Format}, x: Finite(F)) → Float(F) { Fin(x) }
theorem wrap_is_finite({F: Format}, x: Finite(F)): wrap(x).is_finite() = True { refl }
theorem wrap_finite({F: Format}, x: Finite(F)): wrap(x).finite() = Some(x) { refl }

// The order kit resolves at Finite(F), the ring kit at Dyadic.
theorem chain({F: Format}, x, y, z: Finite(F), a: x < y, b: y < z): x < z { relation_step(Finite::Lt, x, y, z, a, b) }
theorem le_chain({F: Format}, x, y, z: Finite(F), a: x <= y, b: y <= z): x <= z { PseudoOrder::le_trans(x, y, z, a, b) }
theorem dy_ring(a, b: Dyadic): a * (b + 1) ≈ a * b + a {
    relation_step(Dyadic::Same, a * (b + 1), a * b + a * 1, a * b + a, a.mul_add_distr(b, 1), rel_cong(a.mul_one()))
}
";

#[test]
fn floats_and_their_client_check() {
    let mut e = base();
    check(&mut e, "float_client", &format!("{IMPORTS}{CLIENT}"));
}

const LAWS: &[&str] = &[
    // Dyadic: the embedding and the setoid.
    "Dyadic::rat", "Dyadic::rat_split", "Dyadic::same_refl", "Dyadic::same_sym", "Dyadic::same_trans",
    "Dyadic::same_via", "Dyadic::zero_mant",
    // Dyadic: arithmetic, the homomorphisms and the ring laws.
    "Dyadic::ofInt", "Dyadic::neg", "Dyadic::add", "Dyadic::mul", "Dyadic::sub", "Dyadic::shift",
    "Dyadic::rat_neg", "Dyadic::rat_add", "Dyadic::rat_mul", "Dyadic::rat_sub", "Dyadic::rat_ofInt",
    "Dyadic::rat_zero", "Dyadic::rat_one", "Dyadic::neg_respects", "Dyadic::add_respects",
    "Dyadic::mul_respects", "Dyadic::add_comm", "Dyadic::mul_comm", "Dyadic::add_assoc",
    "Dyadic::mul_assoc", "Dyadic::zero_add", "Dyadic::add_zero", "Dyadic::one_mul", "Dyadic::mul_one",
    "Dyadic::add_neg", "Dyadic::neg_add_self", "Dyadic::mul_add_distr", "Dyadic::add_mul_distr",
    "Dyadic::zero_mul", "Dyadic::mul_zero",
    // Dyadic: order, shifts and alignment.
    "Dyadic::lt_irrefl", "Dyadic::lt_trans", "Dyadic::le_trans", "Dyadic::lt_respects",
    "Dyadic::same_of_not_lt", "Dyadic::le_of_not_lt", "Dyadic::not_lt_of_le", "Dyadic::lt_cotrans",
    "Dyadic::le_dec", "Dyadic::le_refl", "Dyadic::le_of_same", "Dyadic::le_of_lt", "Dyadic::le_total",
    "Dyadic::lt_of_lt_of_le", "Dyadic::lt_of_le_of_lt", "Dyadic::rat_shift_split", "Dyadic::align",
    "Dyadic::ofInt_le", "Dyadic::ofInt_lt", "Dyadic::lt_of_mant_lt",
    // Formats.
    "Specials::has_inf", "Specials::has_nan", "Specials::reserves_top", "Format::prec", "Format::emax",
    "Format::qmin", "Format::qmax", "Format::half", "Format::top", "Format::top_double",
    "Format::canonical", "Format::two_le_half", "Format::four_le_top", "Format::canonical_intro",
    "Format::max_mag", "binary16", "binary32", "binary64", "bfloat16", "e5m2", "e4m3", "e3m2", "e2m3",
    "e2m1",
    // Finite floats: structure, value, order.
    "Finite::eta_parts", "Finite::ext", "Finite::q", "Finite::signed", "Finite::dyadic", "Finite::val",
    "Finite::ulp", "Finite::same_refl", "Finite::same_sym", "Finite::same_trans", "Finite::lt_irrefl",
    "Finite::lt_trans", "Finite::lt_respects", "Finite::same_of_not_lt", "Finite::le_of_not_lt",
    "Finite::not_lt_of_le", "Finite::lt_cotrans", "Finite::le_dec", "Finite::le_refl",
    "Finite::le_of_same", "Finite::le_of_lt", "Finite::le_trans", "Finite::le_total",
    "Finite::lt_of_lt_of_le", "Finite::lt_of_le_of_lt", "Finite::neg", "Finite::neg_neg",
    "Finite::dyadic_neg",
    // Constants.
    "Finite::zero", "Finite::min_subnormal", "Finite::min_normal", "Finite::max_finite",
    "Finite::zero_dyadic", "Finite::min_normal_dyadic",
    // Floats.
    "Float::is_finite", "Float::is_nan", "Float::is_inf", "Float::finite",
    "Float::not_inf", "Float::not_nan",
    // The general facts the module added to nat and int.
    "Nat::pow_pos", "Nat::le_pow_self", "Nat::int_pow_add", "Int::pos_part", "Int::neg_part",
    "Int::pos_sub_neg",
];

#[test]
fn the_law_kit_is_there() {
    let mut e = base();
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, law) in LAWS.iter().enumerate() {
        src.push_str(&format!("    let law{i} = {law};\n"));
    }
    src.push_str("    0\n}\n");
    check(&mut e, "float_kit", &src);
}

#[test]
fn a_float_must_be_canonical() {
    // Above the least exponent the significand must be normal.
    refused(
        "float_not_normal",
        &format!("{IMPORTS} fn bad() → Finite(binary16()) {{ Finite(False, 1, 1, trivial) }}"),
    );
    // A significand of `prec + 1` bits does not fit.
    refused(
        "float_too_wide",
        &format!("{IMPORTS} fn bad() → Finite(e2m1()) {{ Finite(False, 4, 1, trivial) }}"),
    );
    // The controls: the same parts one step inside the bounds are canonical.
    let mut e = base();
    check(
        &mut e,
        "float_canonical_control",
        &format!(
            "{IMPORTS} fn sub() → Finite(binary16()) {{ Finite(False, 1, 0, trivial) }}
            fn wide() → Finite(e2m1()) {{ Finite(False, 3, 1, trivial) }}"
        ),
    );
}

#[test]
fn e4m3_keeps_no_infinity_and_reserves_its_top_pattern() {
    // 480 = 15 · 2^5 is E4M3's NaN pattern, not a finite value.
    refused(
        "float_e4m3_nan_pattern",
        &format!("{IMPORTS} fn bad() → Finite(e4m3()) {{ Finite(False, 15, 14, trivial) }}"),
    );
    // E4M3 has no infinity to build.
    refused(
        "float_e4m3_inf",
        &format!("{IMPORTS} fn bad() → Float(e4m3()) {{ Inf(False, trivial) }}"),
    );
    // The controls: E5M2 keeps the significand E4M3 reserves, and has
    // infinities; E4M3 has a NaN.
    let mut e = base();
    check(
        &mut e,
        "float_e4m3_control",
        &format!(
            "{IMPORTS} fn top() → Finite(e5m2()) {{ Finite(False, 7, 29, trivial) }}
            fn inf() → Float(e5m2()) {{ Inf(False, trivial) }}
            fn nan() → Float(e4m3()) {{ NaN(trivial) }}"
        ),
    );
}

#[test]
fn the_zeros_are_same_but_not_equal() {
    refused(
        "float_zeros_equal",
        &format!(
            "{IMPORTS} theorem bad(): Finite::zero(binary32(), False) = Finite::zero(binary32(), True) {{ refl }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "float_zeros_control",
        &format!(
            "{IMPORTS} theorem ok(): Finite::zero(binary32(), False) ≈ Finite::zero(binary32(), True) {{
                Dyadic::same_trans(Finite::zero_dyadic(binary32(), False), Dyadic::same_sym(Finite::zero_dyadic(binary32(), True)))
            }}"
        ),
    );
}

#[test]
fn a_float_reads_its_format_at_an_open_parameter() {
    // At an open format a wrapped finite value is not a NaN: the parameter
    // reaches the constructor's field rather than being captured, so the
    // false claim does not compute to `True`.
    refused(
        "float_open_not_nan",
        &format!(
            "{IMPORTS} fn wrap({{F: Format}}, x: Finite(F)) → Float(F) {{ Fin(x) }}
            theorem bad({{F: Format}}, x: Finite(F)): wrap(x).is_nan() = True {{ refl }}"
        ),
    );
    // An infinity at an open format needs the format's evidence: it is not
    // built from nothing.
    refused(
        "float_open_inf_needs_evidence",
        &format!("{IMPORTS} fn bad({{F: Format}}) → Float(F) {{ Inf(False, trivial) }}"),
    );
    // The control: given the evidence, it builds.
    let mut e = base();
    check(
        &mut e,
        "float_open_control",
        &format!(
            "{IMPORTS} fn inf({{F: Format}}, h: F.specials.has_inf().IsTrue()) → Float(F) {{ Inf(False, h) }}"
        ),
    );
}
