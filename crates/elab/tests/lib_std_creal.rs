//! `lib/std/creal.hthr` — regular Cauchy reals over `std/rat`, the first
//! computational presentation of the real numbers
//! (`issues/regular-cauchy-reals.md`, `docs/regular-cauchy-reals-round.md`).
//!
//!  1. the closure checks: the module and the client showcase, which uses
//!     `calc` over `≈` and `<`, `rel_cong` through `+`, and evaluates a term,
//!     a modulus and a gap;
//!  2. the law kit is *there*, named one by one, and resolution finds the
//!     registered dictionaries;
//!  3. negative controls: a sequence must be regular, `≈` is not identity, a
//!     wrong law is refused, a sum and a product read their arguments further
//!     out, `<` is strict and `≤` is not `<`, the inverse needs a gap and
//!     reads further out still, and the witnesses are data that compute
//!     (`docs/creal-multiplication-round.md` for the product and `≤`,
//!     `docs/creal-inverse-round.md` for the inverse), and a product's sign
//!     needs both factors' (`docs/creal-mul-order-round.md`).

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
    ("rat", include_str!("../../../lib/std/rat.hthr")),
    ("creal", include_str!("../../../lib/std/creal.hthr")),
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
    import creal; import relation_props; import algebra_rel;\n";

#[test]
fn reals_and_their_client_check() {
    let mut e = base();
    check(
        &mut e,
        "creal_client",
        include_str!("../../../docs/showcase/creal_client.hthr"),
    );
}

const LAWS: &[&str] = &[
    // The setoid.
    "CReal::regular_close", "CReal::same_of_terms", "CReal::same_of_close",
    "CReal::same_refl", "CReal::same_sym", "CReal::same_trans",
    // The embedding.
    "CReal::const_regular", "CReal::ofRat", "CReal::ofRat_respects", "CReal::ofRat_inj",
    "CReal::ofRat_neg", "CReal::ofRat_add", "CReal::ofRat_lt", "CReal::lt_of_ofRat_lt",
    // Arithmetic and the additive laws.
    "CReal::neg_regular", "CReal::add_regular", "CReal::neg_respects", "CReal::add_respects",
    "CReal::sub_respects", "CReal::add_comm", "CReal::add_neg", "CReal::add_zero", "CReal::add_assoc",
    // Strict order and apartness.
    "CReal::lt_of_term", "CReal::lt_respects", "CReal::lt_irrefl", "CReal::lt_trans",
    "CReal::lt_cotrans", "CReal::apart_irrefl", "CReal::apart_sym", "CReal::apart_cotrans",
    "CReal::same_of_not_apart",
    // Multiplication and its laws.
    "CReal::bound", "CReal::bound_le", "CReal::bound_below", "CReal::same_close_far",
    "CReal::mul_close", "CReal::mul_at", "CReal::mul_at_ge", "CReal::mul_regular", "CReal::mul",
    "CReal::mul_respects", "CReal::mul_comm", "CReal::mul_assoc", "CReal::mul_add_distr",
    "CReal::mul_one", "CReal::mul_zero", "CReal::ofRat_mul",
    // The non-strict order.
    "CReal::Le", "CReal::le_refl", "CReal::le_of_lt", "CReal::le_of_same", "CReal::le_trans",
    "CReal::lt_of_lt_of_le", "CReal::lt_of_le_of_lt", "CReal::le_antisymm", "CReal::le_respects",
    "CReal::ofRat_le", "CReal::le_of_ofRat_le",
    // The inverse.
    "CReal::Away", "CReal::away_of_apart", "CReal::inv_at", "CReal::inv_at_start", "CReal::inv_at_far",
    "CReal::inv_at_ge", "CReal::inv_regular", "CReal::inv_gap", "CReal::inv", "CReal::inv_gap_respects",
    "CReal::mul_inv_gap", "CReal::inv_respects", "CReal::mul_inv", "CReal::inv_mul", "CReal::ofRat_inv",
    "CReal::ofRat_apart",
    // Signs and integer powers.
    "CReal::Positive", "CReal::Negative", "CReal::apart_of_positive", "CReal::apart_of_negative",
    "CReal::npow", "CReal::npow_respects", "CReal::npow_add", "CReal::PowOk", "CReal::pow",
    "CReal::pow_ofNat", "CReal::pow_negSucc", "CReal::pow_zero", "CReal::pow_one", "CReal::pow_two",
    "CReal::pow_neg_one",
    // Bishop's pointwise forms.
    "CReal::BishopSame", "CReal::same_of_bishop", "CReal::bishop_of_same",
    "CReal::BishopLe", "CReal::le_of_bishop", "CReal::bishop_of_le",
    // Order and addition.
    "CReal::add_lt_mono_r", "CReal::add_lt_mono_l", "CReal::add_lt_mono", "CReal::add_neg_cancel_r",
    "CReal::add_lt_cancel_r", "CReal::add_lt_cancel_l", "CReal::add_le_mono_r", "CReal::add_le_mono_l",
    "CReal::add_le_mono", "CReal::add_lt_le_mono", "CReal::add_le_lt_mono", "CReal::add_lt_cancel",
    "CReal::zero_add_zero", "CReal::add_pos", "CReal::add_pos_of_nonneg_of_pos", "CReal::add_nonneg",
    "CReal::pos_of_add_pos",
    // Order and multiplication.
    "CReal::mul_pos", "CReal::mul_nonneg", "CReal::zero_add", "CReal::sub_add_cancel",
    "CReal::add_mul_distr", "CReal::sub_nonneg", "CReal::sub_pos", "CReal::mul_le_mono_r",
    "CReal::mul_lt_mono_r", "CReal::mul_le_mono_l", "CReal::mul_lt_mono_l",
    // The rational facts the reals chain.
    "Rat::abs_sub_self", "Rat::neg_sub_neg", "Rat::abs_neg_sub_neg", "Rat::add_add_add_comm",
    "Rat::add_sub_add", "Rat::dist_add_le", "Rat::sub_add_cancel", "Rat::add_sub_cancel_l",
    "Rat::add_sub_self", "Rat::le_add_nonneg", "Rat::le_add_of_dist", "Rat::sub_le_of_le_add",
    "Rat::dist_le_of_le_add", "Rat::le_of_close_gap", "Rat::same_of_close",
    "Rat::mul_le_mul", "Rat::scale_inv_succ", "Rat::scale_inv_succ_half", "Rat::abs_le_natAbs",
    "Rat::two_add_ofNat", "Rat::mul_sub_mul", "Rat::dist_mul_le", "Rat::mul_add_twice",
    "Rat::ofNat_nonneg", "Rat::succ_mul_inv_succ", "Rat::scale_inv_succ_le", "Rat::le_abs_of_add_le_zero",
    "Rat::le_abs_of_zero_add_le", "Rat::nonzero_of_gap", "Rat::recip_abs_le", "Rat::sub_of_inverses",
    "Rat::mul_sub_one_of_inverse", "Rat::dist_recip_le",
    "Rat::add_left_comm", "Rat::le_of_le_add_inv_succ", "Rat::zero_add", "Rat::inv_succ_mul",
    "Rat::mul_nonneg_approx",
];

#[test]
fn the_law_kit_is_there() {
    let mut e = base();
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, law) in LAWS.iter().enumerate() {
        src.push_str(&format!("    let law{i} = {law};\n"));
    }
    src.push_str("    0\n}\n");
    // Instance resolution finds the equivalence, the strict order's
    // transitivity, and `+`'s compatibility with `≈`.
    src.push_str(
        "theorem resolved(x, y, z: CReal, a: x ≈ y, b: y ≈ z): x ≈ z {
            relation_step(CReal::Same, x, y, z, a, b)
        }
        theorem resolved_lt(x, y, z: CReal, a: x < y, b: y < z): x < z {
            relation_step(CReal::Lt, x, y, z, a, b)
        }
        theorem resolved_cong(x, y, z: CReal, a: y ≈ z): x + y ≈ x + z { rel_cong(a) }
        theorem resolved_mul_cong(x, y, z: CReal, a: y ≈ z): x * y ≈ x * z { rel_cong(a) }
        theorem resolved_le(x, y, z: CReal, a: x <= y, b: y <= z): x <= z {
            relation_step(CReal::Le, x, y, z, a, b)
        }\n",
    );
    check(&mut e, "creal_kit", &src);
}

#[test]
fn a_sequence_must_be_regular() {
    // n ↦ n moves by more than 1/(m+1) + 1/(n+1).
    refused(
        "creal_not_regular",
        &format!(
            "{IMPORTS} fn bad() → CReal {{
                CReal(λ n => Rat::ofInt(OfNat(n)), λ m n => omega)
            }}"
        ),
    );
    // The control: a constant sequence is regular.
    let mut e = base();
    check(
        &mut e,
        "creal_regular_control",
        &format!(
            "{IMPORTS} fn ok(q: Rat) → CReal {{
                CReal(λ n => q, λ m n => CReal::const_regular(q, m, n))
            }}"
        ),
    );
}

#[test]
fn same_is_not_identity() {
    // 1/2 and 2/4 embed as different sequences that are the same real.
    refused(
        "creal_identity",
        &format!(
            "{IMPORTS} theorem bad(): CReal::ofRat(Rat(OfNat(1), 2)) = CReal::ofRat(Rat(OfNat(2), 4)) {{ refl }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "creal_same_control",
        &format!(
            "{IMPORTS} fn ok() → CReal::ofRat(Rat(OfNat(1), 2)) ≈ CReal::ofRat(Rat(OfNat(2), 4)) {{
                CReal::ofRat_respects(refl)
            }}"
        ),
    );
    // Distinct rationals do not embed as the same real.
    refused(
        "creal_not_same",
        &format!(
            "{IMPORTS} fn bad() → CReal::zero() ≈ CReal::one() {{
                CReal::ofRat_respects(refl)
            }}"
        ),
    );
}

#[test]
fn a_wrong_law_is_refused() {
    refused(
        "creal_wrong_law",
        &format!(
            "{IMPORTS} fn bad(x: CReal) → x + x ≈ x {{
                (x + x).same_of_terms(x, λ n => x.seq(n).same_refl())
            }}"
        ),
    );
    // `x + 0` is not `x` term by term: the sum reads index 2n+1. It is only
    // close from index 2k+1 on (`CReal::add_zero`).
    refused(
        "creal_add_zero_termwise",
        &format!(
            "{IMPORTS} fn bad(x: CReal) → x + CReal::zero() ≈ x {{
                (x + CReal::zero()).same_of_terms(x, λ n => x.seq(n + n + 1).add_zero())
            }}"
        ),
    );
}

#[test]
fn a_sum_reads_its_summands_further_out() {
    refused(
        "creal_sum_same_index",
        &format!(
            "{IMPORTS} theorem bad(x, y: CReal, n: Nat): (x + y).seq(n) = x.seq(n) + y.seq(n) {{ refl }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "creal_sum_index_control",
        &format!(
            "{IMPORTS} theorem ok(x, y: CReal, n: Nat): (x + y).seq(n) = x.seq(n + n + 1) + y.seq(n + n + 1) {{ refl }}"
        ),
    );
}

#[test]
fn strict_order_is_strict() {
    // 0 < 0 has no rational gap to embed ...
    refused(
        "creal_lt_zero_zero",
        &format!(
            "{IMPORTS} fn bad() → CReal::zero() < CReal::zero() {{
                let gap: (Rat::zero() < Rat::zero()) = omega;
                CReal::ofRat_lt(gap)
            }}"
        ),
    );
    // ... a real is not below itself even with a gap claimed by hand ...
    refused(
        "creal_lt_self",
        &format!(
            "{IMPORTS} fn bad(x: CReal) → x < x {{
                Exists(0, Exists(0, λ n from => x.seq(n).le_refl()))
            }}"
        ),
    );
    // ... and the strict order does not hold up to `≈` the wrong way round.
    refused(
        "creal_lt_wrong_side",
        &format!(
            "{IMPORTS} fn bad(x, y, z: CReal, a: x ≈ y, b: y < z) → z < x {{
                CReal::lt_respects(CReal::same_sym(a), z.same_refl(), b)
            }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "creal_lt_control",
        &format!(
            "{IMPORTS} fn ok() → CReal::zero() < CReal::one() {{
                let gap: (Rat::zero() < Rat::one()) = omega;
                CReal::ofRat_lt(gap)
            }}"
        ),
    );
}

#[test]
fn witnesses_compute() {
    // The moduli and gaps are theorems whose statements carry data, so
    // their sealed proofs open where a projection is stuck on them and the
    // witnesses evaluate (`issues/theorem-witness-unfolding.md`); a wrong
    // value is refused by the same evaluation.
    let mut e = base();
    check(
        &mut e,
        "creal_witnesses",
        &format!(
            "{IMPORTS} theorem modulus(): (CReal::zero().add_zero()(2)).witness = 5 {{ refl }}
            theorem trans_start(x: CReal): (CReal::same_trans(x.same_refl(), x.same_refl())(4)).witness = 0 {{ refl }}"
        ),
    );
    refused(
        "creal_wrong_modulus",
        &format!("{IMPORTS} theorem bad(): (CReal::zero().add_zero()(2)).witness = 4 {{ refl }}"),
    );
}

#[test]
fn a_product_reads_its_factors_further_out() {
    refused(
        "creal_product_same_index",
        &format!(
            "{IMPORTS} theorem bad(x, y: CReal, n: Nat): (x * y).seq(n) = x.seq(n) * y.seq(n) {{ refl }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "creal_product_index_control",
        &format!(
            "{IMPORTS} theorem ok(x, y: CReal, n: Nat): (x * y).seq(n) = x.seq(x.mul_at(y, n)) * y.seq(x.mul_at(y, n)) {{ refl }}"
        ),
    );
    // The index depends on the factors' bounds in order, so even
    // commutativity is not termwise: `mul_comm` goes through `mul_close`.
    refused(
        "creal_mul_comm_termwise",
        &format!(
            "{IMPORTS} fn bad(x, y: CReal) → x * y ≈ y * x {{
                (x * y).same_of_terms(y * x, λ n => x.seq(x.mul_at(y, n)).mul_comm(y.seq(x.mul_at(y, n))))
            }}"
        ),
    );
    // A wrong product law is refused.
    refused(
        "creal_mul_wrong_law",
        &format!(
            "{IMPORTS} fn bad(x: CReal) → x * x ≈ x {{
                (x * x).same_of_terms(x, λ n => x.seq(n).same_refl())
            }}"
        ),
    );
    // Zero absorbs, but one does not.
    refused(
        "creal_mul_one_is_zero",
        &format!("{IMPORTS} fn bad() → CReal::one() * CReal::one() ≈ CReal::zero() {{ CReal::one().mul_zero() }}"),
    );
}

#[test]
fn le_is_not_lt() {
    // `≤` is a refutation and carries no gap: it does not give `<` ...
    refused(
        "creal_le_as_lt",
        &format!("{IMPORTS} fn bad(x: CReal) → x < x {{ x.le_refl() }}"),
    );
    // ... and 1 ≤ 0 is refuted by the gap of 0 < 1.
    let mut e = base();
    check(
        &mut e,
        "creal_le_control",
        &format!(
            "{IMPORTS} theorem ok(): ¬(CReal::one() <= CReal::zero()) {{
                let gap: (Rat::zero() < Rat::one()) = omega;
                λ h => h(CReal::ofRat_lt(gap))
            }}"
        ),
    );
    refused(
        "creal_le_wrong_way",
        &format!(
            "{IMPORTS} fn bad() → CReal::one() <= CReal::zero() {{
                let le: (Rat::zero() <= Rat::one()) = omega;
                CReal::ofRat_le(le)
            }}"
        ),
    );
}

#[test]
fn product_witnesses_compute() {
    // A product law's modulus opens `mul_close`, which opens
    // `same_close_far`: 1 · 1 has bound 3 on each side, so the factors must
    // be within 1/14, which regularity grants from index 55 on.
    let mut e = base();
    check(
        &mut e,
        "creal_product_witnesses",
        &format!(
            "{IMPORTS} theorem modulus(): (CReal::one().mul_comm(CReal::one())(0)).witness = 55 {{ refl }}
            theorem bound(): CReal::ofRat(Rat(-OfNat(7), 2)).bound() = 9 {{ refl }}"
        ),
    );
    refused(
        "creal_wrong_product_modulus",
        &format!("{IMPORTS} theorem bad(): (CReal::one().mul_comm(CReal::one())(0)).witness = 54 {{ refl }}"),
    );
}

const ONE_APART: &str = "theorem one_apart(): CReal::one().Apart(CReal::zero()) {
        let gap: (Rat::zero() < Rat::one()) = omega;
        Inr(CReal::ofRat_lt(gap))
    }\n";

#[test]
fn the_inverse_needs_a_gap() {
    // Zero has no inverse: no gap above it can be claimed ...
    refused(
        "creal_inv_zero",
        &format!(
            "{IMPORTS} fn bad() → CReal {{
                let above: (Rat::zero() + Rat::inv_succ(0) <= Rat::zero()) = omega;
                CReal::zero().inv(h := Inr(Exists(0, Exists(0, λ n from => above))))
            }}"
        ),
    );
    // ... nor can the inverse be asked for without one ...
    refused("creal_inv_no_gap", &format!("{IMPORTS} fn bad() → CReal {{ CReal::zero().inv() }}"));
    // ... and an apartness proof at zero is absurd.
    let mut e = base();
    check(
        &mut e,
        "creal_inv_gap_control",
        &format!(
            "{IMPORTS} fn ok() → CReal {{
                let above: (Rat::zero() + Rat::inv_succ(0) <= Rat::one()) = omega;
                CReal::one().inv(h := Inr(Exists(0, Exists(0, λ n from => above))))
            }}
            theorem zero_absurd(h: CReal::zero().Apart(CReal::zero())): False {{ CReal::zero().apart_irrefl(h) }}"
        ),
    );
}

#[test]
fn the_inverse_reads_further_out() {
    // Not the termwise reciprocal: the inverse reads past the gap's start
    // and far enough out to pay for the reciprocal's (k+1)².
    refused(
        "creal_inv_same_index",
        &format!(
            "{IMPORTS} theorem bad(x: CReal, h: x.Apart(CReal::zero()), n: Nat): x⁻¹.seq(n) = x.seq(n).recip() {{ refl }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "creal_inv_index_control",
        &format!(
            "{IMPORTS} theorem ok(x: CReal, k, s: Nat, gap: x.Away(k, s), n: Nat):
                x.inv_gap(k, s, gap).seq(n) = x.seq(CReal::inv_at(k, s, n)).recip() {{ refl }}"
        ),
    );
    // A wrong field law is refused.
    refused(
        "creal_mul_inv_wrong",
        &format!(
            "{IMPORTS} fn bad(x: CReal, h: x.Apart(CReal::zero())) → x * x⁻¹ ≈ CReal::zero() {{ x.mul_inv() }}"
        ),
    );
}

#[test]
fn the_inverse_computes() {
    // The gap comes out of the apartness proof's sealed proofs and the
    // inverse's terms evaluate: 1/1 has gap 1/2 (k = 1), 1⁻¹ reads 1, and
    // the reciprocal of -2 reads -1/2.
    let mut e = base();
    check(
        &mut e,
        "creal_inv_computes",
        &format!(
            "{IMPORTS} {ONE_APART}
            theorem gap_size(): (CReal::one().away_of_apart(one_apart())).witness = 1 {{ refl }}
            theorem inv_one_term(): CReal::one().inv(h := one_apart()).seq(3) = Rat::one() {{ refl }}
            theorem neg_two_apart(): CReal::ofRat(Rat(-OfNat(2), 1)).Apart(CReal::zero()) {{
                let gap: (Rat(-OfNat(2), 1) < Rat::zero()) = omega;
                Inl(CReal::ofRat_lt(gap))
            }}
            theorem inv_neg_two_term(): CReal::ofRat(Rat(-OfNat(2), 1)).inv(h := neg_two_apart()).seq(5) = Rat(-OfNat(1), 2) {{ refl }}"
        ),
    );
    refused(
        "creal_inv_wrong_value",
        &format!("{IMPORTS} {ONE_APART} theorem bad(): CReal::one().inv(h := one_apart()).seq(3) = Rat::zero() {{ refl }}"),
    );
    refused(
        "creal_inv_wrong_gap",
        &format!("{IMPORTS} {ONE_APART} theorem bad(): (CReal::one().away_of_apart(one_apart())).witness = 0 {{ refl }}"),
    );
}

#[test]
fn order_and_addition() {
    // Adding to both sides keeps the direction of a gap, never reverses it.
    refused(
        "creal_add_lt_reversed",
        &format!(
            "{IMPORTS} fn bad(x, y, z: CReal, h: x < y) → y + z < x + z {{ x.add_lt_mono_r(y, z, h) }}"
        ),
    );
    // A positive sum names one positive summand, not both.
    refused(
        "creal_pos_of_add_both",
        &format!(
            "{IMPORTS} fn bad(x, y: CReal, h: CReal::zero() < x + y) → CReal::zero() < x ∧ CReal::zero() < y {{
                CReal::pos_of_add_pos(h)
            }}"
        ),
    );
    // Bishop's bound is 2/(n+1), not 1/(n+1).
    refused(
        "creal_bishop_too_tight",
        &format!(
            "{IMPORTS} fn bad(x, y: CReal, h: x ≈ y, n: Nat) → (x.seq(n) -y.seq(n)).abs() <= Rat::inv_succ(n) {{
                CReal::bishop_of_same(h, n)
            }}"
        ),
    );
    // The control: the shifted gap is data, the same 1/(k+1) from the same
    // start, and it evaluates.
    let mut e = base();
    check(
        &mut e,
        "creal_shift_control",
        &format!(
            "{IMPORTS} theorem gap(): (Rat::zero() < Rat::one()) {{ omega }}
            theorem shifted(z: CReal): CReal::zero().add_lt_mono_r(CReal::one(), z, CReal::ofRat_lt(gap())).witness = 1 {{ refl }}"
        ),
    );
    refused(
        "creal_shift_wrong_gap",
        &format!(
            "{IMPORTS} theorem gap(): (Rat::zero() < Rat::one()) {{ omega }}
            theorem shifted(z: CReal): CReal::zero().add_lt_mono_r(CReal::one(), z, CReal::ofRat_lt(gap())).witness = 2 {{ refl }}"
        ),
    );
}

const POWER_IMPORTS: &str = "import logic; import bool; import nat; import int; import algebra; import omega;
    import rat; import creal; import relation_props; import algebra_rel;\n";

/// `x⁻¹` and `x ^ n` on the reals (docs/inverse-power-notation-design.md):
/// the apartness is searched from a local apartness or sign, or from an
/// embedded rational's sign; a negative power needs it and a natural one
/// does not. Negative controls: no hypothesis, zero, a wrong law.
#[test]
fn inverse_and_power_notation() {
    let mut e = base();
    check(
        &mut e,
        "creal_power_notation",
        &format!(
            "{POWER_IMPORTS}
            theorem from_apart(x: CReal, h: x.Apart(CReal::zero())): x * x⁻¹ ≈ CReal::one() {{ x.mul_inv() }}
            theorem from_negative(x: CReal, h: x < CReal::zero()): x ^ (-1) ≈ x⁻¹ {{ x.pow_neg_one() }}
            theorem square(x: CReal): x ^ 2 ≈ x * x {{ x.pow_two() }}
            theorem embedded(): CReal::ofRat(Rat(OfNat(2), 1))⁻¹ ≈ CReal::ofRat(Rat(OfNat(2), 1)⁻¹) {{
                CReal::ofRat_inv(Rat(OfNat(2), 1))
            }}"
        ),
    );
    refused("creal_inv_unknown_sign", &format!("{POWER_IMPORTS} fn bad(x: CReal) → CReal {{ x⁻¹ }}"));
    refused("creal_power_negative_unknown", &format!("{POWER_IMPORTS} fn bad(x: CReal) → CReal {{ x ^ (-2) }}"));
    refused("creal_inv_of_zero", &format!("{POWER_IMPORTS} fn bad() → CReal {{ CReal::ofRat(Rat::zero())⁻¹ }}"));
    refused(
        "creal_pow_neg_one_wrong",
        &format!("{POWER_IMPORTS} theorem bad(x: CReal, h: x.Apart(CReal::zero())): x ^ (-1) ≈ x {{ x.pow_neg_one() }}"),
    );
}

#[test]
fn order_and_multiplication() {
    // A positive product needs both factors positive: a nonnegative one
    // carries no gap to multiply.
    refused(
        "creal_mul_pos_of_nonneg",
        &format!(
            "{IMPORTS} fn bad(x, y: CReal, hx: CReal::zero() <= x, hy: CReal::zero() < y) → CReal::zero() < x * y {{
                CReal::mul_pos(hx, hy)
            }}"
        ),
    );
    // A nonnegative factor keeps the direction, never reverses it.
    refused(
        "creal_mul_le_reversed",
        &format!(
            "{IMPORTS} fn bad(x, y, z: CReal, h: x <= y, hz: CReal::zero() <= z) → y * z <= x * z {{
                CReal::mul_le_mono_r(h, hz)
            }}"
        ),
    );
    // Nonnegative factors give a nonnegative product, not a positive one.
    refused(
        "creal_mul_nonneg_strict",
        &format!(
            "{IMPORTS} fn bad(x, y: CReal, hx: CReal::zero() <= x, hy: CReal::zero() <= y) → CReal::zero() < x * y {{
                CReal::mul_nonneg(hx, hy)
            }}"
        ),
    );
    // The control: the product's gap is the product of the gaps, as data.
    // 0 < 1 has the gap 1/2, so 1 · 1 clears zero by 1/4 (k = 3).
    let mut e = base();
    check(
        &mut e,
        "creal_mul_gap_control",
        &format!(
            "{IMPORTS} theorem gap(): (Rat::zero() < Rat::one()) {{ omega }}
            theorem squared(): CReal::mul_pos(CReal::ofRat_lt(gap()), CReal::ofRat_lt(gap())).witness = 3 {{ refl }}"
        ),
    );
    refused(
        "creal_mul_wrong_gap",
        &format!(
            "{IMPORTS} theorem gap(): (Rat::zero() < Rat::one()) {{ omega }}
            theorem squared(): CReal::mul_pos(CReal::ofRat_lt(gap()), CReal::ofRat_lt(gap())).witness = 1 {{ refl }}"
        ),
    );
}
