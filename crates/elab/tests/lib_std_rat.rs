//! `lib/std/pos.hthr` and `lib/std/rat.hthr` — positive naturals and
//! unreduced rationals, the first arithmetic setoid customer
//! (`issues/positive-naturals-and-rationals.md`,
//! `docs/setoid-rationals-round.md`).
//!
//!  1. the closure checks: both modules and the client showcase, which uses
//!     `calc` over `≈` and `rel_cong` through `+`, `*` and `-`;
//!  2. the law kit is *there*, named one by one;
//!  3. negative controls: `≈` is not identity, a wrong law is refused, the
//!     inverse law needs its nonzero hypothesis, and cancellation cannot be
//!     reached at a zero factor;
//!  4. the order completion (`issues/rational-order-completion.md`): `<` is
//!     strict, `|x|` is not `x`, scaling needs a sign, and the Archimedean
//!     bound needs a positive argument.

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
    ("pos", include_str!("../../../lib/std/pos.hthr")),
    ("rat", include_str!("../../../lib/std/rat.hthr")),
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

const IMPORTS: &str = "import logic; import bool; import nat; import int; import omega; import pos; import rat;
    import relation_props; import algebra_rel;\n";

#[test]
fn rationals_and_their_client_check() {
    let mut e = base();
    check(
        &mut e,
        "rat_client",
        include_str!("../../../docs/showcase/rat_client.hthr"),
    );
}

const LAWS: &[&str] = &[
    "Rat::same_refl", "Rat::same_sym", "Rat::same_trans",
    "Rat::add_respects", "Rat::mul_respects", "Rat::neg_respects", "Rat::inv_respects",
    "Rat::add_comm", "Rat::add_assoc", "Rat::add_zero", "Rat::add_neg",
    "Rat::mul_comm", "Rat::mul_assoc", "Rat::mul_one", "Rat::mul_add_distr", "Rat::mul_inv",
    "Rat::le_refl", "Rat::le_trans", "Rat::le_antisymm", "Rat::le_total",
    "Rat::le_respects", "Rat::add_le_mono_r", "Rat::mul_nonneg",
    "Rat::ofInt_add", "Rat::ofInt_mul", "Rat::ofInt_inj", "Rat::ofInt_le",
    "Int::mul_cancel_pos_r", "Int::mul_le_cancel_pos_r",
    // Strict order and its agreement with `¬ ≤`.
    "Rat::le_of_lt", "Rat::lt_irrefl", "Rat::not_le_of_lt", "Rat::lt_of_not_le", "Rat::le_of_not_lt",
    "Rat::lt_trichotomy", "Rat::lt_respects", "Rat::lt_of_lt_of_le", "Rat::lt_of_le_of_lt",
    "Rat::lt_trans", "Rat::lt_cotrans", "Rat::same_of_not_lt", "Rat::le_dec",
    // Order and the additive structure.
    "Rat::sub_respects", "Rat::neg_neg", "Rat::neg_add", "Rat::add_neg_cancel_r",
    "Rat::neg_le", "Rat::neg_lt", "Rat::add_le_mono_l", "Rat::add_le_mono", "Rat::add_le_cancel_r",
    "Rat::add_lt_mono_r", "Rat::add_lt_mono_l", "Rat::add_lt_mono", "Rat::sub_nonneg", "Rat::sub_pos",
    // Absolute value and distance.
    "Rat::abs_respects", "Rat::abs_nonneg", "Rat::le_abs", "Rat::neg_le_abs", "Rat::abs_neg",
    "Rat::abs_mul", "Rat::abs_cases", "Rat::abs_le", "Rat::neg_abs_le", "Rat::abs_triangle",
    "Rat::neg_sub", "Rat::abs_sub_comm", "Rat::sub_add_sub", "Rat::dist_triangle",
    "Int::abs_cases", "Int::le_abs", "Int::neg_le_abs", "Int::abs_mul", "Int::abs_neg", "Int::mul_lt_mono_r",
    // Products.
    "Rat::zero_mul", "Rat::mul_le_mono_r", "Rat::mul_lt_mono_r", "Rat::mul_le_mono_l",
    "Rat::mul_lt_mono_l", "Rat::mul_pos",
    // Archimedean facts.
    "Rat::inv_succ_pos", "Rat::inv_succ_le_one", "Rat::inv_succ_antitone", "Rat::inv_succ_half",
    "Rat::archimedean", "Rat::archimedean_inv",
];

#[test]
fn the_law_kit_is_there() {
    let mut e = base();
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, law) in LAWS.iter().enumerate() {
        src.push_str(&format!("    let law{i} = {law};\n"));
    }
    src.push_str("    0\n}\n");
    // Instance resolution finds the registered dictionaries at `Rat`: the
    // equivalence, the strict order's transitivity, and `Decide` for `if`.
    src.push_str(
        "theorem resolved(x, y, z: Rat, a: x ≈ y, b: y ≈ z): x ≈ z {
            relation_step(Rat::Same, x, y, z, a, b)
        }
        theorem resolved_lt(x, y, z: Rat, a: x < y, b: y < z): x < z {
            relation_step(Rat::Lt, x, y, z, a, b)
        }
        fn larger(x, y: Rat) → Rat { if x <= y { y } else { x } }\n",
    );
    check(&mut e, "rat_kit", &src);
}

#[test]
fn same_is_not_identity() {
    refused(
        "rat_identity",
        &format!("{IMPORTS} theorem bad(): Rat(OfNat(1), Pos(1)) = Rat(OfNat(2), Pos(3)) {{ refl }}"),
    );
    // The control: the same pair is `≈` by computation.
    let mut e = base();
    check(
        &mut e,
        "rat_same_control",
        &format!("{IMPORTS} theorem ok(): Rat(OfNat(1), Pos(1)) ≈ Rat(OfNat(2), Pos(3)) {{ refl }}"),
    );
    refused(
        "rat_not_same",
        &format!("{IMPORTS} theorem bad(): Rat(OfNat(1), Pos(1)) ≈ Rat(OfNat(2), Pos(2)) {{ refl }}"),
    );
}

#[test]
fn a_wrong_law_or_step_is_refused() {
    refused(
        "rat_wrong_law",
        &format!("{IMPORTS} theorem bad(x, y: Rat): x + y ≈ x {{ Rat::add_comm(x, y) }}"),
    );
    // rel_cong lifts a true step into the wrong context only if the endpoints
    // still match; here the written right side drops the `+ x`.
    refused(
        "rat_wrong_cong",
        &format!(
            "{IMPORTS} theorem bad(x, y: Rat): (y + -y) + x ≈ Rat::zero() {{
                rel_cong(Rat::add_neg(y))
            }}"
        ),
    );
}

#[test]
fn inverse_needs_a_nonzero_argument() {
    // 0⁻¹ is 0 by convention, so 0 · 0⁻¹ is 0, not 1.
    refused(
        "rat_zero_inverse",
        &format!("{IMPORTS} theorem bad(): Rat::zero() * Rat::zero().inv() ≈ Rat::one() {{ refl }}"),
    );
    refused(
        "rat_inverse_without_hypothesis",
        &format!(
            "{IMPORTS} theorem bad(x: Rat): x * x.inv() ≈ Rat::one() {{
                Rat::mul_inv(x, λ h => h)
            }}"
        ),
    );
}

#[test]
fn cancellation_is_only_by_a_positive() {
    refused(
        "int_cancel_zero",
        &format!(
            "{IMPORTS} theorem bad(x, y: Int, h: x * OfNat(0) = y * OfNat(0)): x = y {{
                x.mul_cancel_pos_r(y, Pos::one(), h)
            }}"
        ),
    );
}

#[test]
fn strict_order_is_strict() {
    // 1/2 and 2/4 are the same number, so neither is below the other ...
    refused(
        "rat_lt_same",
        &format!("{IMPORTS} theorem bad(): Rat(OfNat(1), Pos(1)) < Rat(OfNat(2), Pos(3)) {{ omega }}"),
    );
    // ... while 1/2 < 3/4 holds by cross-multiplication.
    let mut e = base();
    check(
        &mut e,
        "rat_lt_control",
        &format!("{IMPORTS} theorem ok(): Rat(OfNat(1), Pos(1)) < Rat(OfNat(3), Pos(3)) {{ omega }}"),
    );
    // `≤` does not give `<`.
    refused(
        "rat_lt_of_le",
        &format!("{IMPORTS} theorem bad(x, y: Rat, h: x <= y): x < y {{ omega }}"),
    );
}

#[test]
fn order_laws_need_their_side_conditions() {
    // |x| is not x: -1/1 has absolute value 1/1.
    refused(
        "rat_abs_identity",
        &format!("{IMPORTS} theorem bad(x: Rat): x.abs() ≈ x {{ refl }}"),
    );
    let mut e = base();
    check(
        &mut e,
        "rat_abs_control",
        &format!("{IMPORTS} theorem ok(): Rat(NegSucc(0), Pos(1)).abs() ≈ Rat(OfNat(1), Pos(1)) {{ refl }}"),
    );
    // Scaling preserves order only by a non-negative factor.
    refused(
        "rat_scale_without_sign",
        &format!(
            "{IMPORTS} theorem bad(x, y, z: Rat, h: x <= y): x * z <= y * z {{
                Rat::mul_le_mono_r(x, y, z, h, Rat::le_refl(z))
            }}"
        ),
    );
    // Every positive rational is above some 1/(n+1); zero is not.
    refused(
        "rat_archimedean_at_zero",
        &format!(
            "{IMPORTS} theorem bad(): ∃ n: Nat, Rat::inv_succ(n) < Rat::zero() {{
                Rat::archimedean_inv(Rat::zero(), Rat::le_refl(Rat::zero()))
            }}"
        ),
    );
}
