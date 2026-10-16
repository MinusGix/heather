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
//!     wrong law is refused, a sum reads its summands further out, `<` is
//!     strict, and the witnesses are data that compute.

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
    // The rational facts the reals chain.
    "Rat::abs_sub_self", "Rat::neg_sub_neg", "Rat::abs_neg_sub_neg", "Rat::add_add_add_comm",
    "Rat::add_sub_add", "Rat::dist_add_le", "Rat::sub_add_cancel", "Rat::add_sub_cancel_l",
    "Rat::add_sub_self", "Rat::le_add_nonneg", "Rat::le_add_of_dist", "Rat::sub_le_of_le_add",
    "Rat::dist_le_of_le_add", "Rat::le_of_close_gap", "Rat::same_of_close",
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
        theorem resolved_cong(x, y, z: CReal, a: y ≈ z): x + y ≈ x + z { rel_cong(a) }\n",
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
    // The moduli and gaps are `fn`s, so their witnesses evaluate; a wrong
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
