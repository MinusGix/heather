//! `lib/std/num/creal.hthr` (`docs/regular-cauchy-reals-round.md`): the
//! refusals that need the checker. Everything the language can state about
//! the reals is a theorem: the probes at specific values, the computed
//! moduli and gaps, the instance checks, and the `¬` theorems for the false
//! claims a reader might expect (`≈` is not `=`, `≤` is not `<`, `n ↦ n` is
//! not regular) are `lib/_tests/std/num/creal_tests.hthr`, which the
//! whole-library gate checks (`crates/cli/tests/library.rs`); the client
//! showcase is a CLI-tier row of `docs/showcase/showcases.tsv`
//! (docs/test-value-audit.md §3.4, §3.5).
//!
//! What is left: lemmas cited at statements they do not prove (vacuity
//! controls: a termwise proof where the law holds only eventually, a wrong
//! law, a reversed or strengthened order law), and the evidence searches
//! that must fail (an inverse at zero or an unknown sign, a negative power).
//! Most vacuity controls are refused by the kernel: the elaborator's
//! conversion leaves these sequence comparisons to it.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support::{self, Refusal};

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("ring", include_str!("../../../lib/std/tactic/ring.hthr")),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("order", include_str!("../../../lib/std/algebra/order.hthr")),
    ("semiring", include_str!("../../../lib/std/algebra/semiring.hthr")),
    ("ordered_field", include_str!("../../../lib/std/algebra/ordered_field.hthr")),
    ("rat", include_str!("../../../lib/std/num/rat.hthr")),
    ("creal", include_str!("../../../lib/std/num/creal.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const IMPORTS: &str = "import logic; import bool; import nat; import int; import algebra; import omega; import rat;
    import creal; import relation_props; import algebra_rel;\n";

fn refused(prefix: &str, cases: &[&str], why: Refusal) {
    for (i, case) in cases.iter().enumerate() {
        support::assert_refused(&mut base(), &format!("{prefix}_{i}"), &format!("{IMPORTS}{case}"), why);
    }
}

/// Termwise proofs of laws that hold only eventually or not at all: the sum
/// reads index 2n+1, so `x + 0` is close to `x` only from 2k+1 on
/// (`CReal::add_zero`); the product's index depends on the factors' bounds in
/// order, so even commutativity goes through `mul_close`.
#[test]
fn laws_are_not_termwise() {
    refused("creal_termwise", &[
        "fn bad(x: CReal) → x + x ≈ x { (x + x).same_of_terms(x, λ n => x.seq(n).same_refl()) }",
        "fn bad(x: CReal) → x + 0 ≈ x { (x + 0).same_of_terms(x, λ n => x.seq(n + n + 1).add_zero()) }",
        "fn bad(x, y: CReal) → x * y ≈ y * x {
            (x * y).same_of_terms(y * x, λ n => x.seq(x.mul_at(y, n)).mul_comm(y.seq(x.mul_at(y, n))))
        }",
        "fn bad(x: CReal) → x * x ≈ x { (x * x).same_of_terms(x, λ n => x.seq(n).same_refl()) }",
    ], Refusal::Kernel);
}

/// Each lemma cited at a statement it does not prove.
#[test]
fn lemmas_are_cited_at_their_own_statements() {
    refused("creal_bad_cite", &[
        // `<` does not hold up to `≈` the wrong way round.
        "fn bad(x, y, z: CReal, a: x ≈ y, b: y < z) → z < x { CReal::lt_respects(CReal::same_sym(a), z.same_refl(), b) }",
        // Zero absorbs, but one does not.
        "fn bad() → CReal::Same(1 * 1, 0) { CReal::mul_zero(1) }",
        "fn bad(x: CReal, h: x.Apart(0)) → x * x⁻¹ ≈ 0 { x.mul_inv() }",
        "theorem bad(x: CReal, h: x.Apart(0)): x ^ (-1) ≈ x { x.pow_neg_one() }",
        // Adding to both sides keeps the direction of a gap.
        "fn bad(x, y, z: CReal, h: x < y) → y + z < x + z { x.add_lt_mono_r(y, z, h) }",
        // Bishop's bound is 2/(n+1), not 1/(n+1).
        "fn bad(x, y: CReal, h: x ≈ y, n: Nat) → (x.seq(n) -y.seq(n)).abs() <= Rat::inv_succ(n) { CReal::bishop_of_same(h, n) }",
        // A positive product needs both factors positive: a nonnegative one
        // carries no gap to multiply ...
        "fn bad(x, y: CReal, hx: 0 <= x, hy: 0 < y) → 0 < x * y { CReal::mul_pos(hx, hy) }",
        // ... and nonnegative factors give a nonnegative product only.
        "fn bad(x, y: CReal, hx: 0 <= x, hy: 0 <= y) → 0 < x * y { CReal::mul_nonneg(hx, hy) }",
    ], Refusal::Kernel);
    refused("creal_bad_cite_mismatch", &[
        // A positive sum names one positive summand, not both.
        "fn bad(x, y: CReal, h: 0 < x + y) → 0 < x ∧ 0 < y { CReal::pos_of_add_pos(h) }",
        // A nonnegative factor keeps the direction, never reverses it.
        "fn bad(x, y, z: CReal, h: x <= y, hz: 0 <= z) → y * z <= x * z { CReal::mul_le_mono_r(h, hz) }",
    ], Refusal::Mismatch);
}

/// The inverse needs a gap: none is found at zero, at an embedded zero, or at
/// an unknown sign, and a negative power needs the same.
#[test]
fn the_inverse_needs_a_gap() {
    refused("creal_inverse", &[
        "fn bad() → CReal { CReal::inv(0) }",
        "fn bad(x: CReal) → CReal { x⁻¹ }",
        "fn bad() → CReal { CReal::ofRat(0)⁻¹ }",
    ], Refusal::Says("no instance for `Apart("));
    refused("creal_power", &["fn bad(x: CReal) → CReal { x ^ (-2) }"], Refusal::Says("no instance for `PowOk("));
}
