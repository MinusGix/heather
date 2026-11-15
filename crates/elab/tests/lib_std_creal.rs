//! `lib/std/num/creal.hthr` (`docs/library/creal.md`): the
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
//! The termwise controls are mismatches: a term is a dyadic read as a
//! rational (`x.at(n)`), and the elaborator compares those itself; the
//! order and product citations are still left to the kernel.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support::{self, Refusal};

// lib-closure: creal
const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("order", include_str!("../../../lib/std/algebra/order.hthr")),
    ("semiring", include_str!("../../../lib/std/algebra/semiring.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("char", include_str!("../../../lib/std/text/char.hthr")),
    ("string", include_str!("../../../lib/std/text/string.hthr")),
    ("mono_laws", include_str!("../../../lib/std/tactic/mono_laws.hthr")),
    ("ordered_field", include_str!("../../../lib/std/algebra/ordered_field.hthr")),
    ("ring", include_str!("../../../lib/std/tactic/ring.hthr")),
    ("big_operator", include_str!("../../../lib/std/algebra/big_operator.hthr")),
    ("linarith", include_str!("../../../lib/std/tactic/linarith.hthr")),
    ("rat", include_str!("../../../lib/std/num/rat.hthr")),
    ("lattice", include_str!("../../../lib/std/algebra/lattice.hthr")),
    ("dyadic", include_str!("../../../lib/std/num/float/dyadic.hthr")),
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
/// reads index n+1, so `x + 0` is close to `x` only eventually
/// (`CReal::add_zero`); the product's index depends on the factors' bounds in
/// order, so even commutativity goes through `mul_close`.
#[test]
fn laws_are_not_termwise() {
    refused("creal_termwise", &[
        "fn bad(x: CReal) → x + x ≈ x { (x + x).same_of_terms(x, λ n => x.at(n).same_refl()) }",
        "fn bad(x: CReal) → x + 0 ≈ x { (x + 0).same_of_terms(x, λ n => x.at(n + 1).add_zero()) }",
        "fn bad(x, y: CReal) → x * y ≈ y * x {
            (x * y).same_of_terms(y * x, λ n => x.at(x.mul_at(y, n)).mul_comm(y.at(x.mul_at(y, n))))
        }",
        "fn bad(x: CReal) → x * x ≈ x { (x * x).same_of_terms(x, λ n => x.at(n).same_refl()) }",
    ], Refusal::Mismatch);
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
        // Nonnegative factors give a nonnegative product only.
        "fn bad(x, y: CReal, hx: 0 <= x, hy: 0 <= y) → 0 < x * y { CReal::mul_nonneg(hx, hy) }",
    ], Refusal::Mismatch);
    // A positive product needs both factors positive: a nonnegative one
    // carries no gap to multiply. `hx`'s parameter type mentions the implicit
    // `x`; its own type is compared with it, so the kernel's refusal is
    // reported at `hx` with `hx`'s type
    // (`issues/implicit-argument-mismatch-reaches-kernel.md`), both types
    // spelled, each with what it unfolds to.
    refused("creal_mul_pos_of_nonneg", &[
        "fn bad(x, y: CReal, hx: 0 <= x, hy: 0 < y) → 0 < x * y { CReal::mul_pos(hx, hy) }",
    ], Refusal::Says("this has type `0 <= x`, but `0 < x` is expected here; `0 <= x` unfolds to"));
    refused("creal_bad_cite_mismatch", &[
        // Bishop's bound is 2 · 2^-n, not 2^-n.
        "fn bad(x, y: CReal, h: x ≈ y, n: Nat) → (x.at(n) - y.at(n)).abs() <= Rat::inv_pow2(n) { CReal::bishop_of_same(h)(n) }",
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
