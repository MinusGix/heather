//! `lib/std/algebra/ordered_field.hthr`
//! (`docs/library/constructive-ordered-field-design.md`): the refusals that need the
//! checker. What the language can state is a theorem: every layer resolving
//! at `Rat` and `CReal` with the carriers' own operations as fields, each
//! layer's theorems at its own layer, predicates meeting their unfoldings,
//! and the ordered layers being rings are
//! `lib/_tests/std/algebra/ordered_field_tests.hthr`, which the
//! whole-library gate checks (`crates/cli/tests/library.rs`); the client
//! showcase is a CLI-tier row of `docs/showcase/showcases.tsv`
//! (docs/test-value-audit.md §3.4, §3.5).
//!
//! What is left: each layer's theorems refused one layer down, a wrong law
//! refused as an instance, the inverse refused without its own argument's
//! apartness or at the wrong sign, nothing in the interface deciding, and
//! the reciprocal not being the group's `inv`.

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

const IMPORTS: &str = "import logic; import nat; import int; import omega; import relation_props;
    import algebra_rel; import semiring; import ordered_field; import rat; import creal;\n";

fn refused(name: &str, src: &str, why: Refusal) {
    support::assert_refused(&mut base(), name, &format!("{IMPORTS}{src}"), why);
}

#[test]
fn each_layer_is_refused_one_layer_down() {
    // `≤` is transitive only where `<` is located ...
    refused(
        "le_trans_needs_locatedness",
        "theorem bad<A: StrictOrder(≈, <, <=)>(x, y, z: A, h1: x <= y, h2: y <= z): x <= z {
            PseudoOrder::le_trans(x, y, z, h1, h2)
        }",
        Refusal::Says("needed for `PseudoOrder<A>(≈, <, <=)`"),
    );
    // ... and so is the mixed step from `<` through `≤`.
    refused(
        "mixed_step_needs_locatedness",
        "theorem bad<A: StrictOrder(≈, <, <=)>(x, y, z: A, h1: x < y, h2: y <= z): x < z {
            PseudoOrder::lt_of_lt_of_le(x, y, z, h1, h2)
        }",
        Refusal::Says("needed for `PseudoOrder<A>(≈, <, <=)`"),
    );
    // A bound's positivity needs the located group, not only the group.
    refused(
        "bound_pos_needs_locatedness",
        "theorem bad<A: OrderedAddGroup(≈, <, <=, +)>(x, e: A, h: AbsLt(x, e)): A.unit < e {
            LocatedAddGroup::abs_lt_pos(x, e, h)
        }",
        Refusal::Says("no instance for `LocatedAddGroup<A>"),
    );
    // A ring theorem needs a ring: a located group has no product.
    refused(
        "ring_theorem_needs_a_ring",
        "theorem bad<A: LocatedAddGroup(≈, <, <=, +)>(x, y: A): A.inv(x) * y ≈ A.inv(x * y) { Ring::neg_mul(x, y) }",
        Refusal::Says("`*` has no meaning here"),
    );
}

#[test]
fn a_wrong_law_is_refused() {
    // `≤` is not a strict order: it is reflexive, so the irreflexivity law
    // cannot be filled.
    refused(
        "le_as_strict_order",
        "instance StrictOrder<Rat>(Rat::Same, Rat::Le, Rat::Le) {
            lt_irrefl := Rat::lt_irrefl,
            lt_trans := λ x y z h1 h2 => Rat::le_trans(h1, h2),
            lt_respects := λ x x2 y y2 hx hy h => Rat::le_respects(hx, hy, h),
            lt_tight := λ x y h1 h2 => Rat::same_of_not_lt(h1, h2),
            le_of_not_lt := λ x y h => Rat::le_of_not_lt(h),
            not_lt_of_le := λ x y h => Rat::not_lt_of_le(h),
        }",
        Refusal::Says("Not(x <= x)"),
    );
    // `≤` is not `<`: `le_refl` at an expected `x < x` reads `<` into its
    // order slot, and no `StrictOrder` has `<` there.
    refused(
        "le_is_not_lt",
        "theorem bad<A: OrderedField(≈, <, <=, +, *)>(x: A): x < x { StrictOrder::le_refl(x) }",
        Refusal::Says("no instance for `StrictOrder<A>"),
    );
    // Abs-bounds compose in their own order: the halves swapped are refused.
    refused(
        "unfolded_predicate_swapped",
        "theorem bad(x, y, e, d: Rat, hx: -e < x ∧ x < e, hy: -d < y ∧ y < d): x + y < e + d ∧ -(e + d) < x + y {
            OrderedAddGroup::abs_lt_add(x, y, e, d, hx, hy)
        }",
        Refusal::Mismatch,
    );
}

#[test]
fn the_inverse_wants_its_own_argument_apart() {
    // `0 < 1` is apartness of one, not of an arbitrary x.
    refused(
        "inverse_of_unrelated_proof",
        "fn bad<A: OrderedField(≈, <, <=, +, *)>(x: A) → A { A.recip(x, Inr(A.zero_lt_one)) }",
        Refusal::Mismatch,
    );
    // Without a proof, `recip` is still waiting for one: it is not an `A`.
    refused(
        "inverse_without_proof",
        "fn bad<A: OrderedField(≈, <, <=, +, *)>() → A { A.recip(A.unit) }",
        Refusal::Mismatch,
    );
    // The inverse's sign is its argument's: a negative argument does not
    // give a positive inverse.
    refused(
        "inverse_sign_of_negative",
        "theorem bad<A: OrderedField(≈, <, <=, +, *)>(x: A, hx: x < A.unit): A.unit < A.recip(x, Inl(hx)) {
            OrderedField::recip_pos(x, Inl(hx), hx)
        }",
        Refusal::Mismatch,
    );
    // The reciprocal is `recip`: `inv` is the additive group's negation, one
    // argument and no apartness.
    refused(
        "inv_is_negation",
        "fn bad<A: OrderedField(≈, <, <=, +, *)>(x: A, h: ApartBy(<, x, A.unit)) → A { A.inv(x, h) }",
        Refusal::Says("applied to too many arguments"),
    );
}

/// No layer carries trichotomy or a `≤` decider; `Rat` has both as extras
/// (`rat_decides` in the probes), `CReal` has neither.
#[test]
fn nothing_in_the_interface_decides() {
    refused(
        "no_trichotomy",
        "theorem bad<A: OrderedField(≈, <, <=, +, *)>(x: A): x < A.unit ∨ x ≈ A.unit ∨ A.unit < x { A.lt_trichotomy(x, A.unit) }",
        Refusal::Says("unbound name `lt_trichotomy`"),
    );
    refused(
        "no_le_decider",
        "fn bad<A: OrderedField(≈, <, <=, +, *)>(x, y: A) → x <= y ∨ ¬(x <= y) { A.le_dec(x, y) }",
        Refusal::Says("unbound name `le_dec`"),
    );
}
