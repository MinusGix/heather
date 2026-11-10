//! `lib/std/algebra/semiring.hthr` (`issues/semiring-ring-structure-api.md`):
//! the refusals that need the checker. What the language can state is a
//! theorem: every structure resolving at `Nat`, `Int` and `Rat` with the
//! carriers' own units and operations, and each layer's theorems at their own
//! layer, are `lib/_tests/std/algebra/semiring_tests.hthr`, which the
//! whole-library gate checks (`crates/cli/tests/library.rs`); the client
//! showcase is a CLI-tier row of `docs/showcase/showcases.tsv`
//! (docs/test-value-audit.md §3.4, §3.5).
//!
//! What is left: each layer's theorems refused one layer down, `Nat` having
//! no ring, distributivity refused with its operations swapped, and a law
//! that holds at `Rat` modulo `≈` refused as `=`.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support::{self, Refusal};

// lib-closure: rat
const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("char", include_str!("../../../lib/std/text/char.hthr")),
    ("string", include_str!("../../../lib/std/text/string.hthr")),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("order", include_str!("../../../lib/std/algebra/order.hthr")),
    ("semiring", include_str!("../../../lib/std/algebra/semiring.hthr")),
    ("ring", include_str!("../../../lib/std/tactic/ring.hthr")),
    ("mono_laws", include_str!("../../../lib/std/tactic/mono_laws.hthr")),
    ("ordered_field", include_str!("../../../lib/std/algebra/ordered_field.hthr")),
    ("big_operator", include_str!("../../../lib/std/algebra/big_operator.hthr")),
    ("linarith", include_str!("../../../lib/std/tactic/linarith.hthr")),
    ("rat", include_str!("../../../lib/std/num/rat.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const IMPORTS: &str = "import logic; import nat; import int; import list; import relation;
    import relation_props; import algebra_rel; import semiring; import rat;\n";

fn refused(name: &str, src: &str, why: Refusal) {
    support::assert_refused(&mut base(), name, &format!("{IMPORTS}{src}"), why);
}

/// One layer down, the layer a theorem needs is not in scope. A theorem
/// whose indices only its own layer's constraint pins is refused before the
/// search (`semiring_tests` holds the same calls one layer up).
#[test]
fn each_layer_is_refused_one_layer_down() {
    // The signs of products need the additive group ...
    refused(
        "signs_need_the_group",
        "theorem bad<A: Semiring(≈, +, *)>(x, y: A): x ≈ x { let s = Ring::neg_mul<A>(x, y); A.rel_refl(x) }",
        Refusal::Says("needed for `Ring<A>(≈, +, *)`"),
    );
    // ... a split product needs a commutative one ...
    refused(
        "split_product_needs_commutativity",
        "theorem bad<A: Semiring(≈, +, *), B>(xs: List<B>, f, g: B → A):
            MonoidRel::fold(*, xs.map(λ x => f(x) * g(x))) ≈ MonoidRel::fold(*, xs.map(f)) * MonoidRel::fold(*, xs.map(g))
        {
            CommMonoidRel::fold_map_op(≈, *, xs, f, g)
        }",
        Refusal::Says("no instance for `Commutative<A>"),
    );
    // ... and a constant factor out of a sum needs zero's annihilation,
    // which distributivity alone does not give.
    refused(
        "sum_distribution_needs_a_semiring",
        "theorem bad<A: Distributes(≈, +, *)>(x: A, ys: List<A>): x ≈ x { let s = Semiring::mul_sum_l<A>(x, ys); A.rel_refl(x) }",
        Refusal::Says("needed for `Semiring<A>(≈, +, *)`"),
    );
}

#[test]
fn nat_has_no_ring_and_laws_are_checked() {
    refused(
        "nat_ring",
        "fn bad() → Nat { let r = Nat::Ring(RelId, Nat::add, Nat::mul); 0 }",
        Refusal::Says("no instance for `Ring<Nat>"),
    );
    // Distributivity names its operations in order: `+` over `*` is not a law.
    refused(
        "add_over_mul",
        "instance Distributes<Nat>(RelId<Nat>, Nat::mul, Nat::add) {
            distrib_l := Nat::mul_add_distr,
            distrib_r := Nat::add_mul_distr,
        }",
        Refusal::Mismatch,
    );
}

/// `Ring::neg_mul_neg` at `Rat` proves `≈`, which is not `=` (`rat_signs` in
/// the probes is the same call at `≈`).
#[test]
fn at_rat_a_law_holds_modulo_same() {
    refused(
        "rat_signs_as_identity",
        "theorem bad(x, y: Rat): -x * -y = x * y { Ring::neg_mul_neg(x, y) }",
        Refusal::Mismatch,
    );
}
