//! `lib/std/semiring.hthr` — semirings and rings modulo a relation,
//! instantiated at `Nat` and `Int` under identity and at `Rat` under `≈`
//! (`issues/semiring-ring-structure-api.md`).
//!
//!  1. the closure checks: the module and the client showcase, which proves
//!     generic theorems once and states them at all three carriers;
//!  2. the layers and their theorems are *there*, resolution finds every
//!     instance, the tags hold the carriers' own units, and the instances'
//!     fields are the carriers' operations by `refl`;
//!  3. negative controls: each layer's theorems are refused one layer down
//!     (signs need the group, a split product needs commutativity), `Nat`
//!     has no ring, distributivity is not symmetric in its operations, and
//!     at `Rat` a law holds modulo `≈`, not as `=`.

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

/// Refused, with `needle` in the rendered error: the refusal names the
/// missing structure rather than failing for an unrelated reason.
fn refused_with(name: &str, src: &str, needle: &str) {
    let mut e = base();
    match e.elab_module_source(name, src) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => {
            let message = err.render(src);
            assert!(message.contains(needle), "{name}: {message}");
        }
    }
}

const IMPORTS: &str = "import logic; import nat; import int; import list; import relation;
    import relation_props; import algebra_rel; import semiring; import rat;\n";

#[test]
fn the_layers_and_their_client_check() {
    let mut e = base();
    check(
        &mut e,
        "semiring_client",
        include_str!("../../../docs/showcase/semiring_client.hthr"),
    );
}

const THEOREMS: &[&str] = &[
    "MonoidRel::fold", "MonoidRel::fold_append", "CommMonoidRel::interchange",
    "CommMonoidRel::fold_map_op", "GroupRel::inv_unique", "GroupRel::inv_inv",
    "Semiring::mul_sum_l", "Semiring::sum_mul_r", "Semiring::mul_add_add",
    "Ring::neg_mul", "Ring::mul_neg", "Ring::neg_mul_neg",
    "respects2_relid", "Rat::one_mul", "Rat::neg_add_self", "Rat::mul_zero", "Rat::add_mul_distr",
];

#[test]
fn the_layers_are_there_at_every_carrier() {
    let mut e = base();
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, name) in THEOREMS.iter().enumerate() {
        src.push_str(&format!("    let thm{i} = {name};\n"));
    }
    src.push_str("    0\n}\n");
    // Each structure resolves; the units under the tags are the carriers'
    // own, and negation is the carrier's, definitionally.
    src.push_str(
        "fn nat_layers() → Nat {
            let a = Nat::CommSemiring(RelId, Nat::add, Nat::mul);
            let b = Nat::Semiring(RelId, Nat::add, Nat::mul);
            let c = Nat::Distributes(RelId, Nat::add, Nat::mul);
            let d = Nat::MonoidRel(RelId, Nat::mul);
            0
        }
        fn int_layers() → Nat {
            let a = Int::CommRing(RelId, Int::add, Int::mul);
            let b = Int::Ring(RelId, Int::add, Int::mul);
            let c = Int::GroupRel(RelId, Int::add);
            0
        }
        fn rat_layers() → Nat {
            let a = Rat::CommRing(Rat::Same, Rat::add, Rat::mul);
            let b = Rat::Ring(Rat::Same, Rat::add, Rat::mul);
            let c = Rat::CommSemiring(Rat::Same, Rat::add, Rat::mul);
            0
        }
        theorem nat_zero(): Nat::Semiring(RelId, Nat::add, Nat::mul).unit = 0 { refl }
        theorem nat_one(): Nat::Semiring(RelId, Nat::add, Nat::mul).multiplicative.unit = 1 { refl }
        theorem int_neg(x: Int): Int::Ring(RelId, Int::add, Int::mul).inv(x) = -x { refl }
        theorem rat_one(): Rat::Ring(Rat::Same, Rat::add, Rat::mul).multiplicative.unit = 1 { refl }
        theorem rat_neg(x: Rat): Rat::Ring(Rat::Same, Rat::add, Rat::mul).inv(x) = -x { refl }
        // The `≈` of the identity carriers is `=`.
        theorem nat_same_is_eq(x, y: Nat, h: x ≈ y): x = y { h }
        theorem int_same_is_eq(x, y: Int, h: x = y): x ≈ y { h }\n",
    );
    check(&mut e, "semiring_kit", &src);
}

#[test]
fn each_layer_is_refused_one_layer_down() {
    // The signs of products need the additive group ...
    refused_with(
        "signs_need_the_group",
        &format!(
            "{IMPORTS} theorem bad<A: Semiring(≈, +, *)>(x, y: A): x ≈ x {{
                let s = Ring::neg_mul(x, y);
                A.rel_refl(x)
            }}"
        ),
        "Ring<A>",
    );
    // ... a split product needs a commutative one ...
    refused_with(
        "split_product_needs_commutativity",
        &format!(
            "{IMPORTS} theorem bad<A: Semiring(≈, +, *), B>(xs: List<B>, f, g: B → A):
                MonoidRel::fold(*, xs.map(λ x => f(x) * g(x))) ≈ MonoidRel::fold(*, xs.map(f)) * MonoidRel::fold(*, xs.map(g))
            {{
                CommMonoidRel::fold_map_op(≈, *, xs, f, g)
            }}"
        ),
        "Commutative<A>",
    );
    // ... and a constant factor out of a sum needs zero's annihilation,
    // which distributivity alone does not give.
    refused_with(
        "sum_distribution_needs_a_semiring",
        &format!(
            "{IMPORTS} theorem bad<A: Distributes(≈, +, *)>(x: A, ys: List<A>): x ≈ x {{
                let s = Semiring::mul_sum_l(x, ys);
                s
            }}"
        ),
        "Semiring<A>",
    );
    // The controls: one layer up, the same calls check, and the sum splits
    // at a semiring without a commutative product.
    let mut e = base();
    check(
        &mut e,
        "layer_controls",
        &format!(
            "{IMPORTS} theorem signs<A: Ring(≈, +, *)>(x, y: A): A.inv(x) * y ≈ A.inv(x * y) {{ Ring::neg_mul(x, y) }}
            theorem split<A: CommSemiring(≈, +, *), B>(xs: List<B>, f, g: B → A):
                MonoidRel::fold(*, xs.map(λ x => f(x) * g(x))) ≈ MonoidRel::fold(*, xs.map(f)) * MonoidRel::fold(*, xs.map(g))
            {{
                CommMonoidRel::fold_map_op(≈, *, xs, f, g)
            }}
            theorem split_sum<A: Semiring(≈, +, *), B>(xs: List<B>, f, g: B → A):
                MonoidRel::fold(+, xs.map(λ x => f(x) + g(x))) ≈ MonoidRel::fold(+, xs.map(f)) + MonoidRel::fold(+, xs.map(g))
            {{
                CommMonoidRel::fold_map_op(≈, +, xs, f, g)
            }}"
        ),
    );
}

#[test]
fn nat_has_no_ring_and_laws_are_checked() {
    refused_with(
        "nat_ring",
        &format!("{IMPORTS} fn bad() → Nat {{ let r = Nat::Ring(RelId, Nat::add, Nat::mul); 0 }}"),
        "Ring",
    );
    // Distributivity names its operations in order: `+` over `*` is not a law.
    refused_with(
        "add_over_mul",
        &format!(
            "{IMPORTS} instance Distributes<Nat>(RelId<Nat>, Nat::mul, Nat::add) {{
                distrib_l := Nat::mul_add_distr,
                distrib_r := Nat::add_mul_distr,
            }}"
        ),
        "is expected here",
    );
}

#[test]
fn at_rat_a_law_holds_modulo_same() {
    refused_with(
        "rat_signs_as_identity",
        &format!("{IMPORTS} theorem bad(x, y: Rat): -x * -y = x * y {{ Ring::neg_mul_neg(x, y) }}"),
        "",
    );
    let mut e = base();
    check(
        &mut e,
        "rat_signs_control",
        &format!("{IMPORTS} theorem ok(x, y: Rat): -x * -y ≈ x * y {{ Ring::neg_mul_neg(x, y) }}"),
    );
}
