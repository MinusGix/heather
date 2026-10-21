//! `lib/std/ordered_field.hthr` — the constructive ordered-field interface,
//! instantiated at `Rat` and `CReal`
//! (`issues/constructive-ordered-field-interface.md`,
//! `docs/constructive-ordered-field-design.md`).
//!
//!  1. the closure checks: the module and the client showcase, which proves
//!     generic theorems once and calls them at both carriers;
//!  2. the layers and their theorems are *there*, resolution finds every
//!     instance at both carriers, and the instances' fields are the
//!     carriers' own operations by `refl`;
//!  3. the ordered layers are the algebraic ones extended
//!     (`issues/ordered-field-over-comm-ring.md`): group and ring theorems
//!     apply to them, and `CReal` is a `CommRing`;
//!  4. negative controls: each layer's theorems are refused one layer down
//!     (`≤` transitivity and a bound's positivity need locatedness), a wrong
//!     law is refused, the inverse wants apartness of its own argument and
//!     has its argument's sign (`issues/ordered-field-inverse-sign.md`), `≤`
//!     is not `<`, and nothing in the interface decides.

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
    ("semiring", include_str!("../../../lib/std/semiring.hthr")),
    (
        "ordered_field",
        include_str!("../../../lib/std/ordered_field.hthr"),
    ),
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
    refused_with(name, src, "");
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

const IMPORTS: &str = "import logic; import nat; import int; import omega; import relation_props;
    import algebra_rel; import semiring; import ordered_field; import rat; import creal;\n";

#[test]
fn the_interface_and_its_client_check() {
    let mut e = base();
    check(
        &mut e,
        "ordered_field_client",
        include_str!("../../../docs/showcase/ordered_field_client.hthr"),
    );
}

const THEOREMS: &[&str] = &[
    // The strict order.
    "StrictOrder::lt_asymm", "StrictOrder::lt_respects_l", "StrictOrder::lt_respects_r",
    "StrictOrder::le_refl", "StrictOrder::le_of_lt", "StrictOrder::le_of_same",
    "StrictOrder::le_respects", "StrictOrder::le_antisymm", "StrictOrder::apart_irrefl",
    "StrictOrder::apart_sym", "StrictOrder::apart_respects", "StrictOrder::same_of_not_apart",
    "StrictOrder::not_apart_of_same", "StrictOrder::between_lt", "StrictOrder::between_respects",
    "StrictOrder::between_widen", "StrictOrder::within_of_between", "StrictOrder::apart_of_lt_between",
    // Locatedness.
    "PseudoOrder::locate", "PseudoOrder::lt_of_lt_of_le", "PseudoOrder::lt_of_le_of_lt",
    "PseudoOrder::le_trans", "PseudoOrder::apart_cotrans", "PseudoOrder::within_le",
    "PseudoOrder::within_widen", "PseudoOrder::between_widen_le", "PseudoOrder::between_of_within",
    // The ordered additive group.
    "OrderedAddGroup::add_respects",
    "OrderedAddGroup::add_neg_add", "OrderedAddGroup::neg_add_add", "OrderedAddGroup::add_neg_cancel_r",
    "OrderedAddGroup::sub_add_cancel", "OrderedAddGroup::neg_zero", "OrderedAddGroup::neg_add",
    "OrderedAddGroup::sub_add_sub", "OrderedAddGroup::neg_sub", "OrderedAddGroup::add_lt_mono_l",
    "OrderedAddGroup::add_lt_mono", "OrderedAddGroup::add_lt_cancel_r", "OrderedAddGroup::add_lt_cancel_l",
    "OrderedAddGroup::add_le_mono_r", "OrderedAddGroup::add_le_mono_l", "OrderedAddGroup::neg_lt",
    "OrderedAddGroup::neg_pos", "OrderedAddGroup::neg_of_neg_pos",
    "OrderedAddGroup::sub_pos", "OrderedAddGroup::lt_of_sub_pos", "OrderedAddGroup::between_add",
    "OrderedAddGroup::abs_lt_respects", "OrderedAddGroup::abs_lt_mono", "OrderedAddGroup::abs_lt_neg",
    "OrderedAddGroup::abs_lt_add", "OrderedAddGroup::same_zero_of_abs_lt", "OrderedAddGroup::close_sym",
    "OrderedAddGroup::close_triangle", "OrderedAddGroup::same_of_close",
    // The located group.
    "LocatedAddGroup::add_lt_cancel", "LocatedAddGroup::pos_of_add_pos", "LocatedAddGroup::abs_lt_pos",
    "LocatedAddGroup::add_le_mono", "LocatedAddGroup::neg_le", "LocatedAddGroup::abs_le_of_abs_lt",
    "LocatedAddGroup::abs_le_add", "LocatedAddGroup::abs_lt_of_abs_le",
    // The field.
    "OrderedField::mul_respects", "OrderedField::one_apart_zero",
    "OrderedField::mul_lt_mono_l", "OrderedField::mul_lt_mono_r",
    "OrderedField::recip_unique", "OrderedField::recip_respects", "OrderedField::recip_mul",
    "OrderedField::of_nat_lt_succ", "OrderedField::of_nat_pos",
    // The reciprocal's sign, from the reflection law.
    "OrderedField::recip_pos", "OrderedField::recip_neg", "OrderedField::recip_recip",
    "OrderedField::recip_lt_recip", "OrderedField::archimedean_recip",
    // What the carriers added for their instances.
    "Rat::not_lt_of_le", "Rat::zero_lt_one", "CReal::archimedean", "CReal::zero_lt_one",
    "CReal::ofNat_succ", "Rat::pos_of_mul_pos", "Rat::le_of_mul_le_bounded", "CReal::pos_of_mul_pos",
    "CReal::one_mul", "CReal::zero_mul", "CReal::neg_add_self",
];

#[test]
fn the_layers_are_there_at_both_carriers() {
    let mut e = base();
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, name) in THEOREMS.iter().enumerate() {
        src.push_str(&format!("    let thm{i} = {name};\n"));
    }
    src.push_str("    0\n}\n");
    // Every layer resolves at both carriers, and each field is the
    // carrier's own operation, definitionally.
    src.push_str(
        "fn rat_layers() → Nat {
            let a = Rat::StrictOrder(Rat::Same, Rat::Lt, Rat::Le);
            let b = Rat::Cotransitive(Rat::Lt);
            let c = Rat::PseudoOrder(Rat::Same, Rat::Lt, Rat::Le);
            let d = Rat::OrderedAddGroup(Rat::Same, Rat::Lt, Rat::Le, Rat::add);
            let f = Rat::LocatedAddGroup(Rat::Same, Rat::Lt, Rat::Le, Rat::add);
            let g = Rat::OrderedField(Rat::Same, Rat::Lt, Rat::Le, Rat::add, Rat::mul);
            let r = Rat::CommRing(Rat::Same, Rat::add, Rat::mul);
            0
        }
        fn creal_layers() → Nat {
            let a = CReal::StrictOrder(CReal::Same, CReal::Lt, CReal::Le);
            let b = CReal::Cotransitive(CReal::Lt);
            let c = CReal::PseudoOrder(CReal::Same, CReal::Lt, CReal::Le);
            let d = CReal::OrderedAddGroup(CReal::Same, CReal::Lt, CReal::Le, CReal::add);
            let f = CReal::LocatedAddGroup(CReal::Same, CReal::Lt, CReal::Le, CReal::add);
            let g = CReal::OrderedField(CReal::Same, CReal::Lt, CReal::Le, CReal::add, CReal::mul);
            let r = CReal::CommRing(CReal::Same, CReal::add, CReal::mul);
            0
        }
        theorem rat_zero(): Rat::OrderedField(Rat::Same, Rat::Lt, Rat::Le, Rat::add, Rat::mul).unit = 0 { refl }
        theorem rat_neg(x: Rat): Rat::OrderedField(Rat::Same, Rat::Lt, Rat::Le, Rat::add, Rat::mul).inv(x) = -x { refl }
        theorem rat_recip(x: Rat, h: x.Apart(0)):
            Rat::OrderedField(Rat::Same, Rat::Lt, Rat::Le, Rat::add, Rat::mul).recip(x, h) = x.inv(h := h) { refl }
        theorem creal_one(): CReal::OrderedField(CReal::Same, CReal::Lt, CReal::Le, CReal::add, CReal::mul).multiplicative.unit = 1 { refl }
        theorem creal_recip(x: CReal, h: x.Apart(0)):
            CReal::OrderedField(CReal::Same, CReal::Lt, CReal::Le, CReal::add, CReal::mul).recip(x, h) = x.inv(h := h) { refl }
        // `≤` at the reals is Bishop's by definition; at the rationals it is
        // the cross-multiplied one, reached through the instance's laws.
        theorem creal_le_is_not_lt(x, y: CReal, h: ¬(y < x)): x <= y { h }
        theorem rat_le_of_not_lt(x, y: Rat, h: ¬(y < x)): x <= y {
            Rat::StrictOrder(Rat::Same, Rat::Lt, Rat::Le).le_of_not_lt(x, y, h)
        }\n",
    );
    check(&mut e, "ordered_field_kit", &src);
}

// A predicate meets its own unfolding wherever it is written: a hypothesis
// of `Close` where `AbsLt` is expected, a bound passed as `Between`, and a
// result checked against the carrier's spelled-out order. The carrier, from
// the first point or a type argument, fills the indices through its
// designations; the unfolding is conversion's
// (issues/constrained-predicate-expected-type.md).
#[test]
fn an_unfolded_predicate_meets_its_name() {
    let mut e = base();
    check(
        &mut e,
        "unfolded_predicates",
        &format!(
            "{IMPORTS} theorem close_neg<A: OrderedAddGroup(≈, <, <=, +)>(x, y, e: A, h: Close(x, y, e)):
                AbsLt(A.inv(x + A.inv(y)), e)
            {{
                OrderedAddGroup::abs_lt_neg(x + A.inv(y), e, h)
            }}
            theorem bound_lt<A: OrderedAddGroup(≈, <, <=, +)>(x, e: A, h: AbsLt(x, e)): A.inv(e) < e {{
                StrictOrder::between_lt(A.inv(e), x, e, h)
            }}
            theorem rat_sum(x, y, e, d: Rat, hx: -e < x ∧ x < e, hy: -d < y ∧ y < d):
                -(e + d) < x + y ∧ x + y < e + d
            {{
                OrderedAddGroup::abs_lt_add(x, y, e, d, hx, hy)
            }}
            theorem creal_within(x, e: CReal, h: -e < x ∧ x < e): -e <= x ∧ x <= e {{
                LocatedAddGroup::abs_le_of_abs_lt(x, e, h)
            }}
            // A carrier given as a type argument pins the indices too.
            theorem rat_le_typed(x, y: Rat, h: x < y): x <= y {{ StrictOrder::le_of_lt<Rat>(x, y, h) }}
            theorem creal_le_typed(x, y: CReal, h: x < y): x <= y {{ StrictOrder::le_of_lt<CReal>(x, y, h) }}"
        ),
    );
    // The unfolding is checked, not assumed: the bound's two halves the
    // wrong way round are refused.
    refused(
        "unfolded_predicate_swapped",
        &format!(
            "{IMPORTS} theorem bad(x, y, e, d: Rat, hx: -e < x ∧ x < e, hy: -d < y ∧ y < d):
                x + y < e + d ∧ -(e + d) < x + y
            {{
                OrderedAddGroup::abs_lt_add(x, y, e, d, hx, hy)
            }}"
        ),
    );
}

#[test]
fn each_layer_is_refused_one_layer_down() {
    // `≤` is transitive only where `<` is located ...
    refused_with(
        "le_trans_needs_locatedness",
        &format!(
            "{IMPORTS} theorem bad<A: StrictOrder(≈, <, <=)>(x, y, z: A, h1: x <= y, h2: y <= z): x <= z {{
                PseudoOrder::le_trans(x, y, z, h1, h2)
            }}"
        ),
        "PseudoOrder<A>",
    );
    // ... and so is the mixed step from `<` through `≤`.
    refused_with(
        "mixed_step_needs_locatedness",
        &format!(
            "{IMPORTS} theorem bad<A: StrictOrder(≈, <, <=)>(x, y, z: A, h1: x < y, h2: y <= z): x < z {{
                PseudoOrder::lt_of_lt_of_le(x, y, z, h1, h2)
            }}"
        ),
        "PseudoOrder<A>",
    );
    // A bound's positivity needs the located group, not only the group.
    refused_with(
        "bound_pos_needs_locatedness",
        &format!(
            "{IMPORTS} theorem bad<A: OrderedAddGroup(≈, <, <=, +)>(x, e: A, h: AbsLt(x, e)): A.unit < e {{
                LocatedAddGroup::abs_lt_pos(x, e, h)
            }}"
        ),
        "no instance for `LocatedAddGroup<A>",
    );
    // The controls: one layer up, the same calls check; and open intervals,
    // tightness and the triangle inequality need no locatedness at all.
    let mut e = base();
    check(
        &mut e,
        "layer_controls",
        &format!(
            "{IMPORTS} theorem le_trans<A: PseudoOrder(≈, <, <=)>(x, y, z: A, h1: x <= y, h2: y <= z): x <= z {{
                PseudoOrder::le_trans(x, y, z, h1, h2)
            }}
            theorem bound_pos<A: LocatedAddGroup(≈, <, <=, +)>(x, e: A, h: AbsLt(x, e)): A.unit < e {{
                LocatedAddGroup::abs_lt_pos(x, e, h)
            }}
            theorem antisymm<A: StrictOrder(≈, <, <=)>(x, y: A, h1: x <= y, h2: y <= x): x ≈ y {{
                StrictOrder::le_antisymm(x, y, h1, h2)
            }}
            theorem triangle<A: OrderedAddGroup(≈, <, <=, +)>(x, y, e, d: A, hx: AbsLt(x, e), hy: AbsLt(y, d)):
                AbsLt(x + y, e + d)
            {{
                OrderedAddGroup::abs_lt_add(x, y, e, d, hx, hy)
            }}"
        ),
    );
}

#[test]
fn a_wrong_law_is_refused() {
    // `≤` is not a strict order: it is reflexive, so the irreflexivity law
    // cannot be filled.
    refused_with(
        "le_as_strict_order",
        &format!(
            "{IMPORTS} instance StrictOrder<Rat>(Rat::Same, Rat::Le, Rat::Le) {{
                lt_irrefl := Rat::lt_irrefl,
                lt_trans := λ x y z h1 h2 => Rat::le_trans(h1, h2),
                lt_respects := λ x x2 y y2 hx hy h => Rat::le_respects(hx, hy, h),
                lt_tight := λ x y h1 h2 => Rat::same_of_not_lt(h1, h2),
                le_of_not_lt := λ x y h => Rat::le_of_not_lt(h),
                not_lt_of_le := λ x y h => Rat::not_lt_of_le(h),
            }}"
        ),
        "Not(Le(x, x))",
    );
    // `≤` is not `<`, at any layer; the control is the same call at `≤`.
    refused(
        "le_is_not_lt",
        &format!(
            "{IMPORTS} theorem bad<A: OrderedField(≈, <, <=, +, *)>(x: A): x < x {{ StrictOrder::le_refl(x) }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "le_refl_control",
        &format!(
            "{IMPORTS} theorem ok<A: OrderedField(≈, <, <=, +, *)>(x: A): x <= x {{ StrictOrder::le_refl(x) }}"
        ),
    );
}

#[test]
fn the_inverse_wants_its_own_argument_apart() {
    // `0 < 1` is apartness of one, not of an arbitrary x.
    refused_with(
        "inverse_of_unrelated_proof",
        &format!(
            "{IMPORTS} fn bad<A: OrderedField(≈, <, <=, +, *)>(x: A) → A {{ A.recip(x, Inr(A.zero_lt_one)) }}"
        ),
        "is expected here",
    );
    // There is no inverse of zero to write: apartness of zero from itself is
    // refutable, so no proof reaches the field.
    refused(
        "inverse_without_proof",
        &format!("{IMPORTS} fn bad<A: OrderedField(≈, <, <=, +, *)>() → A {{ A.recip(A.unit) }}"),
    );
    // The inverse's sign is its argument's: a negative argument does not
    // give a positive inverse.
    refused(
        "inverse_sign_of_negative",
        &format!(
            "{IMPORTS} theorem bad<A: OrderedField(≈, <, <=, +, *)>(x: A, hx: x < A.unit): A.unit < A.recip(x, Inl(hx)) {{
                OrderedField::recip_pos(x, Inl(hx), hx)
            }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "inverse_control",
        &format!(
            "{IMPORTS} fn ok<A: OrderedField(≈, <, <=, +, *)>(x: A) → A {{ A.recip(A.multiplicative.unit, Inr(A.zero_lt_one)) }}
            theorem neg_recip<A: OrderedField(≈, <, <=, +, *)>(x: A, hx: x < A.unit): A.recip(x, Inl(hx)) < A.unit {{
                OrderedField::recip_neg(x, Inl(hx), hx)
            }}
            theorem zero_not_apart<A: OrderedField(≈, <, <=, +, *)>(x: A): ¬(ApartBy(<, A.unit, A.unit)) {{
                StrictOrder::apart_irrefl(A.unit)
            }}"
        ),
    );
}

#[test]
fn nothing_in_the_interface_decides() {
    // No layer carries trichotomy or a `≤` decider; `Rat` has both as extras,
    // `CReal` has neither.
    refused_with(
        "no_trichotomy",
        &format!(
            "{IMPORTS} theorem bad<A: OrderedField(≈, <, <=, +, *)>(x: A): x < A.unit ∨ x ≈ A.unit ∨ A.unit < x {{
                A.lt_trichotomy(x, A.unit)
            }}"
        ),
        "lt_trichotomy",
    );
    refused_with(
        "no_le_decider",
        &format!(
            "{IMPORTS} fn bad<A: OrderedField(≈, <, <=, +, *)>(x, y: A) → x <= y ∨ ¬(x <= y) {{ A.le_dec(x, y) }}"
        ),
        "le_dec",
    );
    let mut e = base();
    check(
        &mut e,
        "rat_decides_as_an_extra",
        &format!("{IMPORTS} fn ok(x, y: Rat) → x <= y ∨ ¬(x <= y) {{ x.le_dec(y) }}"),
    );
}

// The ordered layers extend the algebraic ones
// (issues/ordered-field-over-comm-ring.md): a `GroupRel` theorem applies to
// an ordered group, a `Ring` or `Semiring` theorem to an ordered field, and a
// generic ring theorem lands at `CReal` through its `CommRing` instance.
#[test]
fn the_ordered_layers_are_rings() {
    let mut e = base();
    check(
        &mut e,
        "ordered_layers_are_rings",
        &format!(
            "{IMPORTS} theorem group_neg_neg<A: OrderedAddGroup(≈, <, <=, +)>(x: A): A.inv(A.inv(x)) ≈ x {{
                GroupRel::inv_inv(+, x)
            }}
            theorem field_neg_mul<A: OrderedField(≈, <, <=, +, *)>(x, y: A): A.inv(x) * y ≈ A.inv(x * y) {{
                Ring::neg_mul(x, y)
            }}
            theorem field_mul_add_add<A: OrderedField(≈, <, <=, +, *)>(a, b, c, d: A):
                (a + b) * (c + d) ≈ (a * c + a * d) + (b * c + b * d)
            {{
                Semiring::mul_add_add(a, b, c, d)
            }}
            theorem field_mul_comm<A: OrderedField(≈, <, <=, +, *)>(x, y: A): x * y ≈ y * x {{
                A.commutative.comm(x, y)
            }}
            theorem creal_neg_mul_neg(x, y: CReal): -x * -y ≈ x * y {{ Ring::neg_mul_neg(x, y) }}
            theorem creal_interchange(a, b, c, d: CReal): (a * b) * (c * d) ≈ (a * c) * (b * d) {{
                CommMonoidRel::interchange(≈, *, a, b, c, d)
            }}"
        ),
    );
    // The reciprocal is `recip`: `inv` is the additive group's negation, one
    // argument and no apartness.
    refused(
        "inv_is_negation",
        &format!(
            "{IMPORTS} fn bad<A: OrderedField(≈, <, <=, +, *)>(x: A, h: ApartBy(<, x, A.unit)) → A {{ A.inv(x, h) }}"
        ),
    );
    // A ring theorem needs a ring: a located group has no product.
    refused(
        "ring_theorem_needs_a_ring",
        &format!(
            "{IMPORTS} theorem bad<A: LocatedAddGroup(≈, <, <=, +)>(x, y: A): A.inv(x) * y ≈ A.inv(x * y) {{
                Ring::neg_mul(x, y)
            }}"
        ),
    );
}
