//! `lib/std/num/rat.hthr` (`docs/setoid-rationals-round.md`): the refusals
//! that need the checker. Everything the language can state about rationals
//! is a theorem: the probes at specific values, the instance and `calc`
//! checks, and the `¬` theorems for the false claims a reader might expect
//! (`≈` is not `=`, `|x|` is not `x`, `≤` is not `<`) are
//! `lib/_tests/std/num/rat_tests.hthr`, which the whole-library gate checks
//! (`crates/cli/tests/library.rs`); the client showcase is a CLI-tier row of
//! `docs/showcase/showcases.tsv` (docs/test-value-audit.md §3.4, §3.5).
//!
//! What is left: lemmas cited at statements they do not prove (vacuity
//! controls), evidence searches that must fail (an inverse at zero or at an
//! unknown sign, a power at an unknown exponent, a zero or open denominator,
//! cancellation by zero), the checker's own `calc` and `rel_cong` refusals,
//! and the tactics reading fields of a record with a proof field.

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

const IMPORTS: &str = "import logic; import bool; import nat; import int; import algebra; import omega; import rat;
    import order; import relation_props; import algebra_rel;\n";

fn refused(name: &str, src: &str, why: Refusal) {
    support::assert_refused(&mut base(), name, &format!("{IMPORTS}{src}"), why);
}

/// Each lemma cited at a statement it does not prove: a law that became
/// trivially true (`≈` collapsing, a sign condition dropped) would let the
/// citation through.
#[test]
fn lemmas_are_cited_at_their_own_statements() {
    let cases = [
        "theorem bad(x, y: Rat): x + y ≈ x { Rat::add_comm(x, y) }",
        // `x ^ -1` is `x⁻¹`, not `x`.
        "theorem bad(x: Rat, h: x.Apart(0)): x ^ (-1) ≈ x { x.pow_neg_one() }",
        // A non-negative numerator gives no sign: 0/1 ≈ 0/2.
        "theorem bad(x, y: Rat, h: x ≈ y, hx: OfNat(0) <= x.num): OfNat(0) < y.num { Rat::num_pos_of_same(h, hx) }",
        // Every positive rational is above some 1/(n+1); zero is not.
        "theorem bad(): ∃ n: Nat, Rat::inv_succ(n) < 0 { Rat::archimedean_inv(0, Rat::le_refl(0)) }",
        // `mul_recip`'s hypothesis is `¬(x ≈ 0)`, which the identity does not prove.
        "theorem bad(x: Rat): x * x.recip() ≈ 1 { Rat::mul_recip(x, λ h => h) }",
    ];
    for (i, case) in cases.iter().enumerate() {
        refused(&format!("rat_bad_cite_{i}"), case, Refusal::Mismatch);
    }
}

/// Scaling preserves order only by a non-negative factor: `z.le_refl()` is
/// `z <= z`, not `0 <= z`. The parameter's type mentions the implicit `z`,
/// which the expected type solves; the argument's own type is still compared
/// with it (`issues/implicit-argument-mismatch-reaches-kernel.md`).
#[test]
fn scaling_needs_a_sign() {
    refused(
        "rat_scale_without_sign",
        "theorem bad(x, y, z: Rat, h: x <= y): x * z <= y * z { Rat::mul_le_mono_r(h, z.le_refl()) }",
        Refusal::Mismatch,
    );
}

/// `rel_cong` lifts a true step into a context only if the endpoints still
/// match; here the written right side drops the `+ x`.
#[test]
fn rel_cong_checks_its_context() {
    refused(
        "rat_wrong_cong",
        "theorem bad(x, y: Rat): (y + -y) + x ≈ 0 { rel_cong(Rat::add_neg(y)) }",
        Refusal::Says("`rel_cong` context mismatch"),
    );
}

/// The inverse has no value at 0: no apartness proof exists, so the search
/// for one fails, at a literal zero, at an unknown `x`, and from `¬(x = 0)`,
/// which at the pair's equality does not say `x` is not ≈ 0 (`Rat(0, 2)`).
/// `¬(x ≈ 0)` is read, through `Rat::apart_of_nonzero`
/// (docs/division-design.md).
#[test]
fn an_inverse_needs_apartness() {
    let cases = [
        "fn bad() → Rat { Rat::inv(0) }",
        "fn bad(x: Rat) → Rat { x⁻¹ }",
        "fn bad(x: Rat, h: ¬(x = 0)) → Rat { x⁻¹ }",
    ];
    for (i, case) in cases.iter().enumerate() {
        refused(&format!("rat_inverse_{i}"), case, Refusal::Says("no instance for `Apart("));
    }
}

/// An integer power's side condition computes from the exponent's sign: a
/// neutral exponent's is unknown, and a negative one needs apartness, which
/// zero and an unknown base lack.
#[test]
fn a_power_needs_its_side_condition() {
    let cases = [
        "fn bad(x: Rat, n: Int) → Rat { x ^ n }",
        "fn bad(x: Rat) → Rat { x ^ (-2) }",
        "fn bad() → Rat { 0 ^ (-1) }",
    ];
    for (i, case) in cases.iter().enumerate() {
        refused(&format!("rat_power_{i}"), case, Refusal::Says("no instance for `PowOk("));
    }
}

/// Cancellation is only by a positive: the side condition at 0 is not found.
#[test]
fn cancellation_is_only_by_a_positive() {
    refused(
        "int_cancel_zero",
        "theorem bad(x, y: Int, h: x * OfNat(0) = y * OfNat(0)): x = y { x.mul_cancel_pos_r(y, OfNat(0), h) }",
        Refusal::Says("no instance for `0 < 0`"),
    );
}

/// `den: Pos<Nat>` refuses a zero denominator and an open one.
#[test]
fn a_denominator_carries_its_positivity() {
    refused("rat_zero_den", "fn bad() → Rat { Rat(OfNat(1), 0) }", Refusal::Says("`den_pos` was left to its default"));
    refused("rat_open_den", "fn bad(k: Nat) → Rat { Rat(OfNat(1), k) }", Refusal::Says("`den_pos` was left to its default"));
}

/// `calc` over `<=` and `<`: a chain proves the strongest relation it used
/// and nothing stronger, each step's written relation and endpoints are
/// checked against its proof, and a pair the carrier does not register is a
/// missing instance.
#[test]
fn calc_chains_prove_no_more_than_their_steps() {
    let mismatches = [
        // Two `<=` steps do not make a `<`.
        "theorem bad(x, y, z: Rat, a: x <= y, b: y <= z): x < z { calc { x <= y := a, <= z := b } }",
        // A step's written relation is checked against its proof ...
        "theorem bad(x, y, z: Rat, a: x <= y, b: y <= z): x <= z { calc { x <= y := a, < z := b } }",
        // ... and so is every written endpoint, a single step's included.
        "theorem bad(x, y: Rat, a: x <= y): x <= y { calc { x <= x := a } }",
    ];
    for (i, case) in mismatches.iter().enumerate() {
        refused(&format!("rat_calc_{i}"), case, Refusal::Mismatch);
    }
    // Two bare local relations have no `Trans` between them.
    support::assert_refused(
        &mut base(),
        "calc_unregistered_pair",
        "import relation_props;
            theorem bad<A>(le as <=: A → A → Type, lt as <: A → A → Type,
                x, y, z: A, a: x <= y, b: y < z): x < z {
                calc { x <= y := a, < z := b }
            }",
        Refusal::Says("no instance for `Trans<A>("),
    );
}

#[test]
fn ring_and_omega_read_fields_of_a_record_with_a_proof_field() {
    // A record whose spine is dependent (a `Pos<Nat>` field's `den_pos`
    // mentions `den`) reads its fields through named projections, not the
    // inline walk; `ring` and `omega` must still read a field of a call that
    // computes to a constructor, or of a constructor written out. Varied: a
    // neutral and a literal receiver, a type-parameterised record (an open
    // element type), a checking position, and a wrong equation as the
    // control.
    let src = format!(
        "{IMPORTS} import ring; record Frac {{ num: Int, den: Pos<Nat> }}
        record Tagged<A> {{ tag: A, num: Int, den: Pos<Nat> }}
        fn Frac::mul(self x, y: Frac) → Frac {{ Frac(x.num * y.num, x.den * y.den) }}
        fn Frac::one() → Frac {{ Frac(OfNat(1), 1) }}
        fn Tagged::scale<A>(self t: Tagged<A>, k: Int) → Tagged<A> {{ Tagged(t.tag, t.num * k, t.den) }}
        theorem ring_num(x, y: Frac): x.mul(y).num = y.num * x.num {{ ring }}
        theorem omega_den(x, y: Frac): x.mul(y).den = x.den * y.den {{ omega }}
        theorem omega_literal(x: Int): Frac::one().num + x = x + OfNat(1) {{ omega }}
        theorem ring_literal(a, b: Int, p: Pos<Nat>): Frac(a * b, p).num = b * a {{ ring }}
        theorem open<A>(t: Tagged<A>, k: Int): t.scale(k).num = k * t.num {{ ring }}
        theorem checked(x, y: Frac): OfNat(0) <= x.mul(y).num - x.num * y.num {{
            let e: (x.mul(y).num = x.num * y.num) = ring;
            omega
        }}"
    );
    let mut e = base();
    if let Err(err) = e.elab_module_source("dependent_fields", &src) {
        panic!("{}", err.render(&src));
    }
    refused(
        "dependent_fields_wrong",
        "import ring; record Frac { num: Int, den: Pos<Nat> }
            fn Frac::mul(self x, y: Frac) → Frac { Frac(x.num * y.num, x.den * y.den) }
            theorem bad(x, y: Frac): x.mul(y).num = x.num + y.num { ring }",
        Refusal::Says("it is not an identity of commutative rings"),
    );
}
