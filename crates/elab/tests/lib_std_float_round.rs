//! `lib/std/float/round.hthr` — rounding an exact value to a format
//! (`docs/floating-point-design.md` §5, roadmap submilestone
//! `float-rounding`).
//!
//!  1. literal roundings compute by evaluation on small formats: ties to
//!     even and away, the carry into the next binade, saturation where a
//!     format has no infinity, the IEEE overflow threshold where it has one,
//!     the conjugate mode on negative values, signed zeros, and a sticky
//!     non-dyadic value;
//!  2. the correctness theorems hold at an open format, mode and value, and
//!     the relation unfolds at a literal mode over a neutral result in a
//!     checking position;
//!  3. negative controls: a wrong neighbour, a wrong overflow verdict and a
//!     wrong sign of zero are refused, and so are a correctness proof cited
//!     at the wrong mode, sign symmetry without the conjugate, and a cut
//!     proof for a different value.

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
    (
        "ordered_field",
        include_str!("../../../lib/std/ordered_field.hthr"),
    ),
    ("semiring", include_str!("../../../lib/std/semiring.hthr")),
    ("rat", include_str!("../../../lib/std/rat.hthr")),
    ("dyadic", include_str!("../../../lib/std/float/dyadic.hthr")),
    ("float", include_str!("../../../lib/std/float/float.hthr")),
    ("round", include_str!("../../../lib/std/float/round.hthr")),
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
    import dyadic; import float; import round; import relation_props; import algebra_rel; import ordered_field;
fn val_or({F: Format}, r: Float(F), d: Rat) → Rat { match r { Fin(f) => f.val(), Inf(_, _) => d, NaN(_) => d } }
fn neg_bit({F: Format}, r: Float(F)) → Bool { match r { Fin(f) => f.neg, Inf(n, _) => n, NaN(_) => False } }
";

const LITERAL: &str = "

// Ties: to even, away from zero, and the directed modes.
theorem e2m1_tie_even(): Rat::Same(val_or(e2m1().round_rat(NearestEven, Rat(5, 4)), 99), 1) { refl }
theorem e2m1_tie_away(): Rat::Same(val_or(e2m1().round_rat(NearestAway, Rat(5, 4)), 99), Rat(3, 2)) { refl }
theorem e2m1_up(): Rat::Same(val_or(e2m1().round_rat(TowardPos, Rat(5, 4)), 99), Rat(3, 2)) { refl }
theorem e2m1_down(): Rat::Same(val_or(e2m1().round_rat(TowardNeg, Rat(5, 4)), 99), 1) { refl }
theorem e2m1_carry(): Rat::Same(val_or(e2m1().round_rat(NearestEven, Rat(7, 4)), 99), 2) { refl }
theorem e2m1_tie5(): Rat::Same(val_or(e2m1().round_rat(NearestEven, 5), 99), 4) { refl }
theorem e2m1_tie5a(): Rat::Same(val_or(e2m1().round_rat(NearestAway, 5), 99), 6) { refl }
// No infinity: saturation.
theorem e2m1_sat(): Rat::Same(val_or(e2m1().round_rat(NearestEven, 7), 99), 6) { refl }
theorem e2m1_sat_up(): Rat::Same(val_or(e2m1().round_rat(TowardPos, 100), 99), 6) { refl }
// Negative values round under the conjugate mode.
theorem e2m1_neg_down(): Rat::Same(val_or(e2m1().round_rat(TowardNeg, Rat(-5, 4)), 99), Rat(-3, 2)) { refl }
theorem e2m1_neg_up(): Rat::Same(val_or(e2m1().round_rat(TowardPos, Rat(-5, 4)), 99), -1) { refl }
theorem e2m1_neg_zero(): neg_bit(e2m1().round_rat(NearestEven, Rat(-1, 8))) = True { refl }
theorem e2m1_pos_zero(): neg_bit(e2m1().round_rat(NearestEven, 0)) = False { refl }
// Sticky: 1/3 is past the midpoint 1/4 between 0 and 1/2.
theorem e2m1_third(): Rat::Same(val_or(e2m1().round_rat(NearestEven, Rat(1, 3)), 99), Rat(1, 2)) { refl }
theorem e2m1_third_z(): Rat::Same(val_or(e2m1().round_rat(TowardZero, Rat(1, 3)), 99), 0) { refl }
// Dyadic rounding by shifting.
theorem e3m2_dy(): Rat::Same(val_or(e3m2().round_dyadic(NearestEven, Dyadic(13, -2)), 99), 3) { refl }
theorem e3m2_dy2(): Rat::Same(val_or(e3m2().round_dyadic(NearestEven, Dyadic(29, -3)), 99), Rat(7, 2)) { refl }
theorem e5m2_ovf(): (e5m2().round_dyadic(NearestEven, Dyadic(15, 12))).is_inf() = True { refl }
theorem e5m2_below_ovf(): Rat::Same(val_or(e5m2().round_dyadic(NearestEven, Dyadic(61439, 0)), 99), 57344) { refl }
theorem e5m2_up_ovf(): (e5m2().round_dyadic(TowardPos, Dyadic(57345, 0))).is_inf() = True { refl }
theorem e5m2_neg_ovf(): neg_bit(e5m2().round_dyadic(TowardNeg, Dyadic(-1, 20))) = True { refl }
theorem e5m2_z_sat(): Rat::Same(val_or(e5m2().round_dyadic(TowardZero, Dyadic(1, 20)), 99), 57344) { refl }
theorem e4m3_sat(): Rat::Same(val_or(e4m3().round_dyadic(NearestEven, Dyadic(1, 10)), 99), 448) { refl }
theorem e4m3_top(): Rat::Same(val_or(e4m3().round_dyadic(NearestEven, Dyadic(465, 0)), 99), 448) { refl }
";

const OPEN: &str = "
// Correct at an open format, mode and value.
theorem any_rat(F: Format, mode: Mode, x: Rat): RoundsTo(F, mode, x, F.round_rat(mode, x)) { F.round_rat_correct(mode, x) }
theorem any_dyadic(F: Format, mode: Mode, d: Dyadic): RoundsTo(F, mode, d.rat(), F.round_dyadic(mode, d)) { F.round_dyadic_correct(mode, d) }
theorem any_cut(F: Format, mode: Mode, x: Rat, h: Nat, st: Bool, a: F.Approx(x, h, st)): RoundsTo(F, mode, x, F.round_h(mode, h, st)) { F.round_h_correct(mode, x, h, st, a) }
theorem e5m2_ne(x: Rat): RoundsTo(e5m2(), NearestEven, x, e5m2().round_rat(NearestEven, x)) { e5m2().round_rat_correct(NearestEven, x) }

// The relation unfolds at a literal mode over a neutral result, in checking position.
theorem ne_nearest({F: Format}, x: Rat, f: Finite(F), r: RoundsTo(F, NearestEven, x, Fin(f))): Finite::Nearest(x, f) { r.left.left }
theorem away_fits(x: Rat, f: Finite(e5m2()), r: RoundsTo(e5m2(), NearestAway, x, Fin(f))): e5m2().Fits(x) { r.right }
theorem tz_cases({F: Format}, x: Rat, f: Finite(F), r: RoundsTo(F, TowardZero, x, Fin(f)), nn: 0 <= x): Finite::Below(x, f) { r.left(nn) }
theorem flip({F: Format}, mode: Mode, x: Rat, r: Float(F), h: RoundsTo(F, mode.conj(), -x, r)): RoundsTo(F, mode, x, -r) { F.rounds_neg(mode, x, r, h) }

// The directed roundings compute at a neutral cut.
theorem down_is_down(F: Format, h: Nat, st: Bool): F.round_h(TowardNeg, h, st) = Fin(F.down(h)) { refl }
theorem zero_is_down(F: Format, h: Nat, st: Bool): F.round_h(TowardZero, h, st) = Fin(F.down(h)) { refl }
theorem up_sticky(F: Format, h: Nat): F.round_h(TowardPos, h, True) = F.up_or_over(h, F.up(h)) { refl }
theorem conj_neg(F: Format, h: Nat, st: Bool): F.round_signed(TowardPos, True, h, st) = -F.round_h(TowardNeg, h, st) { refl }
";

#[test]
fn literal_roundings_compute() {
    let mut e = base();
    check(&mut e, "round_literal", &format!("{IMPORTS}{LITERAL}"));
}

#[test]
fn rounding_is_correct_at_open_values() {
    let mut e = base();
    check(&mut e, "round_open", &format!("{IMPORTS}{OPEN}"));
}

#[test]
fn a_wrong_literal_rounding_is_refused() {
    for (i, bad) in [
        "theorem bad(): Rat::Same(val_or(e2m1().round_rat(NearestEven, Rat(5, 4)), 99), Rat(3, 2)) { refl }",
        "theorem bad(): Rat::Same(val_or(e2m1().round_rat(NearestAway, Rat(7, 4)), 99), Rat(3, 2)) { refl }",
        "theorem bad(): (e5m2().round_dyadic(NearestEven, Dyadic(61439, 0))).is_inf() = True { refl }",
        "theorem bad(): neg_bit(e2m1().round_rat(NearestEven, Rat(-1, 8))) = False { refl }",
        "theorem bad(): Rat::Same(val_or(e2m1().round_rat(TowardPos, Rat(1, 3)), 99), 0) { refl }",
    ]
    .iter()
    .enumerate()
    {
        refused(&format!("round_bad_literal_{i}"), &format!("{IMPORTS}{bad}"));
    }
}

#[test]
fn correctness_is_cited_at_its_own_mode_and_value() {
    refused(
        "round_wrong_mode",
        &format!("{IMPORTS} theorem bad(F: Format, x: Rat): RoundsTo(F, NearestEven, x, F.round_rat(NearestAway, x)) {{ F.round_rat_correct(NearestAway, x) }}"),
    );
    refused(
        "round_no_conjugate",
        &format!(
            "{IMPORTS} theorem bad(F: Format, x: Rat): RoundsTo(F, TowardPos, x, -F.round_rat(TowardPos, -x)) {{
                F.rounds_neg(TowardPos, x, F.round_rat(TowardPos, -x), F.round_rat_correct(TowardPos, -x)) }}"
        ),
    );
    refused(
        "round_other_cut",
        &format!(
            "{IMPORTS} theorem bad(F: Format, mode: Mode, x: Rat, h: Nat): RoundsTo(F, mode, x, F.round_h(mode, h, False)) {{
                F.round_h_correct(mode, x, h, False, F.rat_approx(x)) }}"
        ),
    );
}
