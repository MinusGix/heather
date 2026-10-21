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
//!     proof for a different value;
//!  4. part B: neighbours compute on a literal format (`next_up` across a
//!     binade, past the largest float, from below zero and from both zeros;
//!     `next_down` by negation), and uniqueness, exactness, the neighbour
//!     specification and spacing, bracketing and monotonicity hold at open
//!     values, with negative controls for a wrong neighbour, the reversed
//!     order, the wrong bracket side, spacing below zero and uniqueness
//!     across modes.

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

const IMPORTS: &str = "import logic; import bool; import nat; import option; import int; import omega; import rat;
    import dyadic; import float; import round; import relation_props; import algebra_rel; import ordered_field;
fn val_or({F: Format}, r: Float(F), d: Rat) → Rat { match r { Fin(f) => f.val(), Inf(_, _) => d, NaN(_) => d } }
fn neg_bit({F: Format}, r: Float(F)) → Bool { match r { Fin(f) => f.neg, Inf(n, _) => n, NaN(_) => False } }
fn opt_val({F: Format}, o: Option<Finite(F)>, d: Rat) → Rat { match o { Some(s) => s.val(), None => d } }
fn up_val({F: Format}, r: Float(F), d: Rat) → Rat { match r { Fin(f) => opt_val(f.next_up(), d), Inf(_, _) => d, NaN(_) => d } }
fn down_val({F: Format}, r: Float(F), d: Rat) → Rat { match r { Fin(f) => opt_val(f.next_down(), d), Inf(_, _) => d, NaN(_) => d } }
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

const NEIGHBOURS: &str = "
// e2m1's nonnegative floats: 0, 1/2, 1, 3/2, 2, 3, 4, 6.
theorem up_one(): Rat::Same(up_val(e2m1().round_rat(NearestEven, 1), 99), Rat(3, 2)) { refl }
theorem up_binade(): Rat::Same(up_val(e2m1().round_rat(NearestEven, Rat(3, 2)), 99), 2) { refl }
theorem up_wide(): Rat::Same(up_val(e2m1().round_rat(NearestEven, 4), 99), 6) { refl }
theorem up_top(): Rat::Same(up_val(e2m1().round_rat(NearestEven, 6), 99), 99) { refl }
theorem up_neg(): Rat::Same(up_val(e2m1().round_rat(NearestEven, -1), 99), Rat(-1, 2)) { refl }
theorem up_neg_wide(): Rat::Same(up_val(e2m1().round_rat(NearestEven, -6), 99), -4) { refl }
theorem up_zero(): Rat::Same(up_val(e2m1().round_rat(NearestEven, 0), 99), Rat(1, 2)) { refl }
theorem up_neg_zero(): Rat::Same(up_val(e2m1().round_rat(NearestEven, Rat(-1, 8)), 99), Rat(1, 2)) { refl }
theorem up_neg_least(): neg_bit(e2m1().round_rat(NearestEven, Rat(-1, 2))) = True { refl }
theorem down_one(): Rat::Same(down_val(e2m1().round_rat(NearestEven, 1), 99), Rat(1, 2)) { refl }
theorem down_zero(): Rat::Same(down_val(e2m1().round_rat(NearestEven, 0), 99), Rat(-1, 2)) { refl }
theorem down_bottom(): Rat::Same(down_val(e2m1().round_rat(NearestEven, -6), 99), 99) { refl }
theorem down_e3m2(): Rat::Same(down_val(e3m2().round_rat(NearestEven, 4), 99), Rat(7, 2)) { refl }
";

const LAWS: &str = "
theorem uniq(F: Format, mode: Mode, x: Rat, r, s: Float(F), hr: RoundsTo(F, mode, x, r), hs: RoundsTo(F, mode, x, s)): Float::Same(r, s) {
    F.rounds_unique(mode, x, r, s, hr, hs)
}
theorem only_round(F: Format, mode: Mode, x: Rat, r: Float(F), hr: RoundsTo(F, mode, x, r)): Float::Same(r, F.round_rat(mode, x)) { F.rounds_is_round_rat(mode, x, r, hr) }
theorem exact(F: Format, mode: Mode, f: Finite(F)): Float::Same(F.round_rat(mode, f.val()), Fin(f)) { F.round_rat_exact(mode, f) }
theorem exact_e5m2(f: Finite(e5m2())): RoundsTo(e5m2(), TowardZero, f.val(), Fin(f)) { e5m2().rounds_exact(TowardZero, f) }

// The neighbours, at an open float.
theorem up_spec({F: Format}, f: Finite(F)): Finite::IsNextUp(f, f.next_up()) { f.next_up_spec() }
theorem down_spec({F: Format}, f: Finite(F)): Finite::IsNextDown(f, f.next_down()) { f.next_down_spec() }
theorem up_least({F: Format}, f, s, g: Finite(F), is: f.next_up() = Some(s), lt: f.val() < g.val()): s.val() <= g.val() {
    (j(is, λ o _ => Finite::IsNextUp(f, o), f.next_up_spec())).right(g, lt)
}
theorem spacing({F: Format}, f, s: Finite(F), pos: f.neg = False, is: f.next_up() = Some(s)): s.H() = f.H() + Nat::pow(2, Succ(f.bexp)).int() {
    Finite::next_up_spacing(f, s, pos, is)
}
theorem gap(f, s: Finite(e4m3()), pos: f.neg = False, is: f.next_up() = Some(s)): s.val() ≈ f.val() + e4m3().grid(Nat::pow(2, Succ(f.bexp)).int()) {
    Finite::next_up_gap(f, s, pos, is)
}

// The mode laws.
theorem le_unfolds({F: Format}, f, g: Finite(F), h: Float::Le(F := F, a := Float::Fin(f), b := Float::Fin(g))): f.val() <= g.val() { h }
theorem bracket_lo(F: Format, mode: Mode, x: Rat): Float::Le(F.round_rat(TowardNeg, x), F.round_rat(mode, x)) {
    F.rounds_ge_down(mode, x, F.round_rat(TowardNeg, x), F.round_rat(mode, x), F.round_rat_correct(TowardNeg, x), F.round_rat_correct(mode, x))
}
theorem bracket_hi(F: Format, mode: Mode, x: Rat): Float::Le(F.round_rat(mode, x), F.round_rat(TowardPos, x)) {
    F.rounds_le_up(mode, x, F.round_rat(mode, x), F.round_rat(TowardPos, x), F.round_rat_correct(mode, x), F.round_rat_correct(TowardPos, x))
}
theorem mono(F: Format, mode: Mode, x, y: Rat, xy: x <= y): Float::Le(F.round_rat(mode, x), F.round_rat(mode, y)) { F.round_rat_mono(mode, x, y, xy) }
theorem mono_fin_ne({F: Format}, x, y: Rat, xy: x <= y, f, g: Finite(F), hf: RoundsTo(F, NearestEven, x, Fin(f)), hg: RoundsTo(F, NearestEven, y, Fin(g))): f.val() <= g.val() {
    F.rounds_mono(NearestEven, x, y, xy, Fin(f), Fin(g), hf, hg)
}
theorem faithful({F: Format}, mode: Mode, x: Rat, f: Finite(F), h: RoundsTo(F, mode, x, Fin(f))): Finite::Below(x, f) ∨ Finite::Above(x, f) {
    F.rounds_faithful(mode, x, f, h)
}
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
fn neighbours_compute() {
    let mut e = base();
    check(&mut e, "round_neighbours", &format!("{IMPORTS}{NEIGHBOURS}"));
}

#[test]
fn mode_laws_hold_at_open_values() {
    let mut e = base();
    check(&mut e, "round_laws", &format!("{IMPORTS}{LAWS}"));
}

#[test]
fn a_wrong_neighbour_or_law_is_refused() {
    for (i, bad) in [
        "theorem bad(): Rat::Same(up_val(e2m1().round_rat(NearestEven, 1), 99), 2) { refl }",
        "theorem bad(): Rat::Same(down_val(e2m1().round_rat(NearestEven, 0), 99), 0) { refl }",
        "theorem bad(): Rat::Same(up_val(e2m1().round_rat(NearestEven, 6), 99), 8) { refl }",
        "theorem bad(F: Format, mode: Mode, x, y: Rat, xy: x <= y): Float::Le(F.round_rat(mode, y), F.round_rat(mode, x)) { F.round_rat_mono(mode, x, y, xy) }",
        "theorem bad(F: Format, mode: Mode, x: Rat): Float::Le(F.round_rat(TowardPos, x), F.round_rat(mode, x)) {
            F.rounds_ge_down(mode, x, F.round_rat(TowardPos, x), F.round_rat(mode, x), F.round_rat_correct(TowardPos, x), F.round_rat_correct(mode, x)) }",
        "theorem bad({F: Format}, f, s: Finite(F), t: f.neg = True, is: f.next_up() = Some(s)): s.H() = f.H() + Nat::pow(2, Succ(f.bexp)).int() {
            Finite::next_up_spacing(f, s, t, is) }",
        "theorem bad(F: Format, x: Rat): Float::Same(F.round_rat(NearestEven, x), F.round_rat(NearestAway, x)) {
            F.rounds_unique(NearestEven, x, F.round_rat(NearestEven, x), F.round_rat(NearestAway, x), F.round_rat_correct(NearestEven, x), F.round_rat_correct(NearestAway, x)) }",
    ]
    .iter()
    .enumerate()
    {
        refused(&format!("round_bad_law_{i}"), &format!("{IMPORTS}{bad}"));
    }
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
