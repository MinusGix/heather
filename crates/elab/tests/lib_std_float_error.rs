//! `lib/std/float/error.hthr` — rounding error bounds
//! (`docs/floating-point-design.md` §5.3 and §13, roadmap submilestone
//! `float-error`).
//!
//!  1. the constants compute on literal formats: unit roundoff per mode, the
//!     subnormal bound `η`, `γ(n)`, and the ulp and error bound at a literal
//!     value, in the subnormal range, inside a binade and past a binade's top;
//!  2. the bounds hold at an open format, mode and value, are cited at the
//!     executable rounding, and unfold at a literal mode in a checking
//!     position; the γ algebra composes rounding factors over a list of open
//!     values;
//!  3. negative controls: a directed error claimed at the nearest bound, the
//!     relative bound from the subnormal one, a wrong unit roundoff, the γ
//!     inequality reversed, and a product of more roundings than `u` allows.

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
    ("dyadic", include_str!("../../../lib/std/float/dyadic.hthr")),
    ("float", include_str!("../../../lib/std/float/float.hthr")),
    ("round", include_str!("../../../lib/std/float/round.hthr")),
    ("error", include_str!("../../../lib/std/float/error.hthr")),
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

const IMPORTS: &str = "import logic; import bool; import nat; import option; import list; import int; import omega; import rat;
    import dyadic; import float; import round; import error; import relation_props; import algebra_rel; import ordered_field;
";

// e2m1's floats are 0, 0.5, 1, 1.5, 2, 3, 4 and 6 (qmin = -1, half-unit
// 1/4); binary16 and binary32 check the constants at real sizes.
const LITERAL: &str = "
theorem u_near(): Rat::Same(e2m1().u(NearestEven), Rat(1, 4)) { refl }
theorem u_dir(): Rat::Same(e2m1().u(TowardZero), Rat(1, 2)) { refl }
theorem u_half(): Rat::Same(binary16().u(NearestAway), Rat(1, 2048)) { refl }
theorem u_single(): Rat::Same(binary32().u(NearestEven), Rat(1, 16777216)) { refl }
theorem eta_near(): Rat::Same(e2m1().eta(NearestEven), Rat(1, 4)) { refl }
theorem eta_dir(): Rat::Same(e2m1().eta(TowardPos), Rat(1, 2)) { refl }
theorem gamma_two(): Rat::Same(e2m1().gamma(NearestEven, 2), 1) { refl }
theorem gamma_half(): Rat::Same(binary16().gamma(NearestEven, 3), Rat(3, 2045)) { refl }
theorem ulp_sub(): Rat::Same(e2m1().ulp_at(Rat(1, 4)), Rat(1, 2)) { refl }
theorem ulp_mid(): Rat::Same(e2m1().ulp_at(Rat(5, 2)), 1) { refl }
theorem ulp_neg(): Rat::Same(e2m1().ulp_at(Rat(-5, 2)), 1) { refl }
theorem ulp_top(): Rat::Same(e2m1().ulp_at(5), 2) { refl }
theorem err_mid(): Rat::Same(e2m1().err_at(NearestEven, Rat(5, 2)), Rat(1, 2)) { refl }
theorem err_dir(): Rat::Same(e2m1().err_at(TowardNeg, Rat(5, 2)), 1) { refl }
";

const OPEN: &str = "
theorem err({F: Format}, mode: Mode, x: Rat, r: Finite(F), range: x.abs() <= (Finite::max_finite(F)).val(), hr: RoundsTo(F, mode, x, Fin(r))):
    (r.val() -x).abs() <= F.err_at(mode, x) { F.rounding_error(mode, x, r, range, hr) }
theorem in_ulps({F: Format}, mode: Mode, x: Rat, r: Finite(F), range: x.abs() <= (Finite::max_finite(F)).val(), hr: RoundsTo(F, mode, x, Fin(r))):
    (r.val() -x).abs() <= F.ulp_at(x) { Rat::le_trans(F.rounding_error(mode, x, r, range, hr), F.err_le_ulp(mode, x)) }
theorem half_ulp(F: Format, x: Rat): F.err_at(NearestEven, x) + F.err_at(NearestEven, x) ≈ F.ulp_at(x) { F.err_half_ulp(True, x) }
theorem at_round_rat(F: Format, x: Rat, r: Finite(F), range: x.abs() <= (Finite::max_finite(F)).val(),
    normal: (Finite::min_normal(F)).val() <= x.abs(), is: F.round_rat(NearestEven, x) = Fin(r)): ∃ d: Rat, d.abs() <= F.u(NearestEven) ∧ r.val() ≈ x * (1 + d)
{
    F.standard_model(NearestEven, x, r, range, normal, j(is, λ v _ => RoundsTo(F, NearestEven, x, v), F.round_rat_correct(NearestEven, x)))
}
theorem unfolds(F: Format): F.u(NearestEven) ≈ Rat(1, F.top()) {
    let h: (F.u(NearestEven) ≈ Rat(1, F.top())) = refl;
    h
}
theorem rel({F: Format}, mode: Mode, x: Rat, r: Finite(F), range: x.abs() <= (Finite::max_finite(F)).val(),
    normal: (Finite::min_normal(F)).val() <= x.abs(), hr: RoundsTo(F, mode, x, Fin(r))): (r.val() -x).abs() <= F.u(mode) * x.abs()
{
    F.relative_error(mode, x, r, range, normal, hr)
}
theorem sub({F: Format}, mode: Mode, x: Rat, r: Finite(F), small: x.abs() <= (Finite::min_normal(F)).val(), hr: RoundsTo(F, mode, x, Fin(r))):
    (r.val() -x).abs() <= F.eta(mode) { F.subnormal_error(mode, x, r, small, hr) }
theorem both({F: Format}, mode: Mode, x: Rat, r: Finite(F), range: x.abs() <= (Finite::max_finite(F)).val(), hr: RoundsTo(F, mode, x, Fin(r))):
    (r.val() -x).abs() <= F.u(mode) * x.abs() + F.eta(mode) { F.error_bound(mode, x, r, range, hr) }
theorem compose(F: Format, mode: Mode, a, b: Rat, m, n: Nat, ok: m + n < F.u_den(mode), ha: a.abs() <= F.gamma(mode, m), hb: b.abs() <= F.gamma(mode, n)):
    ((1 + a) * (1 + b) -1).abs() <= F.gamma(mode, m + n) { F.theta_mul(mode, m, n, ok, ha, hb) }
theorem grows(F: Format, mode: Mode, m, n: Nat, mn: m <= n, ok: n < F.u_den(mode)): F.gamma(mode, m) <= F.gamma(mode, n) { F.gamma_mono(mode, m, n, mn, ok) }
theorem three(d1, d2, d3: Rat, h1: d1.abs() <= e5m2().u(NearestEven), h2: d2.abs() <= e5m2().u(NearestEven), h3: d3.abs() <= e5m2().u(NearestEven)):
    (List::prod_one_add([d1, d2, d3]) -1).abs() <= e5m2().gamma(NearestEven, 3)
{
    e5m2().gamma_prod(NearestEven, [d1, d2, d3], And(h1, And(h2, And(h3, trivial))), trivial)
}
";

#[test]
fn constants_compute_on_literal_formats() {
    let mut e = base();
    check(&mut e, "error_literal", &format!("{IMPORTS}{LITERAL}"));
}

#[test]
fn bounds_hold_at_open_values() {
    let mut e = base();
    check(&mut e, "error_open", &format!("{IMPORTS}{OPEN}"));
}

#[test]
fn a_wrong_bound_is_refused() {
    for (i, bad) in [
        "theorem bad({F: Format}, x: Rat, r: Finite(F), range: x.abs() <= (Finite::max_finite(F)).val(), hr: RoundsTo(F, TowardZero, x, Fin(r))):
            (r.val() -x).abs() <= F.err_at(NearestEven, x) { F.rounding_error(TowardZero, x, r, range, hr) }",
        "theorem bad({F: Format}, mode: Mode, x: Rat, r: Finite(F), small: x.abs() <= (Finite::min_normal(F)).val(), hr: RoundsTo(F, mode, x, Fin(r))):
            (r.val() -x).abs() <= F.u(mode) * x.abs() { F.subnormal_error(mode, x, r, small, hr) }",
        "theorem bad(F: Format, mode: Mode, m, n: Nat, ok: m + n < F.u_den(mode)):
            F.gamma(mode, m + n) <= F.gamma(mode, m) + F.gamma(mode, n) + F.gamma(mode, m) * F.gamma(mode, n) { F.gamma_add(mode, m, n, ok) }",
        "theorem bad(): Rat::Same(e2m1().u(TowardZero), Rat(1, 4)) { refl }",
        "theorem bad(): Rat::Same(e2m1().err_at(NearestEven, Rat(5, 2)), 1) { refl }",
        "theorem bad(d1, d2, d3, d4: Rat, h: List::AllAbsLe([d1, d2, d3, d4], e2m1().u(NearestEven))):
            (List::prod_one_add([d1, d2, d3, d4]) -1).abs() <= e2m1().gamma(NearestEven, 4)
            { e2m1().gamma_prod(NearestEven, [d1, d2, d3, d4], h, trivial) }",
    ]
    .iter()
    .enumerate()
    {
        refused(&format!("error_bad_{i}"), &format!("{IMPORTS}{bad}"));
    }
}
