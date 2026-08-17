//! `lib/std/nat.hthr`'s arithmetic tail: `min`/`max`, the `sub` kit beyond
//! `sub_zero`, and the lemmas where the order meets the arithmetic
//! (`issues/nat-arithmetic-kit.md`).
//!
//! The module checking is not the assertion — every `.hthr` under `lib/` is
//! checked somewhere already. What is asserted here is what the issue's
//! acceptance names and what a test that only checked the module would miss:
//!
//! - §1 `min`/`max` **reduce** at closed arguments, which is the property
//!   every recursion in that file is written to keep;
//! - §2 they reduce at an **open** argument on the side they descend on, and
//!   are stuck on the other — the currying is a claim about which argument
//!   moves, so it gets a control;
//! - §3 the `sub` kit, including the one lemma that needs a *hypothesis* and a
//!   control that the hypothesis is load-bearing;
//! - §4 monotonicity and cancellation at open arguments, and the round trip
//!   that says they are inverse.
//!
//! Every positive has a negative control beside it, per
//! `docs/testing-generated-terms.md`: most of the positives below would pass
//! against a `max` that returned its second argument, and the controls are
//! what rule that out.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [("logic", LOGIC), ("bool", BOOL), ("nat", NAT)] {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => format!("{name}: {msg}"),
                other => format!("{name}: {other}"),
            });
        }
    }
    if !extra.is_empty() {
        let src = format!("import logic;\nimport bool;\nimport nat;\n{extra}");
        if let Err(err) = e.elab_module_source("probe", &src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
    }
    Ok(e)
}

fn ok(extra: &str) {
    run(extra).unwrap_or_else(|e| panic!("expected this to check, got: {e}"));
}

fn bad(extra: &str) -> String {
    match run(extra) {
        Err(e) => e,
        Ok(_) => panic!("expected a refusal, but it checked"),
    }
}

// ---------------------------------------------------------------------------
// 1. `min`/`max` reduce at closed arguments. This is the issue's acceptance
//    verbatim, and it is what a `theorem`-spelled or decider-driven pick would
//    have cost (`docs/nat-order-design.md` §2's `le_dec` note).

#[test]
fn min_and_max_reduce_at_closed_arguments() {
    ok("theorem a(): max(2, 5) = 5 { refl }
theorem b(): max(5, 2) = 5 { refl }
theorem c(): min(2, 5) = 2 { refl }
theorem d(): min(5, 2) = 2 { refl }
theorem e(): max(0, 0) = 0 { refl }
theorem f(): sub(5)(2) = 3 { refl }
theorem g(): sub(2)(5) = 0 { refl }");
}

/// The control without which the test above is worthless: reduction has to
/// reach the *right* value. A `max` that returned its second argument and a
/// `min` that returned its first would both satisfy §1 alone.
#[test]
fn min_and_max_do_not_reduce_to_the_wrong_side() {
    bad("theorem t(): max(2, 5) = 2 { refl }");
    bad("theorem t(): min(2, 5) = 5 { refl }");
}

// ---------------------------------------------------------------------------
// 2. The open-argument axis (`docs/testing-generated-terms.md`), which for
//    these two functions is also the *asymmetry* axis: both descend on their
//    first argument, so `max(0, n)` reduces at open `n` and `max(n, 0)` is
//    stuck. Pinned in both directions because the currying is a design claim
//    (`issues/ih-generalization.md` forces it) and a reader should be able to
//    see which side it puts the reduction on.

#[test]
fn min_and_max_reduce_at_an_open_second_argument() {
    ok("theorem t(n: Nat): max(0, n) = n { refl }
theorem u(n: Nat): min(0, n) = 0 { refl }");
}

/// The other side is stuck, and *not* because the fact is false — it is true
/// at every `n`, it just needs an induction rather than a conversion. If this
/// starts passing, something has learned to reduce a `match` on a variable and
/// the note above is out of date.
#[test]
fn the_descending_argument_is_the_first_one() {
    bad("theorem t(n: Nat): max(n, 0) = n { refl }");
    bad("theorem t(n: Nat): min(n, 0) = 0 { refl }");
}

/// The lattice kit at open arguments: the four bounds, the two universal
/// properties, and the two order-decided equations. Nothing here can be
/// discharged by reduction, which is the point of applying all of it to
/// variables.
#[test]
fn the_lattice_kit_composes_at_open_arguments() {
    ok("theorem a(x, y: Nat): x <= max(x)(y) { le_max_l(x)(y) }
theorem b(x, y: Nat): y <= max(x)(y) { le_max_r(x)(y) }
theorem c(x, y: Nat): min(x)(y) <= x { min_le_l(x)(y) }
theorem d(x, y: Nat): min(x)(y) <= y { min_le_r(x)(y) }
theorem e(x, y, z: Nat, h1: x <= z, h2: y <= z): max(x)(y) <= z { max_le(x)(y, z, h1, h2) }
theorem f(x, y, z: Nat, h1: z <= x, h2: z <= y): z <= min(x)(y) { le_min(x)(y, z, h1, h2) }
theorem g(x, y: Nat, h: x <= y): max(x)(y) = y { max_eq_r(x)(y, h) }
theorem h(x, y: Nat, h: x <= y): min(x)(y) = x { min_eq_l(x)(y, h) }");
}

/// The controls for the two lemmas above whose statement has a side to get
/// wrong: `max_eq_r` picks the *larger*, and `max_le` needs a bound on **both**
/// arguments and not the same one twice.
#[test]
fn the_order_decided_equations_pick_the_right_side() {
    bad("theorem t(x, y: Nat, h: x <= y): max(x)(y) = x { max_eq_r(x)(y, h) }");
    bad("theorem t(x, y, z: Nat, h: x <= z): max(x)(y) <= z { max_le(x)(y, z, h, h) }");
}

/// A **checking** position rather than a computation (the axis
/// `docs/testing-generated-terms.md` names third): `min`/`max` inside a `fn`
/// body whose type is fixed from outside, with a proof about the composite
/// checked against a goal mentioning the `fn` and not its unfolding. `clamp`
/// is the smallest real consumer of both at once.
#[test]
fn min_and_max_check_inside_a_composite() {
    ok("fn clamp(lo, hi, x: Nat) -> Nat { max(lo, min(hi, x)) }
theorem above(lo, hi, x: Nat): lo <= clamp(lo, hi, x) { le_max_l(lo)(min(hi)(x)) }
theorem below(lo, hi, x: Nat, h: lo <= hi): clamp(lo, hi, x) <= hi {
    max_le(lo)(min(hi)(x), hi, h, min_le_l(hi)(x))
}
theorem at_closed(): clamp(2, 7, 9) = 7 { refl }
theorem inside_the_band(): clamp(2, 7, 5) = 5 { refl }
theorem below_the_band(): clamp(2, 7, 0) = 2 { refl }");
}

// ---------------------------------------------------------------------------
// 3. The `sub` kit. `add_sub_cancel` is unconditional and `sub_add_cancel` is
//    not, and the difference is truncation — so the hypothesis gets a control.

#[test]
fn the_sub_kit_composes_at_open_arguments() {
    ok("theorem a(n: Nat): sub(n)(n) = 0 { sub_self(n) }
theorem b(n, m: Nat): sub(add(n, m))(m) = n { add_sub_cancel(n, m) }
theorem c(n, m: Nat, h: n <= m): add(sub(m)(n), n) = m { sub_add_cancel(n, m, h) }
theorem d(m, n: Nat): sub(m)(n) <= m { sub_le(m)(n) }");
}

/// `sub_add_cancel`'s hypothesis is load-bearing: without a comparison there is
/// nothing to supply it with, and `trivial` does not stand in for one (the
/// order is a relation, not a `= True` equation — `docs/nat-order-design.md`
/// §3). The second line is why the hypothesis exists at all: truncation loses
/// the difference outright, so the unconditional statement is *false*.
#[test]
fn the_conditional_cancellation_needs_its_comparison() {
    bad("theorem t(n, m: Nat): add(sub(m)(n), n) = m { sub_add_cancel(n, m, trivial) }");
    bad("theorem t(): add(sub(2)(5), 5) = 2 { refl }");
    ok("theorem why(): sub(2)(5) = 0 { refl }");
}

// ---------------------------------------------------------------------------
// 4. Monotonicity and cancellation, all at open arguments — a closed instance
//    of any of these is decided by reduction and would assert nothing.

#[test]
fn monotonicity_composes_at_open_arguments() {
    ok("theorem a(x, y, k: Nat, h: x <= y): add(x, k) <= add(y, k) { add_le_mono_r(k)(x, y, h) }
theorem b(x, y, k: Nat, h: x <= y): add(k, x) <= add(k, y) { add_le_mono_l(k, x, y, h) }
theorem c(x, y, z, w: Nat, h1: x <= y, h2: z <= w): add(x, z) <= add(y, w) {
    add_le_mono(x, y, z, w, h1, h2)
}
theorem d(x, y, k: Nat, h: x <= y): mul(x, k) <= mul(y, k) { mul_le_mono_r(k)(x, y, h) }
theorem e(x, y, k: Nat, h: x <= y): mul(k, x) <= mul(k, y) { mul_le_mono_l(k, x, y, h) }
theorem f(x, y, z, w: Nat, h1: x <= y, h2: z <= w): mul(x, z) <= mul(y, w) {
    mul_le_mono(x, y, z, w, h1, h2)
}");
}

#[test]
fn cancellation_composes_at_open_arguments() {
    ok("theorem a(x, y, k: Nat, h: add(x, k) <= add(y, k)): x <= y { le_of_add_le_add_r(k)(x, y, h) }
theorem b(x, y, k: Nat, h: add(k, x) <= add(k, y)): x <= y { le_of_add_le_add_l(k, x, y, h) }");
}

/// The two controls monotonicity most needs: the conclusion is not symmetric,
/// and `mul`'s cancellation is **not** in the kit — `le_of_add_le_add_r` is
/// about `add` and does not accept a product, which is the refusal that says
/// so. (Cancelling a factor is false at `k = 0` and wants a `0 < k`
/// hypothesis; that is a different lemma, not this one's mirror.)
#[test]
fn monotonicity_does_not_run_backwards_or_over_products() {
    bad("theorem t(x, y, z, w: Nat, h1: x <= y, h2: z <= w): add(y, w) <= add(x, z) {
    add_le_mono(x, y, z, w, h1, h2)
}");
    bad("theorem t(x, y, k: Nat, h: mul(x, k) <= mul(y, k)): x <= y { le_of_add_le_add_r(k)(x, y, h) }");
}

/// Monotonicity and cancellation are inverse, asserted by composing them at
/// open arguments in both orders. This is the one test here that would catch a
/// pair of lemmas that were each individually provable but stated about
/// different sides.
#[test]
fn monotonicity_and_cancellation_round_trip() {
    ok("theorem there_and_back(x, y, k: Nat, h: x <= y): x <= y {
    le_of_add_le_add_r(k)(x, y, add_le_mono_r(k)(x, y, h))
}
theorem back_and_there(x, y, k: Nat, h: add(k, x) <= add(k, y)): add(k, x) <= add(k, y) {
    add_le_mono_l(k, x, y, le_of_add_le_add_l(k, x, y, h))
}");
}
