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
//!   that says they are inverse;
//! - §5 `pow` and `fact` (`issues/nat-pow-and-fact.md`), whose laws are
//!   `mul`'s kit read one level up, and whose two order facts are
//!   `mul_le_mono` applied to themselves.
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

#[test]
fn div_and_mod_reduce_together_at_closed_arguments() {
    ok("theorem a(): div(0, 3) = 0 { refl }
theorem b(): mod(0, 3) = 0 { refl }
theorem c(): div(7, 3) = 2 { refl }
theorem d(): mod(7, 3) = 1 { refl }
theorem e(): div(9, 3) = 3 { refl }
theorem f(): mod(9, 3) = 0 { refl }
theorem g(): div(5, 1) = 5 { refl }
theorem h(): mod(5, 1) = 0 { refl }
theorem i(): div(5, 0) = 0 { refl }
theorem j(): mod(5, 0) = 5 { refl }");
}

#[test]
fn div_and_mod_do_not_compute_to_neighboring_values() {
    bad("theorem t(): div(7, 3) = 3 { refl }");
    bad("theorem t(): mod(7, 3) = 0 { refl }");
    bad("theorem t(): mod(5, 0) = 0 { refl }");
}

#[test]
fn div_and_mod_euclidean_laws_compose_at_open_arguments() {
    ok(
        "theorem reconstruct(n, d: Nat): div(n, d) * d + mod(n, d) = n {
    div_mul_add_mod(n, d)
}
theorem bounded(n, d: Nat, h: 0 < d): mod(n, d) < d {
    mod_lt(n, d, h)
}
theorem quotient_at_zero(n: Nat): div(n, 0) = 0 { div_zero(n) }
theorem remainder_at_zero(n: Nat): mod(n, 0) = n { mod_zero(n) }",
    );
}

#[test]
fn the_positive_divisor_hypothesis_is_load_bearing() {
    bad("theorem t(n, d: Nat): mod(n, d) < d { mod_lt(n, d, trivial) }");
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

// ---------------------------------------------------------------------------
// 5. `pow` and `fact`. Both compute, both have a kit that is `mul`'s read one
//    level up, and both have exactly one order fact — which is where the
//    section above pays for itself.

#[test]
fn pow_and_fact_compute() {
    ok("theorem a(): pow(2, 5) = 32 { refl }
theorem b(): pow(3, 3) = 27 { refl }
theorem c(): pow(5, 0) = 1 { refl }
theorem d(): pow(0, 4) = 0 { refl }
theorem e(): fact(0) = 1 { refl }
theorem f(): fact(5) = 120 { refl }");
}

#[test]
fn pow_and_fact_compute_the_right_values() {
    bad("theorem t(): pow(2, 5) = 64 { refl }");
    bad("theorem t(): fact(5) = 100 { refl }");
}

/// The exponent endpoints, and the asymmetry between them: `pow(a, 0)` is
/// `refl` at **open** `a` because the definition descends on the exponent,
/// while `pow(a, 1)` is not — it is `mul(1, a)`, which descends on `a` — so it
/// costs a lemma. The control is what records that this is a real difference
/// and not an oversight in the kit.
#[test]
fn the_exponent_endpoints_are_not_symmetric() {
    ok("theorem zero(a: Nat): pow(a, 0) = 1 { refl }
theorem one(a: Nat): pow(a, 1) = a { pow_one(a) }
theorem base_one(n: Nat): pow(1, n) = 1 { one_pow(n) }");
    bad("theorem t(a: Nat): pow(a, 1) = a { refl }");
}

/// The three laws at open arguments, where none of them can be discharged by
/// reduction — asserted by the controls below, which try exactly that.
#[test]
fn the_pow_laws_compose_at_open_arguments() {
    ok("theorem adds(a, b, c: Nat): pow(a, add(b, c)) = mul(pow(a, b), pow(a, c)) {
    pow_add(a, b, c)
}
theorem muls(a, b, c: Nat): pow(a, mul(b, c)) = pow(pow(a, b), c) { pow_mul(a, b, c) }
theorem over_a_product(a, b, n: Nat): pow(mul(a, b), n) = mul(pow(a, n), pow(b, n)) {
    mul_pow(a, b, n)
}
theorem exchange(x, y, z, w: Nat): mul(mul(x, y), mul(z, w)) = mul(mul(x, z), mul(y, w)) {
    mul_shuffle(x, y, z, w)
}");
}

#[test]
fn the_pow_laws_are_not_definitional() {
    bad("theorem t(a, b, c: Nat): pow(a, add(b, c)) = mul(pow(a, b), pow(a, c)) { refl }");
    bad("theorem t(a, b, n: Nat): pow(mul(a, b), n) = mul(pow(a, n), pow(b, n)) { refl }");
}

/// The order facts, at open arguments and through the hypothesis. `one_le_pow`
/// is the one lemma here that a reader might expect to hold unconditionally.
#[test]
fn the_order_facts_hold_at_open_arguments() {
    ok("theorem pos(a, n: Nat, h: 1 <= a): 1 <= pow(a, n) { one_le_pow(a, n, h) }
theorem fac(n: Nat): 1 <= fact(n) { one_le_fact(n) }
theorem step(n: Nat): fact(n) <= fact(Succ(n)) { fact_le_succ(n) }
theorem chained(n: Nat): fact(n) <= fact(Succ(Succ(n))) {
    le_trans(fact(n))(fact(Succ(n)), fact(Succ(Succ(n))), fact_le_succ(n), fact_le_succ(Succ(n)))
}");
}

/// `one_le_pow`'s hypothesis is load-bearing and the base `0` is why: `pow` at
/// base zero is zero at every positive exponent, so the unconditional reading
/// is false. Both the open attempt (no comparison to supply) and the closed
/// counterexample are pinned, because the second is what makes the first more
/// than a typing accident.
#[test]
fn positivity_needs_its_base_hypothesis() {
    bad("theorem t(n: Nat): 1 <= pow(0, n) { one_le_pow(0, n, trivial) }");
    let e = bad("theorem t(): 1 <= pow(0, 3) { trivial }");
    // `False` rather than the kernel's `Empty`: the display spells the surface
    // name (docs/surface-type-display-design.md).
    assert!(e.contains("False"), "expected the refuted comparison to be falsity, got: {e}");
    ok("theorem why(): pow(0, 3) = 0 { refl }");
}
