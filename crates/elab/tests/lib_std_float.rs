//! The float modules (`lib/std/num/float/`, `docs/floating-point-design.md`):
//! the refusals that need the checker. Everything the language can state
//! about them is a theorem: the probes at specific values and the contract
//! restated at open ones are `lib/_tests/std/num/float/*_tests.hthr`, which
//! the whole-library gate checks (`crates/cli/tests/library.rs`), and the
//! zeros' inequality is `Finite::zeros_differ` (docs/test-value-audit.md §3.4,
//! §3.5).
//!
//! What is left are vacuity controls: each cites a lemma at a statement it
//! does not prove, so a relation that became trivially true (`RoundsTo`, a
//! sign, an error bound) would let the citation through. They are checker
//! behaviour, so they stay here, and each is refused as a checking mismatch,
//! not merely refused (`support::Refusal`). A wrong *literal* needs no
//! refusal: the probe at the right value already pins it.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support::{self, Refusal};

// lib-closure: error arith window literal
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
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("char", include_str!("../../../lib/std/text/char.hthr")),
    ("string", include_str!("../../../lib/std/text/string.hthr")),
    ("mono_laws", include_str!("../../../lib/std/tactic/mono_laws.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("order", include_str!("../../../lib/std/algebra/order.hthr")),
    ("semiring", include_str!("../../../lib/std/algebra/semiring.hthr")),
    ("ring", include_str!("../../../lib/std/tactic/ring.hthr")),
    ("ordered_field", include_str!("../../../lib/std/algebra/ordered_field.hthr")),
    ("linarith", include_str!("../../../lib/std/tactic/linarith.hthr")),
    ("big_operator", include_str!("../../../lib/std/algebra/big_operator.hthr")),
    ("rat", include_str!("../../../lib/std/num/rat.hthr")),
    ("lattice", include_str!("../../../lib/std/algebra/lattice.hthr")),
    ("dyadic", include_str!("../../../lib/std/num/float/dyadic.hthr")),
    ("float", include_str!("../../../lib/std/num/float/float.hthr")),
    ("round", include_str!("../../../lib/std/num/float/round.hthr")),
    ("error", include_str!("../../../lib/std/num/float/error.hthr")),
    ("arith", include_str!("../../../lib/std/num/float/arith.hthr")),
    ("window", include_str!("../../../lib/std/num/float/window.hthr")),
    ("literal", include_str!("../../../lib/std/num/float/literal.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const IMPORTS: &str = "import logic; import bool; import nat; import option; import list; import int; import omega; import rat;
    import dyadic; import float; import round; import error; import arith; import relation_props; import algebra_rel; import ordered_field;
    import literal;\n";

fn mismatches(prefix: &str, cases: &[&str]) {
    for (i, case) in cases.iter().enumerate() {
        support::assert_refused(&mut base(), &format!("{prefix}_{i}"), &format!("{IMPORTS}{case}"), Refusal::Mismatch);
    }
}

#[test]
fn arithmetic_lemmas_are_cited_at_their_own_statements() {
    mismatches("arith_bad", &[
        "theorem bad({F: Format}, a, b: Finite(F), mode: Mode): RoundsTo(F, mode, a.val() -b.val(), a.add(b, mode := mode)) { Finite::add_correct(a, b, mode) }",
        "theorem bad({F: Format}, a, b: Finite(F), mode: Mode): (a.mul(b, mode := mode)).SignIs(a.neg) { Finite::mul_sign(a, b, mode) }",
        "theorem bad({F: Format}, a: Finite(F)): a.sub(a) = Fin(Finite::zero(F, True)) { Finite::sub_self(a, NearestEven) }",
    ]);
}

/// `Float::div` at a format with no NaN: its defaulted evidence cannot be
/// built, and the refusal names the default.
#[test]
fn division_at_a_format_without_nan_needs_its_evidence() {
    support::assert_refused(
        &mut base(),
        "arith_div_no_nan",
        &format!("{IMPORTS} fn bad(x, y: Float(e2m1())) → Float(e2m1()) {{ Float::div(x, y) }}"),
        Refusal::Says("was left to its default"),
    );
}

#[test]
fn rounding_laws_are_cited_at_their_own_statements() {
    mismatches("round_bad_law", &[
        "theorem bad(F: Format, mode: Mode, x, y: Rat, xy: x <= y): Float::Le(F.round_rat(mode, y), F.round_rat(mode, x)) { F.round_rat_mono(mode, x, y, xy) }",
        "theorem bad(F: Format, mode: Mode, x: Rat): Float::Le(F.round_rat(TowardPos, x), F.round_rat(mode, x)) {
            F.rounds_ge_down(mode, x, F.round_rat(TowardPos, x), F.round_rat(mode, x), F.round_rat_correct(TowardPos, x), F.round_rat_correct(mode, x)) }",
        "theorem bad({F: Format}, f, s: Finite(F), t: f.neg = True, is: f.next_up() = Some(s)): s.H() = f.H() + Nat::pow(2, Succ(f.bexp)).int() {
            Finite::next_up_spacing(f, s, t, is) }",
        "theorem bad(F: Format, x: Rat): Float::Same(F.round_rat(NearestEven, x), F.round_rat(NearestAway, x)) {
            F.rounds_unique(NearestEven, x, F.round_rat(NearestEven, x), F.round_rat(NearestAway, x), F.round_rat_correct(NearestEven, x), F.round_rat_correct(NearestAway, x)) }",
    ]);
}

#[test]
fn rounding_correctness_is_cited_at_its_own_mode_and_value() {
    mismatches("round_bad_cite", &[
        "theorem bad(F: Format, x: Rat): RoundsTo(F, NearestEven, x, F.round_rat(NearestAway, x)) { F.round_rat_correct(NearestAway, x) }",
        "theorem bad(F: Format, x: Rat): RoundsTo(F, TowardPos, x, -F.round_rat(TowardPos, -x)) {
            F.rounds_neg(TowardPos, x, F.round_rat(TowardPos, -x), F.round_rat_correct(TowardPos, -x)) }",
        "theorem bad(F: Format, mode: Mode, x: Rat, h: Nat): RoundsTo(F, mode, x, F.round_h(mode, h, False)) {
            F.round_h_correct(mode, x, h, False, F.rat_approx(x)) }",
    ]);
}

#[test]
fn error_bounds_are_cited_at_their_own_statements() {
    mismatches("error_bad", &[
        "theorem bad({F: Format}, x: Rat, r: Finite(F), range: x.abs() <= (Finite::max_finite(F)).val(), hr: RoundsTo(F, TowardZero, x, Fin(r))):
            (r.val() -x).abs() <= F.err_at(NearestEven, x) { F.rounding_error(TowardZero, x, r, range, hr) }",
        "theorem bad({F: Format}, mode: Mode, x: Rat, r: Finite(F), small: x.abs() <= (Finite::min_normal(F)).val(), hr: RoundsTo(F, mode, x, Fin(r))):
            (r.val() -x).abs() <= F.u(mode) * x.abs() { F.subnormal_error(mode, x, r, small, hr) }",
        "theorem bad(F: Format, mode: Mode, m, n: Nat, ok: m + n < F.u_den(mode)):
            F.gamma(mode, m + n) <= F.gamma(mode, m) + F.gamma(mode, n) + F.gamma(mode, m) * F.gamma(mode, n) { F.gamma_add(mode, m, n, ok) }",
    ]);
}

/// Four roundings are more than e2m1's unit roundoff allows: `gamma_prod`'s
/// side condition is false at `n = 4`, so `trivial` does not discharge it.
#[test]
fn a_product_of_too_many_roundings_is_refused() {
    support::assert_refused(
        &mut base(),
        "error_bad_prod",
        &format!("{IMPORTS} theorem bad(d1, d2, d3, d4: Rat, h: List::AllAbsLe([d1, d2, d3, d4], e2m1().u(NearestEven))):
            (List::prod_one_add([d1, d2, d3, d4]) -1).abs() <= e2m1().gamma(NearestEven, 4)
            {{ e2m1().gamma_prod(NearestEven, [d1, d2, d3, d4], h, trivial) }}"),
        Refusal::Says("`trivial` proves `True`"),
    );
}

/// How many inexact-literal warnings `src` raises; it must check.
fn inexact_warnings(src: &str) -> usize {
    let mut e = base();
    e.elab_module_source("m", &format!("{IMPORTS}{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err}\n{src}"));
    e.take_warnings().iter().filter(|w| w.lint == heather_elab::Lint::InexactLiteral).count()
}

/// The warning is the carrier's `exact` bit, run: a decimal the format holds
/// is silent, one it rounds (or overflows) is not, and `Rat` holds them all.
#[test]
fn an_inexact_decimal_literal_draws_a_warning() {
    assert_eq!(inexact_warnings("fn a() → Float(binary64()) { 0.1 }"), 1);
    assert_eq!(inexact_warnings("fn a() → Float(binary16()) { 1e5 }"), 1);
    assert_eq!(inexact_warnings("fn a() → Float(binary64()) { 0.5 }"), 0);
    assert_eq!(inexact_warnings("fn a() → Float(binary32()) { 1e10 }"), 0);
    assert_eq!(inexact_warnings("fn a() → Rat { 0.1 }"), 0);
}

/// A hex float must be exact: one with a bit past the format's precision is
/// refused, and the refusal says so rather than spelling the obligation.
#[test]
fn an_unrepresentable_hex_float_is_refused() {
    support::assert_refused(
        &mut base(),
        "hex_inexact",
        &format!("{IMPORTS} fn bad() → Float(binary64()) {{ 0x1.00000000000008p0 }}"),
        Refusal::Says("a hex float must be exact"),
    );
}
