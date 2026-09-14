//! `lib/std/int.hthr` — the integer module, checked on its own
//! (`issues/std-int-encoding.md` and `issues/std-int-order-completion.md`,
//! waves I and I-prime of `issues/std-api-waves.md`).
//!
//! Nothing else in the library imports `int`, so without this binary the file
//! would be checked by nothing at all. The coverage split is the one
//! `lib_std_list.rs` established, plus explicit negative controls:
//!
//!  1. the closure checks (the module and everything it imports);
//!  2. the law kit is *there* — named one by one, because a law deleted rather
//!     than broken is a change test 1 cannot see;
//!  3. the API computes at closed arguments, in both signs, and the operators
//!     and class instances resolve at `Int` in a file that ALSO imports `nat`
//!     (the whole point of the designations);
//!  4. false decisions/equations are refused, so test 3 is not vacuous;
//!  5. multiplication monotonicity cannot be used at a negative factor.
//!
//! `int` imports `algebra` (it registers its own instances), so the prefix here
//! is the whole of `lib/std`.

use heather_elab::{ElabError, Elaborator, Lint};

mod support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");

fn elaborated(cached: bool) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let load = |e: &mut Elaborator| {
        for (name, src) in [
            ("logic", LOGIC), ("bool", BOOL), ("nat", NAT),
            ("option", OPTION), ("pair", PAIR), ("list", LIST),
            ("algebra", ALGEBRA), ("int", INT),
        ] {
            if let Err(err) = e.elab_module_source(name, src) {
                let msg = match err {
                    ElabError::Elab { msg, .. } => msg,
                    other => format!("{other}"),
                };
                panic!("{name} did not check: {msg}");
            }
        }
    };
    if cached {
        support::with_decl_cache(&mut e, load);
    } else {
        load(&mut e);
    }
    e
}

fn probe(name: &str, src: &str) {
    let mut e = elaborated(true);
    if let Err(err) = e.elab_module_source("probe", src) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("{name}: {msg}");
    }
}

#[test]
fn the_int_module_checks() {
    let mut e = elaborated(false);
    assert!(
        INT.contains("match le_dec(a, b) as λ d => a <= or_pick(d, a, b)")
            && INT.contains("match le_dec(a, b) as λ d => b <= or_pick(d, a, b)")
            && INT.contains("match le_dec(a, b) as λ d => c <= or_pick(d, b, a)"),
        "the three kernel-required motives remain explicit"
    );
    assert!(
        e.take_warnings().iter().all(|w| w.lint != Lint::RedundantMatchMotive),
        "a motive whose omission elaborates but fails the local kernel check is retained"
    );
}

/// The kits requested by waves I and I-prime, stated at OPEN integers so that
/// nothing here is answered by computation: `neg`, `add`, `sub`, `mul` with
/// their laws, the group and ring facts, the completed order/lattice kit, and
/// the `Nat` embedding.
///
/// Every name is applied rather than counted. Two entries are the ones to read
/// first: `mul_add_distr` is the law that made the round's `mul_isucc`/
/// `mul_ipred` pair necessary, and `add_le_mono_r` is the only lemma here that
/// spends the order kit and the arithmetic kit at once.
#[test]
fn the_law_kit_is_present() {
    probe(
        "the law kit did not apply",
        r#"
import int;
import nat;
import logic;

theorem i_neg_neg(a: Int): int::neg(int::neg(a)) = a { int::neg_neg(a) }
theorem i_add_comm(a, b: Int): int::add(a, b) = int::add(b, a) { int::add_comm(a, b) }
theorem i_add_assoc(a, b, c: Int): int::add(int::add(a, b), c) = int::add(a, int::add(b, c)) { int::add_assoc(a, b, c) }
theorem i_add_zero(a: Int): int::add(a, OfNat(0)) = a { int::add_zero(a) }
theorem i_zero_add(a: Int): int::add(OfNat(0), a) = a { int::zero_add(a) }
theorem i_add_neg(a: Int): int::add(a, int::neg(a)) = OfNat(0) { int::add_neg(a) }
theorem i_neg_add(a, b: Int): int::neg(int::add(a, b)) = int::add(int::neg(a), int::neg(b)) { int::neg_add(a, b) }
theorem i_sub_self(a: Int): int::sub(a, a) = OfNat(0) { int::sub_self(a) }
theorem i_neg_unique(x, y: Int, h: int::add(x, y) = OfNat(0)): y = int::neg(x) { int::neg_unique(x, y, h) }

theorem i_mul_comm(a, b: Int): int::mul(a, b) = int::mul(b, a) { int::mul_comm(a, b) }
theorem i_mul_assoc(a, b, c: Int): int::mul(int::mul(a, b), c) = int::mul(a, int::mul(b, c)) { int::mul_assoc(a, b, c) }
theorem i_mul_one(a: Int): int::mul(a, OfNat(1)) = a { int::mul_one(a) }
theorem i_mul_zero(a: Int): int::mul(a, OfNat(0)) = OfNat(0) { int::mul_zero(a) }
theorem i_mul_neg_r(a, b: Int): int::mul(a, int::neg(b)) = int::neg(int::mul(a, b)) { int::mul_neg_r(a, b) }
theorem i_mul_neg_l(a, b: Int): int::mul(int::neg(a), b) = int::neg(int::mul(a, b)) { int::mul_neg_l(a, b) }
theorem i_mul_isucc(a, x: Int): int::mul(a, int::isucc(x)) = int::add(int::mul(a, x), a) { int::mul_isucc(a, x) }
theorem i_distr(a, b, c: Int): int::mul(a, int::add(b, c)) = int::add(int::mul(a, b), int::mul(a, c)) {
    int::mul_add_distr(a, b, c)
}
theorem i_distr_r(a, b, c: Int): int::mul(int::add(a, b), c) = int::add(int::mul(a, c), int::mul(b, c)) {
    int::add_mul_distr(a, b, c)
}

theorem i_le_refl(a: Int): a <= a { int::le_refl(a) }
theorem i_le_trans(a, b, c: Int, h1: a <= b, h2: b <= c): a <= c { int::le_trans(a)(b, c, h1, h2) }
theorem i_le_antisym(a, b: Int, h1: a <= b, h2: b <= a): a = b { int::le_antisym(a)(b, h1, h2) }
theorem i_le_total(a, b: Int): Or<int::Le(a, b), int::Le(b, a)> { int::le_total(a, b) }
theorem i_le_dec(a, b: Int): Or<int::Le(a, b), ¬ int::Le(a, b)> { int::le_dec(a, b) }
theorem i_le_of_not_le(a, b: Int, h: ¬ int::Le(a, b)): b <= a { int::le_of_not_le(a, b, h) }
theorem i_lt_irrefl(a: Int): ¬ int::Lt(a, a) { int::lt_irrefl(a) }
theorem i_le_of_lt(a, b: Int, h: int::Lt(a, b)): a <= b { int::le_of_lt(a)(b, h) }
theorem i_lt_trichotomy(a, b: Int): a < b ∨ a = b ∨ b < a { int::lt_trichotomy(a, b) }
theorem i_lt_trans(a, b, c: Int, h1: a < b, h2: b < c): a < c { int::lt_trans(a, b, c, h1, h2) }
theorem i_lt_of_lt_of_le(a, b, c: Int, h1: a < b, h2: b <= c): a < c {
    int::lt_of_lt_of_le(a, b, c, h1, h2)
}
theorem i_lt_of_le_of_lt(a, b, c: Int, h1: a <= b, h2: b < c): a < c {
    int::lt_of_le_of_lt(a, b, c, h1, h2)
}
theorem i_lt_of_le_of_ne(a, b: Int, h1: a <= b, h2: ¬ (a = b)): a < b {
    int::lt_of_le_of_ne(a, b, h1, h2)
}
theorem i_lt_asymm(a, b: Int, h: a < b): ¬ (b < a) { int::lt_asymm(a, b, h) }
theorem i_le_of_not_lt(a, b: Int, h: ¬ (a < b)): b <= a { int::le_of_not_lt(a, b, h) }
theorem i_lt_of_not_le(a, b: Int, h: ¬ (b <= a)): a < b { int::lt_of_not_le(a, b, h) }
theorem i_le_isucc(a, b: Int, h: a <= b): int::isucc(a) <= int::isucc(b) { int::le_isucc(a)(b, h) }
theorem i_le_ipred(a, b: Int, h: a <= b): int::ipred(a) <= int::ipred(b) { int::le_ipred(a)(b, h) }
theorem i_le_neg(a, b: Int, h: a <= b): int::neg(b) <= int::neg(a) { int::le_neg(a)(b, h) }
theorem i_add_le_mono_r(a, b, c: Int, h: a <= b): int::add(a, c) <= int::add(b, c) {
    int::add_le_mono_r(a, b, c, h)
}
theorem i_add_le_mono_l(a, b, c: Int, h: a <= b): int::add(c, a) <= int::add(c, b) {
    int::add_le_mono_l(a, b, c, h)
}
theorem i_add_le_mono(a, b, c, d: Int, h1: a <= b, h2: c <= d): a + c <= b + d {
    int::add_le_mono(a, b, c, d, h1, h2)
}
theorem i_mul_le_mono_r(a, b, k: Int, h1: a <= b, h2: OfNat(0) <= k): a * k <= b * k {
    int::mul_le_mono_r(a, b, k, h1, h2)
}
theorem i_mul_le_mono_l(a, b, k: Int, h1: a <= b, h2: OfNat(0) <= k): k * a <= k * b {
    int::mul_le_mono_l(a, b, k, h1, h2)
}

theorem i_le_max_l(a, b: Int): a <= int::max(a, b) { int::le_max_l(a, b) }
theorem i_le_max_r(a, b: Int): b <= int::max(a, b) { int::le_max_r(a, b) }
theorem i_min_le_l(a, b: Int): int::min(a, b) <= a { int::min_le_l(a, b) }
theorem i_min_le_r(a, b: Int): int::min(a, b) <= b { int::min_le_r(a, b) }
theorem i_max_le(a, b, c: Int, h1: a <= c, h2: b <= c): int::max(a, b) <= c {
    int::max_le(a, b, c, h1, h2)
}
theorem i_le_min(a, b, c: Int, h1: c <= a, h2: c <= b): c <= int::min(a, b) {
    int::le_min(a, b, c, h1, h2)
}
theorem i_max_eq_r(a, b: Int, h: a <= b): int::max(a, b) = b { int::max_eq_r(a, b, h) }
theorem i_max_eq_l(a, b: Int, h: b <= a): int::max(a, b) = a { int::max_eq_l(a, b, h) }
theorem i_min_eq_l(a, b: Int, h: a <= b): int::min(a, b) = a { int::min_eq_l(a, b, h) }
theorem i_min_eq_r(a, b: Int, h: b <= a): int::min(a, b) = b { int::min_eq_r(a, b, h) }

theorem i_ofNat_add(m, n: Nat): OfNat(nat::add(m, n)) = int::add(OfNat(m), OfNat(n)) {
    int::ofNat_add(m, n)
}
theorem i_ofNat_mul(m, n: Nat): OfNat(nat::mul(m, n)) = int::mul(OfNat(m), OfNat(n)) {
    int::ofNat_mul(m, n)
}
theorem i_ofNat_le(m, n: Nat): Iff<nat::Le(m, n), int::Le(OfNat(m), OfNat(n))> {
    int::ofNat_le_iff(m, n)
}
theorem i_toNat(a: Int, h: OfNat(0) <= a): OfNat(int::toNat(a)) = a { int::ofNat_toNat(a)(h) }
theorem i_int_ind(P: Int -> Type, z: P(OfNat(0)),
                  up: (k: Nat) -> P(OfNat(k)) -> P(OfNat(Succ(k))),
                  d: P(NegSucc(0)),
                  dn: (k: Nat) -> P(NegSucc(k)) -> P(NegSucc(Succ(k))), a: Int): P(a) {
    int::int_ind(P, z, up, d, dn, a)
}
"#,
    );
}

/// The API *computes*, and the operators and instances resolve at `Int` in a
/// file that imports `nat` too — which is the property the four designations
/// beside their operations in `int.hthr` exist for, and the one a reader would
/// otherwise have to take on trust. Both signs on both sides of every operation, since a
/// sign-blind bug survives any test that stays non-negative.
///
/// Note what has to be qualified and what does not: `int::add` and `nat::add`
/// are both in scope unqualified and are therefore ambiguous *by name*, while
/// `x + y` is not ambiguous at all — the carrier of the operand picks the
/// designation (`docs/operators-onto-classes-design.md`).
#[test]
fn the_api_computes_and_the_operators_resolve() {
    probe(
        "the API did not compute",
        r#"
import int;
import nat;
import list;
import logic;
import algebra;

theorem c_add_pp(): int::add(OfNat(2), OfNat(3)) = OfNat(5) { refl }
theorem c_add_pn(): int::add(OfNat(2), NegSucc(4)) = NegSucc(2) { refl }
theorem c_add_np(): int::add(NegSucc(1), OfNat(5)) = OfNat(3) { refl }
theorem c_add_nn(): int::add(NegSucc(1), NegSucc(2)) = NegSucc(4) { refl }
theorem c_sub_under(): int::sub(OfNat(3), OfNat(8)) = NegSucc(4) { refl }
theorem c_sub_over(): int::sub(OfNat(8), OfNat(3)) = OfNat(5) { refl }
theorem c_neg_p(): int::neg(OfNat(4)) = NegSucc(3) { refl }
theorem c_neg_n(): int::neg(NegSucc(3)) = OfNat(4) { refl }
theorem c_neg_zero(): int::neg(OfNat(0)) = OfNat(0) { refl }
fn c_positive_numeral() -> Int { 4 }
fn c_negative_numeral() -> Int { -4 }
fn c_as_int(a: Int) -> Int { a }
fn c_negative_argument() -> Int { c_as_int(-1) }
fn c_nested_negative_argument() -> Int { c_as_int(--1) }
fn c_nested_numeral_anchor(a: Int) -> Int { let b = -(1 + a); b }
fn c_generic_numeral<A: Numeral>() -> A { 1 }
fn c_literal_left_infers_from_sibling(a: Int) -> Int { let x = 3 + a; x }
theorem c_positive_numeral_computes(): c_positive_numeral() = OfNat(4) { refl }
theorem c_negative_numeral_computes(): c_negative_numeral() = NegSucc(3) { refl }
theorem c_negative_argument_computes(): c_negative_argument() = NegSucc(0) { refl }
theorem c_negative_zero_literal(): c_as_int(-0) = OfNat(0) { refl }
theorem c_negative_radix_literal(): c_as_int(-0x10) = NegSucc(15) { refl }
theorem c_nested_negative_argument_computes(): c_nested_negative_argument() = OfNat(1) { refl }
theorem c_nested_numeral_anchor_open(a: Int):
    c_nested_numeral_anchor(a) = int::neg(int::add(OfNat(1), a)) { refl }
theorem c_generic_int_numeral(): c_generic_numeral<Int>() = OfNat(1) { refl }
theorem c_generic_nat_numeral(): c_generic_numeral<Nat>() = 1 { refl }
theorem c_positive_literal_equation(): 4 = OfNat(4) { refl }
theorem c_negative_literal_equation(): -4 = NegSucc(3) { refl }
theorem c_literal_arithmetic_equation(): 2 + 3 = OfNat(5) { refl }
theorem c_literal_left_computes(): c_literal_left_infers_from_sibling(OfNat(2)) = OfNat(5) { refl }
theorem c_prefix_neg_open(a: Int): -a = int::neg(a) { refl }
theorem c_prefix_neg_positive(): -OfNat(4) = NegSucc(3) { refl }
theorem c_prefix_neg_negative(): -NegSucc(3) = OfNat(4) { refl }
theorem c_prefix_neg_nested(a: Int): --a = a { int::neg_neg(a) }
theorem c_prefix_neg_precedence(a, b: Int): -a * b = int::mul(int::neg(a), b) { refl }
theorem c_mul_pp(): int::mul(OfNat(2), OfNat(3)) = OfNat(6) { refl }
theorem c_mul_pn(): int::mul(OfNat(2), NegSucc(2)) = NegSucc(5) { refl }
theorem c_mul_np(): int::mul(NegSucc(1), OfNat(3)) = NegSucc(5) { refl }
theorem c_mul_nn(): int::mul(NegSucc(1), NegSucc(2)) = OfNat(6) { refl }
theorem c_mul_zero(): int::mul(NegSucc(7), OfNat(0)) = OfNat(0) { refl }
theorem c_toNat(): int::toNat(NegSucc(3)) = 0 { refl }

// the order decides by computing, in all four sign combinations
theorem c_le_pp(): OfNat(2) <= OfNat(7) { trivial }
theorem c_le_nn(): NegSucc(9) <= NegSucc(0) { trivial }
theorem c_le_np(): NegSucc(9) <= OfNat(0) { trivial }
theorem c_not_le_pn(): ¬ (OfNat(0) <= NegSucc(0)) { λ (h: OfNat(0) <= NegSucc(0)) => h }
theorem c_lt(): int::Lt(NegSucc(0), OfNat(0)) { trivial }
theorem c_max_mixed(): int::max(NegSucc(2), OfNat(1)) = OfNat(1) { refl }
theorem c_max_negative(): int::max(NegSucc(2), NegSucc(5)) = NegSucc(2) { refl }
theorem c_min_mixed(): int::min(OfNat(3), NegSucc(1)) = NegSucc(1) { refl }
theorem c_min_positive(): int::min(OfNat(3), OfNat(7)) = OfNat(3) { refl }

// the operators at BOTH carriers, in one file, with neither qualified
theorem c_op_int(a, b: Int): a + b = b + a { int::add_comm(a, b) }
theorem c_op_nat(m, n: Nat): m + n = n + m { nat::add_comm(m, n) }
theorem c_op_int_mul(a, b: Int): a * b = b * a { int::mul_comm(a, b) }
theorem c_op_le_int(a: Int): a <= a { int::le_refl(a) }
theorem c_op_lt_int(a: Int): a < int::isucc(a) { int::lt_isucc_self(a) }
theorem c_op_lt_nat(n: Nat): n < Succ(n) { nat::lt_succ_self(n) }

// the instances, reached by resolution: the commutative monoid's generic law,
// the monoid fold at `List<Int>`, the group's inverse-uniqueness, and `Cmp`
theorem c_unit(a: Int): a + OfNat(0) = a { op_unit_of_comm(a) }
theorem c_sum(): sum_all(Cons(OfNat(2), Cons(NegSucc(0), Nil))) = OfNat(1) { refl }
theorem c_inv(x, y: Int, h: int::add(x, y) = OfNat(0)): y = int::neg(x) {
    op_inv_unique(x, y, h)
}

theorem c_max(a: Int): max_of(a, a) = a { max_of_self(a) }
theorem c_max_computes(): max_of(NegSucc(2), OfNat(1)) = OfNat(1) { refl }
"#,
    );
}

/// A closed sum costs one `Nat` operation on the payloads, not the
/// magnitude: `add` is the four sign cases over `nat::add` and the
/// synchronous `subNatNat`, both of which the kernel iterates over runs in
/// one program application (issues/int-arithmetic-over-nat-primitives.md).
/// Every quadrant at `2^63`/`2^64`, including the mixed ones that used to
/// peel one `ipred` per unit, and `sub` through `neg`. The negative control
/// is the false-equation test below, which refuses at small operands; here
/// the cost is the datum, and a wrong answer would fail `refl`.
#[test]
fn addition_at_machine_magnitudes_costs_a_payload_operation() {
    probe(
        "large integer addition did not compute",
        r#"
import int;
import nat;

theorem big_sub(): int::sub(OfNat(nat::pow(2, 63)), OfNat(nat::pow(2, 64))) = NegSucc(nat::sub(nat::pow(2, 63), 1)) { refl }
theorem big_sub_over(): int::sub(OfNat(nat::pow(2, 64)), OfNat(nat::pow(2, 63))) = OfNat(nat::pow(2, 63)) { refl }
theorem big_add(): int::add(OfNat(nat::pow(2, 63)), OfNat(nat::pow(2, 63))) = OfNat(nat::pow(2, 64)) { refl }
theorem big_neg_neg(): int::add(NegSucc(nat::pow(2, 63)), NegSucc(nat::pow(2, 63))) = NegSucc(nat::add(nat::pow(2, 64), 1)) { refl }
theorem big_mixed(): int::add(NegSucc(nat::pow(2, 63)), OfNat(nat::pow(2, 64))) = OfNat(nat::sub(nat::pow(2, 63), 1)) { refl }
theorem big_mixed_under(): int::add(OfNat(nat::pow(2, 63)), NegSucc(nat::pow(2, 64))) = NegSucc(nat::pow(2, 63)) { refl }
theorem big_cancel(): int::sub(OfNat(nat::pow(2, 64)), OfNat(nat::pow(2, 64))) = OfNat(0) { refl }
"#,
    );
}

#[test]
fn euclidean_division_computes_in_every_sign_quadrant() {
    probe(
        "integer Euclidean division did not compute",
        r#"
import int;

theorem div_pp(): int::div(OfNat(7), OfNat(3)) = OfNat(2) { refl }
theorem mod_pp(): int::mod(OfNat(7), OfNat(3)) = OfNat(1) { refl }
theorem div_np(): int::div(NegSucc(6), OfNat(3)) = NegSucc(2) { refl }
theorem mod_np(): int::mod(NegSucc(6), OfNat(3)) = OfNat(2) { refl }
theorem div_pn(): int::div(OfNat(7), NegSucc(2)) = NegSucc(1) { refl }
theorem mod_pn(): int::mod(OfNat(7), NegSucc(2)) = OfNat(1) { refl }
theorem div_nn(): int::div(NegSucc(6), NegSucc(2)) = OfNat(3) { refl }
theorem mod_nn(): int::mod(NegSucc(6), NegSucc(2)) = OfNat(2) { refl }
theorem div_exact_negative(): int::div(NegSucc(5), OfNat(3)) = NegSucc(1) { refl }
theorem mod_exact_negative(): int::mod(NegSucc(5), OfNat(3)) = OfNat(0) { refl }
theorem div_zero(): int::div(NegSucc(4), OfNat(0)) = OfNat(0) { refl }
theorem mod_zero(): int::mod(NegSucc(4), OfNat(0)) = NegSucc(4) { refl }
"#,
    );
}

#[test]
fn euclidean_division_reconstructs_open_integers() {
    probe(
        "integer Euclidean reconstruction did not compose",
        r#"
import int;
import logic;

theorem reconstruct(a, b: Int):
    int::div(a, b) * b + int::mod(a, b) = a
{
    int::div_mul_add_mod(a, b)
}
theorem remainder_nonnegative(a, b: Int, h: b ≠ OfNat(0)):
    OfNat(0) <= int::mod(a, b)
{
    int::mod_nonneg(a, b, h)
}
theorem remainder_bounded(a, b: Int, h: b ≠ OfNat(0)):
    int::mod(a, b) < int::abs(b)
{
    int::mod_lt_abs(a, b, h)
}
theorem quotient_at_zero(a: Int): int::div(a, OfNat(0)) = OfNat(0) {
    int::div_zero(a)
}
theorem remainder_at_zero(a: Int): int::mod(a, OfNat(0)) = a {
    int::mod_zero(a)
}
"#,
    );
}

/// The round's own row, and the reason it could not be written until
/// 2026-08-17: `Decide` at **three** orders that are all written `Le`
/// (`docs/instance-resolved-key-design.md`,
/// `issues/instance-key-collides-across-modules.md`). One downstream file that
/// imports all three, `<=` reading its carrier off the operand, and `decide` at
/// each — so the claim is not merely "three instances registered" but "the
/// resolver hands each goal the one at its own carrier".
///
/// Per `docs/testing-generated-terms.md`: an OPEN carrier on each side (the
/// `d_*_open` rows, where no goal is closed by computation), a *checking*
/// position (each is a declaration with a written result type), a closed
/// scrutinee that must actually decide (`d_*_computes`), and the negative
/// control below it.
#[test]
fn decide_resolves_at_all_three_orders_named_le() {
    probe(
        "the three `Le` carriers did not all decide",
        r#"
import int;
import nat;
import bool;
import logic;

// `<=` at three carriers in one file, none of them qualified: the designation
// at the operand's carrier is what picks the order (`nat`, `int` and `bool`
// each declare their own row).
theorem o_nat(m: Nat): m <= m { nat::le_refl(m) }
theorem o_int(a: Int): a <= a { int::le_refl(a) }
theorem o_bool(p: Bool): p <= p { bool::le_refl(p) }

// The same three, decided through the class rather than by naming a decider —
// at OPEN operands, so each is answered by the registry and not by reduction.
fn d_nat_open(m, n: Nat) -> Or<nat::Le(m, n), ¬ nat::Le(m, n)> { decide<nat::Le(m, n)>() }
fn d_int_open(a, b: Int) -> Or<int::Le(a, b), ¬ int::Le(a, b)> { decide<int::Le(a, b)>() }
fn d_bool_open(p, q: Bool) -> Or<bool::Le(p, q), ¬ bool::Le(p, q)> { decide<bool::Le(p, q)>() }

// And they COMPUTE, which is what says the answer was the right instance and
// not merely one of the right type: a decider that unfolds picks a branch.
theorem d_nat_computes(): decide_pick<nat::Le(2, 5), Nat>(7, 9) = 9 { refl }
theorem d_int_computes(): decide_pick<int::Le(OfNat(2), NegSucc(0)), Nat>(7, 9) = 7 { refl }
theorem d_bool_computes(): decide_pick<bool::Le(True, False), Nat>(7, 9) = 7 { refl }

// The canonical names, written: three modules, three declarations, one spelling
// `Le::Decide` each. This is the string the registry hands out and it is now
// writable verbatim.
fn k_nat(m, n: Nat) -> Decide<nat::Le(m, n)> { nat::Le::Decide() }
fn k_int(a, b: Int) -> Decide<int::Le(a, b)> { int::Le::Decide() }
fn k_bool(p, q: Bool) -> Decide<bool::Le(p, q)> { bool::Le::Decide() }
"#,
    );
}

/// The negative control for the test above: a decision that is *false* at
/// closed operands is refused. Without it, `d_*_computes` would pass over a
/// `decide_pick` that always took the same branch.
#[test]
fn a_wrong_decision_at_one_of_the_three_orders_is_refused() {
    let mut e = elaborated(true);
    let bad = r#"
import int;
import logic;
theorem wrong(): decide_pick<int::Le(OfNat(2), NegSucc(0)), Nat>(7, 9) = 9 { refl }
"#;
    match e.elab_module_source("bad", bad) {
        Err(_) => {}
        Ok(()) => panic!("a false decision at closed integers was accepted"),
    }
}

/// The negative control: a *false* equation at closed integers is refused. Test
/// 3 would pass over an `add` that ignored its second argument if that argument
/// happened to be `0` everywhere, and it would pass over a `mul` whose sign
/// logic was inverted if nothing pinned the sign — so this pins that the checks
/// above are checks.
#[test]
fn a_wrong_sign_is_refused() {
    let mut e = elaborated(true);
    let bad = r#"
import int;
theorem wrong(): int::mul(NegSucc(1), OfNat(3)) = OfNat(6) { refl }
"#;
    match e.elab_module_source("bad", bad) {
        Err(_) => {}
        Ok(()) => panic!("a false equation at closed integers was accepted"),
    }
}

/// Multiplication monotonicity is deliberately unavailable at a negative
/// factor: its final argument is mathematical evidence, not a Boolean guard
/// that could be ignored by the proof.
#[test]
fn multiplication_monotonicity_requires_a_nonnegative_factor() {
    let mut e = elaborated(true);
    let bad = r#"
import int;
theorem wrong(a, b: Int, h: a <= b): a * NegSucc(0) <= b * NegSucc(0) {
    int::mul_le_mono_r(a, b, NegSucc(0), h, trivial)
}
"#;
    match e.elab_module_source("bad", bad) {
        Err(_) => {}
        Ok(()) => panic!("multiplication monotonicity accepted a negative factor"),
    }
}
