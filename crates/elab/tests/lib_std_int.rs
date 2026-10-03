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

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");

fn elaborated(cached: bool) -> Elaborator {
    if cached {
        // The probes: the library checked once per process, a fork each.
        let mut e = support::library(&[
            ("logic", LOGIC), ("bool", BOOL), ("nat", NAT),
            ("option", OPTION), ("pair", PAIR), ("list", LIST),
            ("algebra", ALGEBRA), ("int", INT),
        ]);
        e.set_review_lints(true);
        return e;
    }
    let mut e = Elaborator::with_prelude().expect("prelude");
    // The retained-motive control in `the_int_module_checks` reads the
    // review-mode lint.
    e.set_review_lints(true);
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
    load(&mut e);
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
        INT.contains("decide_bit_split<a <= b>(λ c => a <= match c { True => b, False => a }")
            && INT.contains("decide_bit_split<a <= b>(λ c => b <= match c { True => b, False => a }")
            && INT.contains("decide_bit_split<a <= b>(λ x => c <= match x { True => a, False => b }"),
        "the three kernel-required motives remain explicit (over the bit an evidence-free `if` matches on)"
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

theorem i_neg_neg(a: Int): int::Int::neg(int::Int::neg(a)) = a { int::Int::neg_neg(a) }
theorem i_add_comm(a, b: Int): int::Int::add(a, b) = int::Int::add(b, a) { int::Int::add_comm(a, b) }
theorem i_add_assoc(a, b, c: Int): int::Int::add(int::Int::add(a, b), c) = int::Int::add(a, int::Int::add(b, c)) { int::Int::add_assoc(a, b, c) }
theorem i_add_zero(a: Int): int::Int::add(a, OfNat(0)) = a { int::Int::add_zero(a) }
theorem i_zero_add(a: Int): int::Int::add(OfNat(0), a) = a { int::Int::zero_add(a) }
theorem i_add_neg(a: Int): int::Int::add(a, int::Int::neg(a)) = OfNat(0) { int::Int::add_neg(a) }
theorem i_neg_add(a, b: Int): int::Int::neg(int::Int::add(a, b)) = int::Int::add(int::Int::neg(a), int::Int::neg(b)) { int::Int::neg_add(a, b) }
theorem i_sub_self(a: Int): int::Int::sub(a, a) = OfNat(0) { int::Int::sub_self(a) }
theorem i_neg_unique(x, y: Int, h: int::Int::add(x, y) = OfNat(0)): y = int::Int::neg(x) { int::Int::neg_unique(x, y, h) }

theorem i_mul_comm(a, b: Int): int::Int::mul(a, b) = int::Int::mul(b, a) { int::Int::mul_comm(a, b) }
theorem i_mul_assoc(a, b, c: Int): int::Int::mul(int::Int::mul(a, b), c) = int::Int::mul(a, int::Int::mul(b, c)) { int::Int::mul_assoc(a, b, c) }
theorem i_mul_one(a: Int): int::Int::mul(a, OfNat(1)) = a { int::Int::mul_one(a) }
theorem i_mul_zero(a: Int): int::Int::mul(a, OfNat(0)) = OfNat(0) { int::Int::mul_zero(a) }
theorem i_mul_neg_r(a, b: Int): int::Int::mul(a, int::Int::neg(b)) = int::Int::neg(int::Int::mul(a, b)) { int::Int::mul_neg_r(a, b) }
theorem i_mul_neg_l(a, b: Int): int::Int::mul(int::Int::neg(a), b) = int::Int::neg(int::Int::mul(a, b)) { int::Int::mul_neg_l(a, b) }
theorem i_mul_isucc(a, x: Int): int::Int::mul(a, int::Int::isucc(x)) = int::Int::add(int::Int::mul(a, x), a) { int::Int::mul_isucc(a, x) }
theorem i_distr(a, b, c: Int): int::Int::mul(a, int::Int::add(b, c)) = int::Int::add(int::Int::mul(a, b), int::Int::mul(a, c)) {
    int::Int::mul_add_distr(a, b, c)
}
theorem i_distr_r(a, b, c: Int): int::Int::mul(int::Int::add(a, b), c) = int::Int::add(int::Int::mul(a, c), int::Int::mul(b, c)) {
    int::Int::add_mul_distr(a, b, c)
}

theorem i_le_refl(a: Int): a <= a { int::Int::le_refl(a) }
theorem i_le_trans(a, b, c: Int, h1: a <= b, h2: b <= c): a <= c { int::Int::le_trans(a)(b, c, h1, h2) }
theorem i_le_antisym(a, b: Int, h1: a <= b, h2: b <= a): a = b { int::Int::le_antisym(a)(b, h1, h2) }
theorem i_le_total(a, b: Int): Or<int::Int::Le(a, b), int::Int::Le(b, a)> { int::Int::le_total(a, b) }
theorem i_le_dec(a, b: Int): Or<int::Int::Le(a, b), ¬ int::Int::Le(a, b)> { int::Int::le_dec(a, b) }
theorem i_le_of_not_le(a, b: Int, h: ¬ int::Int::Le(a, b)): b <= a { int::Int::le_of_not_le(a, b, h) }
theorem i_lt_irrefl(a: Int): ¬ int::Int::Lt(a, a) { int::Int::lt_irrefl(a) }
theorem i_le_of_lt(a, b: Int, h: int::Int::Lt(a, b)): a <= b { int::Int::le_of_lt(a)(b, h) }
theorem i_lt_trichotomy(a, b: Int): a < b ∨ a = b ∨ b < a { int::Int::lt_trichotomy(a, b) }
theorem i_lt_trans(a, b, c: Int, h1: a < b, h2: b < c): a < c { int::Int::lt_trans(a, b, c, h1, h2) }
theorem i_lt_of_lt_of_le(a, b, c: Int, h1: a < b, h2: b <= c): a < c {
    int::Int::lt_of_lt_of_le(a, b, c, h1, h2)
}
theorem i_lt_of_le_of_lt(a, b, c: Int, h1: a <= b, h2: b < c): a < c {
    int::Int::lt_of_le_of_lt(a, b, c, h1, h2)
}
theorem i_lt_of_le_of_ne(a, b: Int, h1: a <= b, h2: ¬ (a = b)): a < b {
    int::Int::lt_of_le_of_ne(a, b, h1, h2)
}
theorem i_lt_asymm(a, b: Int, h: a < b): ¬ (b < a) { int::Int::lt_asymm(a, b, h) }
theorem i_le_of_not_lt(a, b: Int, h: ¬ (a < b)): b <= a { int::Int::le_of_not_lt(a, b, h) }
theorem i_lt_of_not_le(a, b: Int, h: ¬ (b <= a)): a < b { int::Int::lt_of_not_le(a, b, h) }
theorem i_le_isucc(a, b: Int, h: a <= b): int::Int::isucc(a) <= int::Int::isucc(b) { int::Int::le_isucc(a)(b, h) }
theorem i_le_ipred(a, b: Int, h: a <= b): int::Int::ipred(a) <= int::Int::ipred(b) { int::Int::le_ipred(a)(b, h) }
theorem i_le_neg(a, b: Int, h: a <= b): int::Int::neg(b) <= int::Int::neg(a) { int::Int::le_neg(a)(b, h) }
theorem i_add_le_mono_r(a, b, c: Int, h: a <= b): int::Int::add(a, c) <= int::Int::add(b, c) {
    int::Int::add_le_mono_r(a, b, c, h)
}
theorem i_add_le_mono_l(a, b, c: Int, h: a <= b): int::Int::add(c, a) <= int::Int::add(c, b) {
    int::Int::add_le_mono_l(a, b, c, h)
}
theorem i_add_le_mono(a, b, c, d: Int, h1: a <= b, h2: c <= d): a + c <= b + d {
    int::Int::add_le_mono(a, b, c, d, h1, h2)
}
theorem i_mul_le_mono_r(a, b, k: Int, h1: a <= b, h2: OfNat(0) <= k): a * k <= b * k {
    int::Int::mul_le_mono_r(a, b, k, h1, h2)
}
theorem i_mul_le_mono_l(a, b, k: Int, h1: a <= b, h2: OfNat(0) <= k): k * a <= k * b {
    int::Int::mul_le_mono_l(a, b, k, h1, h2)
}

theorem i_le_max_l(a, b: Int): a <= int::Int::max(a, b) { int::Int::le_max_l(a, b) }
theorem i_le_max_r(a, b: Int): b <= int::Int::max(a, b) { int::Int::le_max_r(a, b) }
theorem i_min_le_l(a, b: Int): int::Int::min(a, b) <= a { int::Int::min_le_l(a, b) }
theorem i_min_le_r(a, b: Int): int::Int::min(a, b) <= b { int::Int::min_le_r(a, b) }
theorem i_max_le(a, b, c: Int, h1: a <= c, h2: b <= c): int::Int::max(a, b) <= c {
    int::Int::max_le(a, b, c, h1, h2)
}
theorem i_le_min(a, b, c: Int, h1: c <= a, h2: c <= b): c <= int::Int::min(a, b) {
    int::Int::le_min(a, b, c, h1, h2)
}
theorem i_max_eq_r(a, b: Int, h: a <= b): int::Int::max(a, b) = b { int::Int::max_eq_r(a, b, h) }
theorem i_max_eq_l(a, b: Int, h: b <= a): int::Int::max(a, b) = a { int::Int::max_eq_l(a, b, h) }
theorem i_min_eq_l(a, b: Int, h: a <= b): int::Int::min(a, b) = a { int::Int::min_eq_l(a, b, h) }
theorem i_min_eq_r(a, b: Int, h: b <= a): int::Int::min(a, b) = b { int::Int::min_eq_r(a, b, h) }

theorem i_ofNat_add(m, n: Nat): OfNat(nat::Nat::add(m, n)) = int::Int::add(OfNat(m), OfNat(n)) {
    int::Int::ofNat_add(m, n)
}
theorem i_ofNat_mul(m, n: Nat): OfNat(nat::Nat::mul(m, n)) = int::Int::mul(OfNat(m), OfNat(n)) {
    int::Int::ofNat_mul(m, n)
}
theorem i_ofNat_le(m, n: Nat): Iff<nat::Nat::Le(m, n), int::Int::Le(OfNat(m), OfNat(n))> {
    int::Int::ofNat_le_iff(m, n)
}
theorem i_toNat(a: Int, h: OfNat(0) <= a): OfNat(int::Int::toNat(a)) = a { int::Int::ofNat_toNat(a)(h) }
theorem i_int_ind(P: Int -> Type, z: P(OfNat(0)),
                  up: (k: Nat) -> P(OfNat(k)) -> P(OfNat(Succ(k))),
                  d: P(NegSucc(0)),
                  dn: (k: Nat) -> P(NegSucc(k)) -> P(NegSucc(Succ(k))), a: Int): P(a) {
    int::Int::ind(P, z, up, d, dn, a)
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
/// Note what has to be qualified and what does not: `int::Int::add` and `nat::Nat::add`
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

theorem c_add_pp(): int::Int::add(OfNat(2), OfNat(3)) = OfNat(5) { refl }
theorem c_add_pn(): int::Int::add(OfNat(2), NegSucc(4)) = NegSucc(2) { refl }
theorem c_add_np(): int::Int::add(NegSucc(1), OfNat(5)) = OfNat(3) { refl }
theorem c_add_nn(): int::Int::add(NegSucc(1), NegSucc(2)) = NegSucc(4) { refl }
theorem c_sub_under(): int::Int::sub(OfNat(3), OfNat(8)) = NegSucc(4) { refl }
theorem c_sub_over(): int::Int::sub(OfNat(8), OfNat(3)) = OfNat(5) { refl }
theorem c_neg_p(): int::Int::neg(OfNat(4)) = NegSucc(3) { refl }
theorem c_neg_n(): int::Int::neg(NegSucc(3)) = OfNat(4) { refl }
theorem c_neg_zero(): int::Int::neg(OfNat(0)) = OfNat(0) { refl }
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
    c_nested_numeral_anchor(a) = int::Int::neg(int::Int::add(OfNat(1), a)) { refl }
theorem c_generic_int_numeral(): c_generic_numeral<Int>() = OfNat(1) { refl }
theorem c_generic_nat_numeral(): c_generic_numeral<Nat>() = 1 { refl }
theorem c_positive_literal_equation(): 4 = OfNat(4) { refl }
theorem c_negative_literal_equation(): -4 = NegSucc(3) { refl }
theorem c_literal_arithmetic_equation(): 2 + 3 = OfNat(5) { refl }
theorem c_literal_left_computes(): c_literal_left_infers_from_sibling(OfNat(2)) = OfNat(5) { refl }
theorem c_prefix_neg_open(a: Int): -a = int::Int::neg(a) { refl }
theorem c_prefix_neg_positive(): -OfNat(4) = NegSucc(3) { refl }
theorem c_prefix_neg_negative(): -NegSucc(3) = OfNat(4) { refl }
theorem c_prefix_neg_nested(a: Int): --a = a { int::Int::neg_neg(a) }
theorem c_prefix_neg_precedence(a, b: Int): -a * b = int::Int::mul(int::Int::neg(a), b) { refl }
theorem c_mul_pp(): int::Int::mul(OfNat(2), OfNat(3)) = OfNat(6) { refl }
theorem c_mul_pn(): int::Int::mul(OfNat(2), NegSucc(2)) = NegSucc(5) { refl }
theorem c_mul_np(): int::Int::mul(NegSucc(1), OfNat(3)) = NegSucc(5) { refl }
theorem c_mul_nn(): int::Int::mul(NegSucc(1), NegSucc(2)) = OfNat(6) { refl }
theorem c_mul_zero(): int::Int::mul(NegSucc(7), OfNat(0)) = OfNat(0) { refl }
theorem c_toNat(): int::Int::toNat(NegSucc(3)) = 0 { refl }

// the order decides by computing, in all four sign combinations
theorem c_le_pp(): OfNat(2) <= OfNat(7) { trivial }
theorem c_le_nn(): NegSucc(9) <= NegSucc(0) { trivial }
theorem c_le_np(): NegSucc(9) <= OfNat(0) { trivial }
theorem c_not_le_pn(): ¬ (OfNat(0) <= NegSucc(0)) { λ (h: OfNat(0) <= NegSucc(0)) => h }
theorem c_lt(): int::Int::Lt(NegSucc(0), OfNat(0)) { trivial }
theorem c_max_mixed(): int::Int::max(NegSucc(2), OfNat(1)) = OfNat(1) { refl }
theorem c_max_negative(): int::Int::max(NegSucc(2), NegSucc(5)) = NegSucc(2) { refl }
theorem c_min_mixed(): int::Int::min(OfNat(3), NegSucc(1)) = NegSucc(1) { refl }
theorem c_min_positive(): int::Int::min(OfNat(3), OfNat(7)) = OfNat(3) { refl }

// the operators at BOTH carriers, in one file, with neither qualified
theorem c_op_int(a, b: Int): a + b = b + a { int::Int::add_comm(a, b) }
theorem c_op_nat(m, n: Nat): m + n = n + m { nat::Nat::add_comm(m, n) }
theorem c_op_int_mul(a, b: Int): a * b = b * a { int::Int::mul_comm(a, b) }
theorem c_op_le_int(a: Int): a <= a { int::Int::le_refl(a) }
theorem c_op_lt_int(a: Int): a < int::Int::isucc(a) { int::Int::lt_isucc_self(a) }
theorem c_op_lt_nat(n: Nat): n < Succ(n) { nat::Nat::lt_succ_self(n) }

// the instances, reached by resolution: the commutative monoid's generic law,
// the monoid fold at `List<Int>`, the group's inverse-uniqueness, and `Cmp`
theorem c_unit(a: Int): a + OfNat(0) = a { op_unit_of_comm(a) }
theorem c_sum(): sum_all(Cons(OfNat(2), Cons(NegSucc(0), Nil))) = OfNat(1) { refl }
theorem c_inv(x, y: Int, h: int::Int::add(x, y) = OfNat(0)): y = int::Int::neg(x) {
    op_inv_unique(x, y, h)
}

theorem c_max(a: Int): max_of(a, a) = a { max_of_self(a) }
theorem c_max_computes(): max_of(NegSucc(2), OfNat(1)) = OfNat(1) { refl }
"#,
    );
}

/// A closed sum costs one `Nat` operation on the payloads, not the
/// magnitude: `add` is the four sign cases over `nat::Nat::add` and the
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

theorem big_sub(): int::Int::sub(OfNat(nat::Nat::pow(2, 63)), OfNat(nat::Nat::pow(2, 64))) = NegSucc(nat::Nat::sub(nat::Nat::pow(2, 63), 1)) { refl }
theorem big_sub_over(): int::Int::sub(OfNat(nat::Nat::pow(2, 64)), OfNat(nat::Nat::pow(2, 63))) = OfNat(nat::Nat::pow(2, 63)) { refl }
theorem big_add(): int::Int::add(OfNat(nat::Nat::pow(2, 63)), OfNat(nat::Nat::pow(2, 63))) = OfNat(nat::Nat::pow(2, 64)) { refl }
theorem big_neg_neg(): int::Int::add(NegSucc(nat::Nat::pow(2, 63)), NegSucc(nat::Nat::pow(2, 63))) = NegSucc(nat::Nat::add(nat::Nat::pow(2, 64), 1)) { refl }
theorem big_mixed(): int::Int::add(NegSucc(nat::Nat::pow(2, 63)), OfNat(nat::Nat::pow(2, 64))) = OfNat(nat::Nat::sub(nat::Nat::pow(2, 63), 1)) { refl }
theorem big_mixed_under(): int::Int::add(OfNat(nat::Nat::pow(2, 63)), NegSucc(nat::Nat::pow(2, 64))) = NegSucc(nat::Nat::pow(2, 63)) { refl }
theorem big_cancel(): int::Int::sub(OfNat(nat::Nat::pow(2, 64)), OfNat(nat::Nat::pow(2, 64))) = OfNat(0) { refl }
"#,
    );
}

#[test]
fn euclidean_division_computes_in_every_sign_quadrant() {
    probe(
        "integer Euclidean division did not compute",
        r#"
import int;

theorem div_pp(): int::Int::div(OfNat(7), OfNat(3)) = OfNat(2) { refl }
theorem mod_pp(): int::Int::mod(OfNat(7), OfNat(3)) = OfNat(1) { refl }
theorem div_np(): int::Int::div(NegSucc(6), OfNat(3)) = NegSucc(2) { refl }
theorem mod_np(): int::Int::mod(NegSucc(6), OfNat(3)) = OfNat(2) { refl }
theorem div_pn(): int::Int::div(OfNat(7), NegSucc(2)) = NegSucc(1) { refl }
theorem mod_pn(): int::Int::mod(OfNat(7), NegSucc(2)) = OfNat(1) { refl }
theorem div_nn(): int::Int::div(NegSucc(6), NegSucc(2)) = OfNat(3) { refl }
theorem mod_nn(): int::Int::mod(NegSucc(6), NegSucc(2)) = OfNat(2) { refl }
theorem div_exact_negative(): int::Int::div(NegSucc(5), OfNat(3)) = NegSucc(1) { refl }
theorem mod_exact_negative(): int::Int::mod(NegSucc(5), OfNat(3)) = OfNat(0) { refl }
theorem div_zero(): int::Int::div(NegSucc(4), OfNat(0)) = OfNat(0) { refl }
theorem mod_zero(): int::Int::mod(NegSucc(4), OfNat(0)) = NegSucc(4) { refl }
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
    int::Int::div(a, b) * b + int::Int::mod(a, b) = a
{
    int::Int::div_mul_add_mod(a, b)
}
theorem remainder_nonnegative(a, b: Int, h: b ≠ OfNat(0)):
    OfNat(0) <= int::Int::mod(a, b)
{
    int::Int::mod_nonneg(a, b, h)
}
theorem remainder_bounded(a, b: Int, h: b ≠ OfNat(0)):
    int::Int::mod(a, b) < int::Int::abs(b)
{
    int::Int::mod_lt_abs(a, b, h)
}
theorem quotient_at_zero(a: Int): int::Int::div(a, OfNat(0)) = OfNat(0) {
    int::Int::div_zero(a)
}
theorem remainder_at_zero(a: Int): int::Int::mod(a, OfNat(0)) = a {
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
theorem o_nat(m: Nat): m <= m { nat::Nat::le_refl(m) }
theorem o_int(a: Int): a <= a { int::Int::le_refl(a) }
theorem o_bool(p: Bool): p <= p { bool::Bool::le_refl(p) }

// The same three, decided through the class rather than by naming a decider —
// at OPEN operands, so each is answered by the registry and not by reduction.
fn d_nat_open(m, n: Nat) -> Or<nat::Nat::Le(m, n), ¬ nat::Nat::Le(m, n)> { decide<nat::Nat::Le(m, n)>() }
fn d_int_open(a, b: Int) -> Or<int::Int::Le(a, b), ¬ int::Int::Le(a, b)> { decide<int::Int::Le(a, b)>() }
fn d_bool_open(p, q: Bool) -> Or<bool::Bool::Le(p, q), ¬ bool::Bool::Le(p, q)> { decide<bool::Bool::Le(p, q)>() }

// And they COMPUTE, which is what says the answer was the right instance and
// not merely one of the right type: a decider that unfolds picks a branch.
theorem d_nat_computes(): decide_pick<nat::Nat::Le(2, 5), Nat>(7, 9) = 9 { refl }
theorem d_int_computes(): decide_pick<int::Int::Le(OfNat(2), NegSucc(0)), Nat>(7, 9) = 7 { refl }
theorem d_bool_computes(): decide_pick<bool::Bool::Le(True, False), Nat>(7, 9) = 7 { refl }

// The canonical names, written: three modules, three declarations, one spelling
// `Le::Decide` each. This is the string the registry hands out and it is now
// writable verbatim.
fn k_nat(m, n: Nat) -> Decide<nat::Nat::Le(m, n)> { nat::Nat::Le::Decide() }
fn k_int(a, b: Int) -> Decide<int::Int::Le(a, b)> { int::Int::Le::Decide() }
fn k_bool(p, q: Bool) -> Decide<bool::Bool::Le(p, q)> { bool::Bool::Le::Decide() }
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
theorem wrong(): decide_pick<int::Int::Le(OfNat(2), NegSucc(0)), Nat>(7, 9) = 9 { refl }
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
theorem wrong(): int::Int::mul(NegSucc(1), OfNat(3)) = OfNat(6) { refl }
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
    int::Int::mul_le_mono_r(a, b, NegSucc(0), h, trivial)
}
"#;
    match e.elab_module_source("bad", bad) {
        Err(_) => {}
        Ok(()) => panic!("multiplication monotonicity accepted a negative factor"),
    }
}
