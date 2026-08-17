//! `lib/std/int.hthr` — the integer module, checked on its own
//! (`issues/std-int-encoding.md`, wave I of `issues/std-api-waves.md`).
//!
//! Nothing else in the library imports `int`, so without this binary the file
//! would be checked by nothing at all. Four tests, and the split is the one
//! `lib_std_list.rs` established plus the negative control that file lacks:
//!
//!  1. the closure checks (the module and everything it imports);
//!  2. the law kit is *there* — named one by one, because a law deleted rather
//!     than broken is a change test 1 cannot see;
//!  3. the API computes at closed arguments, in both signs, and the operators
//!     and class instances resolve at `Int` in a file that ALSO imports `nat`
//!     (the whole point of the designations);
//!  4. a false equation is refused, so test 3 is not vacuous.
//!
//! `int` imports `algebra` (it registers its own instances), so the prefix here
//! is the whole of `lib/std`.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");

fn elaborated() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("algebra", ALGEBRA),
        ("int", INT),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            let msg = match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            };
            panic!("{name} did not check: {msg}");
        }
    }
    e
}

fn probe(name: &str, src: &str) {
    let mut e = elaborated();
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
    elaborated();
}

/// The kit `issues/std-int-encoding.md` §"Sketch of the kit" asked for, stated
/// at OPEN integers so that nothing here is answered by computation: `neg`,
/// `add`, `sub`, `mul` with their laws, the group and ring facts, the order and
/// its kit, and the `Nat` embedding.
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
theorem i_le_isucc(a, b: Int, h: a <= b): int::isucc(a) <= int::isucc(b) { int::le_isucc(a)(b, h) }
theorem i_le_ipred(a, b: Int, h: a <= b): int::ipred(a) <= int::ipred(b) { int::le_ipred(a)(b, h) }
theorem i_le_neg(a, b: Int, h: a <= b): int::neg(b) <= int::neg(a) { int::le_neg(a)(b, h) }
theorem i_add_le_mono_r(a, b, c: Int, h: a <= b): int::add(a, c) <= int::add(b, c) {
    int::add_le_mono_r(a, b, c, h)
}
theorem i_add_le_mono_l(a, b, c: Int, h: a <= b): int::add(c, a) <= int::add(c, b) {
    int::add_le_mono_l(a, b, c, h)
}

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
/// file that imports `nat` too — which is the property the three designations at
/// the end of `int.hthr` exist for, and the one a reader would otherwise have to
/// take on trust. Both signs on both sides of every operation, since a
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

// the operators at BOTH carriers, in one file, with neither qualified
theorem c_op_int(a, b: Int): a + b = b + a { int::add_comm(a, b) }
theorem c_op_nat(m, n: Nat): m + n = n + m { nat::add_comm(m, n) }
theorem c_op_int_mul(a, b: Int): a * b = b * a { int::mul_comm(a, b) }
theorem c_op_le_int(a: Int): a <= a { int::le_refl(a) }

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

/// The negative control: a *false* equation at closed integers is refused. Test
/// 3 would pass over an `add` that ignored its second argument if that argument
/// happened to be `0` everywhere, and it would pass over a `mul` whose sign
/// logic was inverted if nothing pinned the sign — so this pins that the checks
/// above are checks.
#[test]
fn a_wrong_sign_is_refused() {
    let mut e = elaborated();
    let bad = r#"
import int;
theorem wrong(): int::mul(NegSucc(1), OfNat(3)) = OfNat(6) { refl }
"#;
    match e.elab_module_source("bad", bad) {
        Err(_) => {}
        Ok(()) => panic!("a false equation at closed integers was accepted"),
    }
}
