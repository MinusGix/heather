//! `bv_omega`, word arithmetic lifted to Nat (docs/bv-omega-design.md), and
//! the speller fix it rests on (issues/omega-respells-atoms-without-implicits.md).
//! The axes of docs/testing-generated-terms.md: literal and open values, an
//! open width, positions other than a declaration's body, nesting depth, and
//! a negative control for each refusal.

use std::cell::OnceCell;

use heather_elab::{ElabError, Elaborator, SemanticImage};

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
    ("bitvec", include_str!("../../../lib/std/bitvec.hthr")),
    ("bitvec_nat", include_str!("../../../lib/std/bitvec/nat.hthr")),
    ("bitvec_omega", include_str!("../../../lib/std/bitvec/omega.hthr")),
];

const PREFIX: &str = "import bool;\nimport logic;\nimport nat;\nimport list;\nimport omega;\nimport bitvec;\nimport bitvec_nat;\nimport bitvec_omega;\n\n\
fn double(x: BitVec(64)) → BitVec(64) { x.add(x) }\n\
fn times256(x: BitVec(64)) → BitVec(64) { double(double(double(double(double(double(double(double(x)))))))) }\n";

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn elaborator() -> Elaborator {
    BASE.with(|base| base.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator())
}

fn message(error: ElabError) -> String {
    match error {
        ElabError::Elab { msg, .. } => msg,
        other => other.to_string(),
    }
}

fn checks(what: &str, body: &str) {
    let source = format!("{PREFIX}\n{body}\n");
    elaborator()
        .elab_module_source("probe", &source)
        .unwrap_or_else(|error| panic!("{what} did not check: {}", message(error)));
}

fn refused(what: &str, body: &str) -> String {
    let source = format!("{PREFIX}\n{body}\n");
    message(elaborator().elab_module_source("probe", &source).expect_err(what))
}

#[test]
fn bv_omega_suite() {
    respelled_atoms_elaborate();
    lifts_word_arithmetic();
    lifts_at_an_open_width();
    lifts_in_other_positions();
    lifts_a_deep_word();
    lifts_proofs_into_lemmas();
    unfolds_only_what_no_fact_states();
    refuses_naming_the_side_condition();
}

/// The respelling issue's acceptance: an atom whose implicit nothing written
/// determines is spelled with it, and a type argument likewise, so the
/// certificate elaborates to the same term.
fn respelled_atoms_elaborate() {
    checks("the width of an `ofNat` atom", "theorem uses(n: Nat, fact: BitVec::ofNat(5, n := 64).toNat() = n, small: n < 10): BitVec::ofNat(5, n := 64).toNat() < 20 { omega }");
    checks("a type argument", "fn empty<A>() → List<A> { Nil }\ntheorem typed(k: Nat, fact: empty<Nat>().len() = k, small: k < 3): empty<Nat>().len() < 5 { omega }");
    // Control: the spelled atom is the goal's own, so a false bound over it
    // is still refused rather than proved about some other term.
    let message = refused("a false bound over a respelled atom", "theorem wrong(n: Nat, fact: BitVec::ofNat(5, n := 64).toNat() = n, small: n < 10): BitVec::ofNat(5, n := 64).toNat() < 3 { omega }");
    assert!(message.contains("no contradiction"), "{message}");
}

fn lifts_word_arithmetic() {
    checks("doubling through definitions", "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, bound: v * 256 < 1152921504606846976): times256(y).toNat() = v * 256 { bv_omega }");
    checks("a literal operand", "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, bound: v < 1000): y.add(BitVec::ofNat(5)).toNat() = v + 5 { bv_omega }");
    checks("an open operand and a subtraction",
        "theorem t(s: BitVec(64), r, h, c: Nat, value: s.toNat() = 1099511627776 * r + h, fit: c <= r):\n\
         s.sub(BitVec::ofNat(1099511627776 * c)).toNat() + 1099511627776 * c = 1099511627776 * r + h { bv_omega }");
    // An operand whose written value is not its normal form.
    checks("an unnormalised constant", "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, bound: v < 1000): y.add(BitVec::ofNat(2 * v + v)).toNat() = 4 * v { bv_omega }");
    checks("a word read back from a Nat",
        "theorem t(n: Nat, small: n < 16384): double(bitvec_nat::word_of_nat(64, n)).add(BitVec::ofNat(7)).toNat() = 2 * n + 7 { bv_omega }");
}

fn lifts_at_an_open_width() {
    checks("an open width",
        "theorem t(n: Nat, a, b: BitVec(n), h: a.toNat() + b.toNat() < nat::Nat::pow(2, n)): a.add(b).toNat() = a.toNat() + b.toNat() { bv_omega }");
}

fn lifts_in_other_positions() {
    checks("a `let` annotation and an argument",
        "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, bound: v < 1000): double(y).toNat() + 1 = v + v + 1 {\n\
             let e: (double(y).toNat() = v + v) = bv_omega;\n\
             Nat::cong(λ (x: Nat) => x + 1, e)\n\
         }");
    checks("a fact in scope over a stated word",
        "theorem t(y: BitVec(64), small: double(y).toNat() < 100): double(y).add(BitVec::ofNat(1)).toNat() < 101 { bv_omega }");
    checks("a fact in scope over a word taken apart",
        "theorem t(y: BitVec(64), small: y.toNat() < 10, h: y.add(BitVec::ofNat(1)).toNat() = 5): y.toNat() = 4 { bv_omega }");
    // Control: a stated word's value may already have wrapped, so it says
    // nothing about the sum it was built from.
    let message = refused("a wrapped word's bound",
        "theorem t(y: BitVec(64), small: double(y).toNat() < 100): y.add(y).add(BitVec::ofNat(1)).toNat() < 101 { bv_omega }");
    assert!(message.contains("may overflow 64 bits"), "{message}");
}

/// Depth, the fifth axis: thirty-nine doublings is past where a Π per side
/// condition, or `omega` over the composite words, ran out of kernel depth.
fn lifts_a_deep_word() {
    checks("thirty-nine doublings",
        "theorem t(n: Nat, small: n < 16384): double(double(double(double(double(double(double(times256(times256(times256(times256(bitvec_nat::word_of_nat(64, n)))))))))))).toNat() = 549755813888 * n { bv_omega }");
}

/// Each `bv_omega` proof is checked as a lemma of its own
/// (`docs/bv-omega-design.md` §7). The sites here are the ones the lifting has
/// to get right: one site met in several contexts (only the first lifts), a
/// later proof that reaches an earlier one through a `let`, a lifted proof
/// beside a written hole, and a branch of a `match` on an equation.
fn lifts_proofs_into_lemmas() {
    checks("one site in several branches",
        "theorem t(b: bool::Bool, y: BitVec(64), v: Nat, value: y.toNat() = v, small: v < 1000): double(y).toNat() = v + v {\n\
             split_all;\n\
             all_goals { bv_omega }\n\
         }");
    checks("a proof over an earlier one",
        "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, small: v < 1000): y.add(BitVec::ofNat(2)).add(BitVec::ofNat(1)).toNat() = v + 3 {\n\
             let first: (y.add(BitVec::ofNat(2)).toNat() = v + 2) = bv_omega;\n\
             let moved: (y.add(BitVec::ofNat(2)).toNat() + 1 = v + 3) = Nat::cong(λ (x: Nat) => x + 1, first);\n\
             bv_omega\n\
         }");
    checks("a lifted proof beside a hole",
        "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, small: v < 1000): (double(y).toNat() = v + v) ∧ (v <= v + 1) {\n\
             ⟨bv_omega, ?rest⟩\n\
             on ?rest := omega;\n\
         }");
    // A `match` arm's hidden induction hypothesis (`#ih`) is no fact for a
    // certificate to cite: source cannot name it.
    checks("`omega` in an arm with a hidden hypothesis",
        "theorem t(y: BitVec(64), v, q: Nat, value: y.toNat() = v, small: v < 1000): y.toNat() + y.toNat() = v + v {\n\
             match q { Zero => omega, Succ(_) => omega }\n\
         }");
    checks("a branch",
        "theorem t(y: BitVec(64), v, q: Nat, value: y.toNat() = v, small: v < 1000, one: q <= 1): double(y).toNat() = v + v {\n\
             match q { Zero => bv_omega, Succ(_) => bv_omega }\n\
         }");
}

/// A word whose `toNat` a fact states is a leaf, not unfolded past what the
/// writer knows about it.
fn unfolds_only_what_no_fact_states() {
    checks("a stated word",
        "fn three(x: BitVec(64)) → BitVec(64) { x.add(x).add(x) }\n\
         theorem t(y: BitVec(64), k: Nat, known: three(y).toNat() = k, small: k < 1000): three(y).add(BitVec::ofNat(1)).toNat() = k + 1 { bv_omega }");
}

fn refuses_naming_the_side_condition() {
    let message = refused("an overflowing doubling",
        "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, bound: v < 18446744073709551615): double(y).toNat() = v * 2 { bv_omega }");
    assert!(message.contains("`double(y)` may overflow 64 bits"), "{message}");
    let message = refused("a borrowing subtraction",
        "theorem t(a, b: BitVec(64), x, y: Nat, ha: a.toNat() = x, hb: b.toNat() = y): a.sub(b).toNat() + y = x { bv_omega }");
    assert!(message.contains("may borrow"), "{message}");
    let message = refused("a constant past the width",
        "theorem t(): BitVec::ofNat(nat::Nat::pow(2, 64), n := 64).toNat() = nat::Nat::pow(2, 64) { bv_omega }");
    assert!(message.contains("does not fit 64 bits"), "{message}");
    // Every side condition holds and the goal is false: the final `omega`
    // refuses it.
    let message = refused("a wrong value",
        "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, bound: v < 1000): double(y).toNat() = v + v + 1 { bv_omega }");
    assert!(message.contains("no contradiction"), "{message}");
    let message = refused("no word", "theorem t(n: Nat, h: n < 3): n < 5 { bv_omega }");
    assert!(message.contains("found no `toNat` of a word"), "{message}");
}
