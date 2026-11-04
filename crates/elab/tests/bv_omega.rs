//! `bv_omega`, word arithmetic lifted to Nat (docs/bv-omega-design.md), and
//! the speller fix it rests on (issues/omega-respells-atoms-without-implicits.md).
//! The axes of docs/testing-generated-terms.md: literal and open values, an
//! open width, positions other than a declaration's body, nesting depth, and
//! a negative control for each refusal.

use std::sync::OnceLock;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("bitvec", include_str!("../../../lib/std/bitvec/bitvec.hthr")),
    ("bitvec_nat", include_str!("../../../lib/std/bitvec/bitvec_nat.hthr")),
    ("bitvec_omega", include_str!("../../../lib/std/tactic/bitvec_omega.hthr")),
    ("char", include_str!("../../../lib/std/text/char.hthr")),
    ("byte", include_str!("../../../lib/std/bitvec/byte.hthr")),
];

const PREFIX: &str = "import bool;\nimport logic;\nimport nat;\nimport list;\nimport omega;\nimport bitvec;\nimport bitvec_nat;\nimport bitvec_omega;\n\n\
fn double(x: BitVec(64)) → BitVec(64) { x.add(x) }\n\
fn times256(x: BitVec(64)) → BitVec(64) { double(double(double(double(double(double(double(double(x)))))))) }\n";

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn elaborator() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
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
    lifts_bytes_comparisons_and_equality();
    reconstructs_bounded_combinations();
    lifts_at_an_open_width();
    lifts_in_other_positions();
    lifts_a_deep_word();
    lifts_proofs_into_lemmas();
    unfolds_only_what_no_fact_states();
    refuses_naming_the_side_condition();
    names_atom_lists();
    proves_what_is_written_down_without_search();
    splits_stuck_comparisons();
    splits_through_definitions();
    byte_tests_read_as_written();
    splits_decided_predicates();
    splits_comparisons_a_split_decides();
}

/// Byte tests as a program writes them (S3 of
/// docs/native-programs-read-like-programs-design.md): a numeral or a
/// character at a byte is its `ofNat`, also on the left of an order and before
/// the argument that fixes the width; `=`, `<` and `<=` at bytes decide, alone
/// and under connectives; and the decision computes on closed bytes.
fn byte_tests_read_as_written() {
    let source = |body: &str| format!("import bool;\nimport logic;\nimport nat;\nimport algebra;\nimport bitvec;\nimport char;\nimport byte;\n\n{body}\n");
    let check = |what: &str, body: &str| {
        let source = source(body);
        elaborator().elab_module_source("probe", &source).unwrap_or_else(|error| panic!("{what} did not check: {}", message(error)));
    };
    check("literals at a byte are their ofNat", r#"
        fn ten() → BitVec(8) { 10 }
        fn newline() → BitVec(8) { '\n' }
        theorem same(): ten() = newline() { refl }
        theorem spelled(): ten() = BitVec::ofNat(10) { refl }
    "#);
    check("decided byte tests", r#"
        fn newline(b: BitVec(8)) → Bool { if b = '\n' { True } else { False } }
        fn space(b: BitVec(8)) → Bool { if b = ' ' ∨ ('\t' <= b ∧ b <= '\r') { True } else { False } }
        fn control(b: BitVec(8)) → Bool { if b < 32 ∧ ¬(9 <= b) { True } else { False } }
        theorem closed(): (newline('\n') = True) ∧ ((newline('a') = False) ∧ ((space('\r') = True) ∧ ((space(' ') = True) ∧
            ((space('x') = False) ∧ ((control(BitVec::ofNat(3)) = True) ∧ (control('\t') = False)))))) {
            ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, ⟨refl, refl⟩⟩⟩⟩⟩⟩
        }
    "#);
    let refused = |what: &str, body: &str| {
        let source = source(body);
        assert!(elaborator().elab_module_source("probe", &source).is_err(), "{what} checked");
    };
    refused("a wrong closed decision", r#"
        fn newline(b: BitVec(8)) → Bool { if b = '\n' { True } else { False } }
        theorem wrong(): newline('\r') = True { refl }
    "#);
    refused("a character at a wider word", r#"
        fn wide() → BitVec(16) { 'a' }
    "#);
}

/// Predicates written as decisions' bits (S4 of
/// docs/native-programs-read-like-programs-design.md): an equality splits like
/// an order, with its Nat fact (`≠` on the false side, which omega splits); a
/// helper that *is* a comparison is split at the comparison, under `of_bit`
/// too; and a recursive definition at a constructor, which reaches the byte
/// through the constructor's encoding, splits with the other side.
fn splits_decided_predicates() {
    let source = |body: &str| format!("import bool;\nimport logic;\nimport nat;\nimport list;\nimport omega;\nimport algebra;\n\
        import bitvec;\nimport bitvec_nat;\nimport bitvec_omega;\nimport char;\nimport byte;\n\n{body}\n");
    let check = |what: &str, body: &str| {
        let source = source(body);
        elaborator().elab_module_source("probe", &source).unwrap_or_else(|error| panic!("{what} did not check: {}", message(error)));
    };
    let refused = |what: &str, body: &str| message(elaborator().elab_module_source("probe", &source(body)).expect_err(what));
    let predicates = r#"
        fn newline(b: BitVec(8)) → Bool { decide_bit<b = '\n'>() }
        fn space(b: BitVec(8)) → Bool { decide_bit<b = ' ' ∨ ('\t' <= b ∧ b <= '\r')>() }
        fn kept(b: BitVec(8)) → Bool { decide_bit<b ≠ '\r'>() }
        fn step(count: Nat, b: BitVec(8)) → Nat { match space(b) { True => count, False => Succ(count) } }
    "#;
    check("equalities, connectives and helpers", &format!("{predicates}
        theorem newline_space(b: BitVec(8)): Nat::of_bit(newline(b)) <= Nat::of_bit(space(b)) {{ split_all; all_goals {{ omega }} }}
        theorem lines(count: Nat, b: BitVec(8)): (if b = '\\n' {{ Succ(count) }} else {{ count }}) = count + Nat::of_bit(newline(b)) {{
            split_all; all_goals {{ omega }}
        }}
        theorem advances(count: Nat, b: BitVec(8)): step(count, b) <= Succ(count) {{ split_all; all_goals {{ omega }} }}
        theorem one(b: BitVec(8), rest: List<BitVec(8)>):
            Cons(b, rest).filter(kept) = match kept(b) {{ True => Cons(b, rest.filter(kept)), False => rest.filter(kept) }} {{
            split_all; all_goals {{ refl }}
        }}
        theorem single(b: BitVec(8)): Cons(b, Nil<BitVec(8)>).filter(kept) = (if b = '\\r' {{ Nil }} else {{ Cons(b, Nil) }}) {{
            split_all; all_goals {{ refl }}
        }}
    "));
    let error = refused("a newline counted at every space", &format!("{predicates}
        theorem wrong(count: Nat, b: BitVec(8)): step(count, b) = count + Nat::of_bit(newline(b)) {{ split_all; all_goals {{ omega }} }}
    "));
    assert!(error.contains("no contradiction") || error.contains("stuck"), "{error}");
}

/// What a split decides reaches the rest of the goal and the hypotheses
/// (issues/split-all-reduce-defined-heads.md,
/// issues/split-all-closed-tonat-literals.md): connectives and helpers at the
/// constructor a split substituted reduce, a binder introduced after a split
/// is restated simplified, and a comparison's fact against a literal is
/// stated at the literal, so plain `omega` closes a case two splits rule out.
fn splits_through_definitions() {
    checks("a predicate built with connectives", r#"
        fn newline(b: BitVec(8)) → Bool { !b.unsigned_lt_bit(BitVec::ofNat(10)) && b.unsigned_lt_bit(BitVec::ofNat(11)) }
        fn blank(b: BitVec(8)) → Bool { newline(b) || !b.unsigned_lt_bit(BitVec::ofNat(32)) && b.unsigned_lt_bit(BitVec::ofNat(33)) }
        fn step(count: Nat, b: BitVec(8)) → Nat { match newline(b) { False => count, True => Succ(count) } }
        theorem advances(count: Nat, b: BitVec(8)): step(count, b) <= Succ(count) { split_all; all_goals { omega } }
        theorem open_count(count: Nat): (b: BitVec(8)) → step(count, b) <= Succ(count) { split_all; all_goals { omega } }
        fn bit(x: Bool) → Nat { match x { True => 1, False => 0 } }
        theorem newline_blank(b: BitVec(8)): bit(newline(b)) <= bit(blank(b)) { split_all; all_goals { omega } }
    "#);
    checks("two splits' literals, compared by plain omega", r#"
        fn ten(b: BitVec(8)) → Bool { match b.unsigned_lt_bit(BitVec::ofNat(10)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(11)) } }
        fn low(b: BitVec(8)) → Bool { match b.unsigned_lt_bit(BitVec::ofNat(14)) { True => match b.unsigned_lt_bit(BitVec::ofNat(9)) { True => False, False => True }, False => False } }
        fn bit(x: Bool) → Nat { match x { True => 1, False => 0 } }
        theorem ten_is_low(b: BitVec(8)): bit(ten(b)) <= bit(low(b)) { split_all; all_goals { omega } }
    "#);
    checks("a helper at the constructor a split chose, and a hypothesis after it", r#"
        fn weight(cut: Bool) → Nat { match cut { True => 0, False => 1 } }
        fn wrap<A>(cut: Bool, x: A) → List<A> { match cut { True => Cons(x, Nil), False => Nil } }
        fn size<A>(xs: List<A>) → Nat { match xs { Nil => 0, Cons(_, _) => 1 } }
        theorem balanced<A>(x: A, xs: List<A>, total: Nat): (cut: Bool) → (total = weight(cut) + size(xs)) →
            total + size(wrap(cut, x)) = size(xs) + 1 {
            split_all; all_goals { omega }
        }
    "#);
    let error = refused("a false statement through a helper", r#"
        fn weight(cut: Bool) → Nat { match cut { True => 0, False => 1 } }
        fn wrap<A>(cut: Bool, x: A) → List<A> { match cut { True => Cons(x, Nil), False => Nil } }
        fn size<A>(xs: List<A>) → Nat { match xs { Nil => 0, Cons(_, _) => 1 } }
        theorem wrong<A>(x: A, xs: List<A>, total: Nat): (cut: Bool) → (total = weight(cut) + size(xs)) →
            total + size(wrap(cut, x)) = size(xs) {
            split_all; all_goals { omega }
        }
    "#);
    assert!(error.contains("no contradiction"), "{error}");
}

fn splits_stuck_comparisons() {
    checks("a restoring step split at its comparison", r#"
        fn place(s, threshold, weight: BitVec(8)) → BitVec(8) {
            match s.unsigned_lt_bit(threshold) {
                True => s, False => s.sub(threshold).add(weight)
            }
        }
        theorem kept(s: BitVec(8), small: s.toNat() < 10):
            place(s, BitVec::ofNat(10), BitVec::ofNat(1)).toNat() = s.toNat() {
            split_all; all_goals { bv_omega }
        }
        theorem taken(s: BitVec(8), lo: 10 <= s.toNat(), hi: s.toNat() < 100):
            place(s, BitVec::ofNat(10), BitVec::ofNat(1)).toNat() + 9 = s.toNat() {
            split_all; all_goals { bv_omega }
        }
        theorem both_branches(s: BitVec(8)):
            place(s, BitVec::ofNat(10), BitVec::ofNat(0)).toNat() <= s.toNat() {
            split_all; all_goals { bv_omega }
        }
        theorem open_threshold(s: BitVec(8), c: Nat, fits: 16 * c < 256):
            place(s, BitVec::ofNat(16 * c), BitVec::ofNat(0)).toNat() <= s.toNat() {
            split_all; all_goals { bv_omega }
        }
    "#);
    checks("open widths, nested comparisons, and finite locals", r#"
        fn minimum(n: Nat, a, b: BitVec(n)) → BitVec(n) {
            match a.unsigned_lt_bit(b) { True => a, False => b }
        }
        theorem bound(n: Nat, a, b, c: BitVec(n), flag: bool::Bool,
            __split_comparison: Nat):
            minimum(n, minimum(n, a, b), c).toNat() <= a.toNat() {
            split_all; all_goals { bv_omega }
        }
        theorem equal(n: Nat, a: BitVec(n)):
            minimum(n, a, a) = a {
            split_all; all_goals { bv_omega }
        }
        theorem nat_leaf(n: Nat, a, b: BitVec(n)): minimum(n, a, b).toNat() <= a.toNat() {
            split_all; all_goals { omega }
        }
        fn minimum3(n: Nat, a, b, c: BitVec(n)) → BitVec(n) {
            match a.unsigned_lt_bit(b) {
                True => match a.unsigned_lt_bit(c) { True => a, False => c },
                False => match b.unsigned_lt_bit(c) { True => b, False => c }
            }
        }
        theorem nested(n: Nat, a, b, c: BitVec(n)):
            minimum3(n, a, b, c).toNat() <= a.toNat() {
            split_all; all_goals { bv_omega }
        }
    "#);
    checks("a comparison split with a non-arithmetic leaf", r#"
        fn select(a, b: BitVec(8)) → bool::Bool {
            match a.unsigned_lt_bit(b) { True => True, False => False }
        }
        theorem same(a, b: BitVec(8)): select(a, b) = select(a, b) {
            split_all; all_goals { refl }
        }
    "#);
    let error = refused("a false comparison branch", r#"
        fn minimum(a, b: BitVec(8)) → BitVec(8) {
            match a.unsigned_lt_bit(b) { True => a, False => b }
        }
        theorem wrong(a, b: BitVec(8)): minimum(a, b).toNat() < a.toNat() {
            split_all; all_goals { bv_omega }
        }
    "#);
    assert!(error.contains("no contradiction"), "{error}");
    let error = refused("overflow in a comparison branch", r#"
        fn raise(a: BitVec(8)) → BitVec(8) {
            match a.unsigned_lt_bit(BitVec::ofNat(1)) {
                True => a, False => a.add(BitVec::ofNat(255))
            }
        }
        theorem wrong(a: BitVec(8)): a.toNat() <= raise(a).toNat() {
            split_all; all_goals { bv_omega }
        }
    "#);
    assert!(error.contains("may overflow 8 bits"), "{error}");
}

/// A comparison that computation decides, or that a later split decides
/// (issues/split-all-nested-scrutinee-kernel-reject.md): the case it
/// contradicts is closed by `absurd`, never handed to the leaf, and a
/// comparison over a match is split after the match, at the operand each
/// case has. The axes: closed comparisons under a finite local, open words on
/// either side of the equation, a checking position, a leaf other than `refl`,
/// and the negative control, a false statement whose `refl` leaf is refused
/// by the splitter itself, naming the case.
fn splits_comparisons_a_split_decides() {
    let decided = r#"
        fn zero() → BitVec(64) { BitVec::ofNat(0) }
        fn f(c: Bool) → Nat {
            match (match c { False => zero().unsigned_lt_bit(zero()), True => zero().eq_bit(zero()) }) {
                False => 0,
                True => 1,
            }
        }
        fn g(c: Bool) → Nat { match c { False => 0, True => 1 } }
    "#;
    checks("closed comparisons under a split", &format!("{decided}
        theorem f_g(c: Bool): f(c) = g(c) {{ split_all; all_goals {{ refl }} }}
        theorem f_g_omega(c: Bool): f(c) = g(c) {{ split_all; all_goals {{ omega }} }}
        theorem f_g_checking(c: Bool): f(c) = g(c) {{
            let p: (f(c) = g(c)) = {{ split_all; all_goals {{ refl }} }};
            p
        }}
    "));
    checks("a comparison over a match on open words", r#"
        fn one() → BitVec(64) { BitVec::ofNat(1) }
        fn h(c: Bool, x, y: BitVec(64)) → Nat {
            match (match c { False => x, True => y }).eq_bit(one()) { False => 0, True => 1 }
        }
        fn k(c: Bool, x, y: BitVec(64)) → Nat {
            match c {
                False => match x.eq_bit(one()) { False => 0, True => 1 },
                True => match y.eq_bit(one()) { False => 0, True => 1 },
            }
        }
        theorem h_k(c: Bool, x, y: BitVec(64)): h(c, x, y) = k(c, x, y) { split_all; all_goals { refl } }
        theorem k_h(c: Bool, x, y: BitVec(64)): k(c, x, y) = h(c, x, y) { split_all; all_goals { refl } }
        theorem bounded(c: Bool, x, y: BitVec(64)): h(c, x, y) <= 1 { split_all; all_goals { omega } }
    "#);
    let error = refused("a false value in a case the program reaches", &format!("{decided}
        theorem wrong(c: Bool): f(c) = 1 {{ split_all; all_goals {{ refl }} }}
    "));
    assert!(error.contains("`split_all` leaves the goal `0 = 1` in the case") && error.contains("which `refl` does not prove"), "{error}");
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
    let message = refused("an unbounded word_of_nat",
        "theorem self_sub(e: Nat): bitvec_nat::word_of_nat(64, e).sub(bitvec_nat::word_of_nat(64, e)).toNat() = 0 { bv_omega }");
    assert!(message.contains("does not fit 64 bits"), "{message}");
    checks("a bounded word_of_nat subtracted from itself",
        "theorem t(e: Nat, small: e < 1000): bitvec_nat::word_of_nat(64, e).sub(bitvec_nat::word_of_nat(64, e)).toNat() = 0 { bv_omega }");
    checks("a shared operand below the minuend",
        "theorem t(e: Nat, small: e < 1000): double(bitvec_nat::word_of_nat(64, e)).sub(bitvec_nat::word_of_nat(64, e)).toNat() = e { bv_omega }");
    checks("a variable word subtracted from itself",
        "theorem t(a: BitVec(64)): a.sub(a).toNat() = 0 { bv_omega }");
    let message = refused("an unbounded shared operand below the minuend",
        "theorem t(e: Nat): double(bitvec_nat::word_of_nat(64, e)).sub(bitvec_nat::word_of_nat(64, e)).toNat() = e { bv_omega }");
    assert!(message.contains("may overflow 64 bits"), "{message}");
    let message = refused("a wrong self subtraction",
        "theorem t(e: Nat, small: e < 1000): bitvec_nat::word_of_nat(64, e).sub(bitvec_nat::word_of_nat(64, e)).toNat() = 1 { bv_omega }");
    assert!(message.contains("no contradiction"), "{message}");
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

/// `omega` names its atom list by a transparent slot (docs/bv-omega-design.md
/// §6.1): an empty list, more `omega` calls than the declaration reserved
/// (one written call, copied into every branch, restarts it), two calls that
/// share a list, a list inside `bv_omega`'s proof, and a refusal.
fn names_atom_lists() {
    checks("no atoms", "theorem t(): 5 < nat::Nat::pow(2, 64) + 0 { omega }");
    checks("a literal word", "theorem t(): BitVec::ofNat(5, n := 64).toNat() = 5 { bv_omega }");
    checks("more calls than reserved",
        "theorem t(a, b: bool::Bool, v: Nat, small: v < 1000): v + v = 2 * v {\n\
             split_all;\n\
             all_goals { omega }\n\
         }");
    checks("two calls over one list", "theorem t(v, w: Nat, small: v < w): (v + 1 <= w) ∧ (v < w + 1) { omega }");
    checks("under binders", "theorem t(v: Nat): (w: Nat) → v < w → v + 1 <= w { λ w h => omega }");
    let message = refused("a false goal over a named list", "theorem t(v, w: Nat, small: v < w): w + 1 <= v { omega }");
    assert!(message.contains("no contradiction"), "{message}");
}

/// Calls that need no `omega` (docs/bv-omega-design.md §2–§3): a goal that
/// is a word's fact, as a value or a truncated difference, either way round,
/// at a literal and an open width; a leaf a fact defines, either way round,
/// and a cycle of definitions; a bound a fact states, strict and not; a
/// closed side condition. Then the optimistic first proof refused and the
/// careful one accepted, and the controls.
fn proves_what_is_written_down_without_search() {
    checks("a goal that is a word's fact",
        "theorem t(n: Nat, small: n < 16384): double(bitvec_nat::word_of_nat(64, n)).toNat() = n * 2 { bv_omega }");
    checks("flipped", "theorem t(n: Nat, small: n < 16384): 2 * n = double(bitvec_nat::word_of_nat(64, n)).toNat() { bv_omega }");
    checks("a truncated difference over a defined leaf",
        "theorem t(z: BitVec(64), k: Nat, zv: z.toNat() = k, small: k <= 3): BitVec::ofNat(5, n := 64).sub(z).toNat() = 5 -k { bv_omega }");
    checks("a truncated difference at an open width",
        "theorem t(n: Nat, a, b: BitVec(n), h: b.toNat() <= a.toNat()): a.sub(b).toNat() = a.toNat() -b.toNat() { bv_omega }");
    checks("a leaf defined the other way round",
        "theorem t(y: BitVec(64), v: Nat, value: v = y.toNat(), small: v < 1000): y.add(BitVec::ofNat(5)).toNat() = v + 5 { bv_omega }");
    checks("a cycle of definitions",
        "theorem t(a, b: BitVec(64), ab: a.toNat() = b.toNat(), ba: b.toNat() = a.toNat(), small: a.toNat() < 10):\n\
         a.add(BitVec::ofNat(1)).toNat() = b.toNat() + 1 { bv_omega }");
    checks("a stated strict bound", "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, bound: v * 256 < 1152921504606846976): times256(y).toNat() = v * 256 { bv_omega }");
    checks("a stated bound, not strict", "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, bound: 4 * v <= 1000): double(double(y)).toNat() = 4 * v { bv_omega }");
    checks("a closed side condition", "theorem t(): BitVec::ofNat(5, n := 64).add(BitVec::ofNat(7, n := 64)).toNat() = 12 { bv_omega }");
    // The optimistic proof restates `other`, whose sum overflows; refused,
    // the careful one leaves `other` alone.
    checks("an optional fact that overflows",
        "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, small: v < 1000,\n\
             other: double(y).add(BitVec::ofNat(18446744073709551615)).toNat() = 3): double(y).toNat() < 2001 { bv_omega }");
    // Controls: a stated bound past the width bounds nothing, and a goal of
    // a fact's shape with the wrong constant is still refused.
    let message = refused("a stated bound past the width",
        "theorem t(y: BitVec(64), v: Nat, value: y.toNat() = v, bound: v < 36893488147419103232): double(y).toNat() = 2 * v { bv_omega }");
    assert!(message.contains("may overflow 64 bits"), "{message}");
    let message = refused("a difference off by one",
        "theorem t(z: BitVec(64), k: Nat, zv: z.toNat() = k, small: k <= 3): BitVec::ofNat(5, n := 64).sub(z).toNat() = 6 -k { bv_omega }");
    assert!(message.contains("no contradiction"), "{message}");
}

fn lifts_bytes_comparisons_and_equality() {
    checks("low byte and remaining bytes",
        "theorem t(x: BitVec(16), lo, hi: Nat, v: x.toNat() = lo + 256 * hi, small: lo < 256): x.take_low(8, 8).toNat() = lo { bv_omega }\n\
         theorem u(x: BitVec(16), lo, hi: Nat, v: x.toNat() = lo + 256 * hi, small: lo < 256): x.drop_low(8, 8).toNat() = hi { bv_omega }");
    checks("extraction through definitions",
        "fn byte(x: BitVec(16)) → BitVec(8) { x.take_low(8, 8) }\n\
         theorem t(x: BitVec(16), lo, hi: Nat, v: x.toNat() = lo + 256 * hi, small: lo < 256): byte(x) = BitVec::ofNat(lo) { bv_omega }");
    checks("named aliases of both halves",
        "fn byte(x: BitVec(16)) → BitVec(8) { x.take_low(8, 8) }\n\
         fn tail(x: BitVec(16)) → BitVec(8) { x.drop_low(8, 8) }\n\
         theorem t(x: BitVec(16)): x.toNat() = byte(x).toNat() + 256 * tail(x).toNat() { bv_omega }");
    checks("word equality in a let annotation",
        "theorem t(a: BitVec(8), h: a.toNat() = 5): a.toNat() = BitVec::ofNat(5, n := 8).toNat() { let same: (a = BitVec::ofNat(5)) = bv_omega; @cong(λ (w: BitVec(8)) => w.toNat(), a, BitVec::ofNat(5), same) }");
    checks("extraction of arithmetic",
        "theorem t(x: BitVec(16), v: Nat, h: x.toNat() = v, small: v < 200): x.add(BitVec::ofNat(3)).take_low(8, 8).toNat() = v + 3 { bv_omega }");
    checks("nested extraction",
        "theorem t(x: BitVec(24), a, b, c: Nat, h: x.toNat() = a + 256 * (b + 256 * c), sa: a < 256, sb: b < 256): x.drop_low(8, 16).take_low(8, 8).toNat() = b { bv_omega }");
    checks("seven byte extractions",
        "theorem t(x: BitVec(64), a, b, c, d, e, f, g, h: Nat, value: x.toNat() = a + 256 * (b + 256 * (c + 256 * (d + 256 * (e + 256 * (f + 256 * (g + 256 * h)))))), sa: a < 256, sb: b < 256, sc: c < 256, sd: d < 256, se: e < 256, sf: f < 256, sg: g < 256): x.drop_low(8, 56).drop_low(8, 48).drop_low(8, 40).drop_low(8, 32).drop_low(8, 24).drop_low(8, 16).drop_low(8, 8).toNat() = h { bv_omega }");
    checks("a zero width half",
        "theorem t(x: BitVec(8)): x.take_low(0, 8).toNat() = 0 { bv_omega }");
    checks("open width decomposition",
        "theorem t(n, m: Nat, x: BitVec(m + n)): x.toNat() = x.take_low(n, m).toNat() + Nat::pow(2, n) * x.drop_low(n, m).toNat() { bv_omega }");
    checks("comparison at an open width",
        "theorem t(n: Nat, a, b: BitVec(n), h: bool::True = a.unsigned_lt_bit(b)): a.toNat() < b.toNat() { bv_omega }");
    checks("an optional comparison that wraps",
        "theorem t(a: BitVec(8), h: a.toNat() < 10, other: a.add(BitVec::ofNat(255)).unsigned_lt_bit(a) = bool::True): a.add(BitVec::ofNat(1)).toNat() < 11 { bv_omega }");
    checks("open width word equality",
        "theorem t(n: Nat, a, b: BitVec(n), h: a.toNat() = b.toNat()): a = b { bv_omega }");
    checks("word arithmetic equality",
        "theorem t(a: BitVec(8), h: a.toNat() < 100): a.add(BitVec::ofNat(1)) = BitVec::ofNat(a.toNat() + 1) { bv_omega }");
    checks("unsigned true and false goals",
        "theorem t(a, b: BitVec(8), h: a.toNat() < b.toNat()): a.unsigned_lt_bit(b) = bool::True { bv_omega }\n\
         theorem u(a, b: BitVec(8), h: b.toNat() <= a.toNat()): bool::False = a.unsigned_lt_bit(b) { bv_omega }");
    checks("unsigned comparison hypotheses",
        "theorem t(a, b: BitVec(8), h: a.unsigned_lt_bit(b) = bool::True): a.toNat() < b.toNat() { bv_omega }\n\
         theorem u(a, b: BitVec(8), h: bool::False = a.unsigned_lt_bit(b)): b.toNat() <= a.toNat() { bv_omega }");
    checks("comparison of arithmetic words",
        "theorem t(a: BitVec(8), h: a.toNat() < 100): a.add(BitVec::ofNat(1)).unsigned_lt_bit(BitVec::ofNat(101)) = bool::True { bv_omega }");
    checks("equal words compare false", "theorem t(a: BitVec(8)): a.unsigned_lt_bit(a) = bool::False { bv_omega }");
    for (what, body) in [
        ("wrong low byte", "theorem t(x: BitVec(16), h: x.toNat() = 257): x.take_low(8, 8).toNat() = 2 { bv_omega }"),
        ("wrong high byte", "theorem t(x: BitVec(16), h: x.toNat() = 257): x.drop_low(8, 8).toNat() = 2 { bv_omega }"),
        ("out of range byte", "theorem t(x: BitVec(16), h: x.toNat() = 256): x.take_low(8, 8) = BitVec::ofNat(1) { bv_omega }"),
        ("wrapping comparison", "theorem t(a: BitVec(8), h: a.toNat() = 255): a.add(BitVec::ofNat(1)).unsigned_lt_bit(a) = bool::False { bv_omega }"),
        ("wrong word equality", "theorem t(a: BitVec(8), h: a.toNat() = 2): a = BitVec::ofNat(3) { bv_omega }"),
        ("false unsigned comparison", "theorem t(a: BitVec(8)): a.unsigned_lt_bit(a) = bool::True { bv_omega }"),
    ] {
        refused(what, body);
    }
}

// Byte decomposition uses intervals with two finite endpoints. Their
// positive combinations must reconstruct both endpoints through checked
// lemmas, including when unrelated range rows affect the search route.
fn reconstructs_bounded_combinations() {
    checks("a bounded combination with extra ranges",
        "theorem t(s, t, v: Nat, value: s = v, small: v < 1000, first: t = v + v, r0: s < Nat::pow(2, 64), r1: t < Nat::pow(2, 64)): 2 * t + 0 < Nat::pow(2, 64) + 0 { omega }");
    refused("a false bound with the same ranges",
        "theorem t(s, t, v: Nat, value: s = v, small: v < 1000, first: t = v + v, r0: s < Nat::pow(2, 64), r1: t < Nat::pow(2, 64)): 2 * t < 1000 { omega }");
}

/// `split_all` over words (docs/goal-combinators.md): a word local is never
/// split into its bits, and a comparison is found through the helpers that
/// spell it, or through a match on another one, with its Nat fact at each
/// leaf.
#[test]
fn split_all_finds_comparisons_through_helpers() {
    checks("a comparison behind a helper", "
fn low(x: BitVec(8)) → Bool { x.unsigned_lt_bit(BitVec::ofNat(10)) }
fn pick(x: BitVec(8), n: Nat) → Nat { match low(x) { True => n, False => Succ(n) } }
theorem pick_grows(x: BitVec(8), n: Nat): n <= pick(x, n) {
    split_all;
    all_goals { omega }
}");
    checks("a comparison under a match on another", "
fn space(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(14)) { True => True, False => b.unsigned_lt_bit(BitVec::ofNat(33)) }
}
fn count(b: BitVec(8), n: Nat) → Nat { match space(b) { True => Succ(n), False => n } }
theorem count_bounded(b: BitVec(8), n: Nat): count(b, n) <= Succ(n) {
    split_all;
    all_goals { omega }
}");
    checks("the leaf reads the comparison as Nats", "
fn below(x: BitVec(8)) → Bool { x.unsigned_lt_bit(BitVec::ofNat(10)) }
theorem small(x: BitVec(8)): match below(x) { True => x.toNat() < 10, False => 10 <= x.toNat() } {
    split_all;
    all_goals { bv_omega }
}");
    let error = refused("a leaf the comparison does not prove", "
fn below(x: BitVec(8)) → Bool { x.unsigned_lt_bit(BitVec::ofNat(10)) }
theorem wrong(x: BitVec(8)): match below(x) { True => x.toNat() < 9, False => 10 <= x.toNat() } {
    split_all;
    all_goals { bv_omega }
}");
    assert!(error.contains("bv_omega"), "{error}");
}
