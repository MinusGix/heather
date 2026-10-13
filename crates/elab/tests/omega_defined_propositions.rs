//! Acceptance for issues/omega-unfolds-defined-propositions.md: omega reads a
//! fact or goal whose head is a defined proposition as the relation it
//! unfolds to, and a `Nat`/`Int` atom that computes to `Succ(…)`/`OfNat(…)`
//! as that arithmetic. Rows: a fact through a defined `<=`, `<` and `=` at
//! `Int` and `Nat`, negated, at literal arguments and at an open element
//! type; a goal through a defined equation; `omega` in a checking position;
//! a call computing to a successor or to `OfNat`, a field of a call that
//! unfolds to a constructor, a factor that computes to a numeral; a fact
//! stated through `Int::cong` of a function literal. The controls: a
//! proposition stuck on a match is still skipped, a false claim through a
//! defined fact is refused, and a call stuck on a match stays an atom.

use std::cell::OnceCell;
use std::sync::Mutex;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/omega.hthr");

/// The same prefix, in the same order, as `semantic_omega_warmup.rs`, so the
/// on-disk image keys this file reads are the ones the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("int", INT),
    ("omega", OMEGA),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn load_image() -> SemanticImage {
    // As in `omega_record_fields.rs`: one libtest worker fills the cold
    // image store, the others wait and replay it.
    let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    support::semantic_test_base(MODULES).semantic_image()
}

fn base() -> Elaborator {
    BASE.with(|base| base.get_or_init(load_image).elaborator())
}

const PRELUDE: &str = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport int;\nimport omega;\n\
    fn Below(x, y: Int) → Type { x + OfNat(1) <= y }\n\
    fn NBelow(m, n: Nat) → Type { m < n }\n\
    fn Within(m, n: Nat) → Type { m <= n }\n\
    fn Balanced(x, y: Int) → Type { x + y = OfNat(0) }\n\
    fn Small(b: Bool, n: Nat) → Type { match b { True => n <= 3, False => n <= 5 } }\n\
    record P { pred: Nat }\n\
    fn P::val(self p: P) → Nat { Succ(p.pred) }\n\
    fn P::int(self p: P) → Int { OfNat(Succ(p.pred)) }\n\
    fn P::twice(self p: P) → P { P(p.pred + p.pred + 1) }\n\
    fn P::one() → P { P(0) }\n\
    record Q { num: Int, den: P }\n\
    fn Q::add(self x, y: Q) → Q { Q(x.num + y.num, x.den) }\n\
    fn Q::unit() → Q { Q(OfNat(1), P::one()) }\n\
    fn bump(b: Bool, n: Nat) → Nat { match b { True => Succ(n), False => n } }\n";

fn ok(src: &str) {
    let mut e = base();
    e.elab_module_source("m", &format!("{PRELUDE}{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err}"));
}

fn elab_err(src: &str) -> String {
    let mut e = base();
    match e.elab_module_source("m", &format!("{PRELUDE}{src}")) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

#[test]
fn a_fact_through_a_defined_relation_is_read_unfolded() {
    ok("theorem i(a, b: Int, h: Below(a, b)): a < b { omega }");
    ok("theorem n(a, b: Nat, h: NBelow(a, b)): a + 1 <= b { omega }");
    ok("theorem w(a, b, c: Nat, h: Within(a, b), k: Within(b, c)): a <= c { omega }");
    ok("theorem e(a, b: Int, h: Balanced(a, b)): b = OfNat(0) - a { omega }");
}

#[test]
fn a_negated_defined_fact_is_read_unfolded() {
    ok("theorem neg(a, b: Nat, h: ¬NBelow(a, b)): b <= a { omega }");
}

#[test]
fn a_defined_fact_at_literal_arguments() {
    ok("theorem lit(n: Nat, h: NBelow(3, n)): 4 <= n { omega }");
}

#[test]
fn a_defined_fact_at_an_open_element_type() {
    ok("record Tally<A> { item: A, count: Nat }\n\
        fn Full<A>(t: Tally<A>) → Type { 3 <= t.count }\n\
        theorem open_full<A>(t: Tally<A>, h: Full<A>(t)): 2 < t.count { omega }");
}

#[test]
fn a_goal_through_a_defined_equation_is_read_unfolded() {
    ok("theorem g(a: Int): Balanced(a, OfNat(0) - a) { omega }");
    ok("theorem gl(a, b: Nat, h: a < b): NBelow(a, b + 1) { omega }");
}

#[test]
fn a_defined_fact_in_a_checking_position() {
    ok("theorem chk(a, b: Nat, h: NBelow(a, b)): a < b + 1 {\n\
            let k: (a + 1 <= b) = omega;\n\
            omega\n\
        }");
}

#[test]
fn a_call_computing_to_a_successor_or_of_nat_is_that_arithmetic() {
    ok("theorem v(p: P): 1 <= p.val() { omega }");
    ok("theorem iv(p: P): OfNat(1) <= p.int() { omega }");
    ok("theorem both(p: P): p.int() = OfNat(p.val()) { omega }");
}

#[test]
fn a_field_of_a_call_is_what_the_call_put_there() {
    ok("theorem t(p: P): p.pred <= p.twice().pred { omega }");
    ok("theorem tv(p: P): p.val() < p.twice().val() + 1 { omega }");
    ok("theorem q(x, y: Q): x.add(y).num = x.num + y.num { omega }");
}

#[test]
fn a_factor_that_computes_to_a_numeral_scales() {
    ok("theorem f(x: Q): x.num * Q::unit().num = x.num { omega }");
    ok("theorem nf(n: Nat): n * P::one().val() = n { omega }");
}

#[test]
fn a_fact_from_cong_of_a_function_literal_is_read() {
    ok("theorem c(e, a, b: Int, p: a = b): e * a = e * b {\n\
            let f = Int::cong(λ (t: Int) => e * t, p);\n\
            omega\n\
        }");
}

#[test]
fn a_proposition_stuck_on_a_match_is_still_skipped() {
    let msg = elab_err("theorem stuck(b: Bool, n: Nat, h: Small(b, n)): n <= 5 { omega }");
    assert!(msg.contains("got stuck"), "{msg}");
    // The same fact at a literal scrutinee computes and is read.
    ok("theorem lit(n: Nat, h: Small(True, n)): n <= 5 { omega }");
}

#[test]
fn a_false_claim_through_a_defined_fact_is_refused() {
    let msg = elab_err("theorem bad(a, b: Nat, h: NBelow(a, b)): b <= a { omega }");
    assert!(msg.contains("got stuck"), "{msg}");
}

#[test]
fn a_call_stuck_on_a_match_stays_an_atom() {
    let msg = elab_err("theorem stuck(b: Bool, n: Nat): 1 <= bump(b, n) { omega }");
    assert!(msg.contains("got stuck"), "{msg}");
    assert!(msg.contains("bump"), "{msg}");
}
