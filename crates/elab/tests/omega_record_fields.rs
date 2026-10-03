//! Acceptance for issues/omega-record-projection-atoms.md: a record field is
//! an `omega` atom. A closed record whose spine is not dependent registers no
//! projection definitions, so `s.words` elaborates to the inline Σ walk, and
//! the speller now names that walk `s.words` from the receiver's type. Rows:
//! a field of a local, of a call and of a field; a fact about a call's field
//! in scope; a field read off a record value and off a `match` on a literal
//! (a motive's instance), each reflected as what it computes to; two field
//! reads whose receivers convert; an open element type; `omega` in a
//! checking position. The controls: a false claim over fields is refused and
//! names the atoms `s.words` and `s.bytes`, and a motive's field that
//! computes to `Succ(s.words)` is not below `s.words`.

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
    // As in `omega_atoms_computation.rs`: one libtest worker fills the cold
    // image store, the others wait and replay it.
    let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    support::semantic_test_base(MODULES).semantic_image()
}

fn base() -> Elaborator {
    BASE.with(|base| base.get_or_init(load_image).elaborator())
}

const PRELUDE: &str = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport omega;\n\
    record WcState { lines: Nat, words: Nat, bytes: Nat, inside: Bool }\n\
    record Outer { tag: Bool, inner: WcState, n: Nat }\n\
    fn wc_next(space: Bool, s: WcState) → WcState {\n\
        match space { True => WcState(s.lines, s.words, Succ(s.bytes), False), \
                      False => WcState(s.lines, Succ(s.words), Succ(s.bytes), True) }\n\
    }\n";

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
fn a_field_of_a_local_is_an_atom() {
    ok("theorem x2(s: WcState, a: Nat): s.words + a = a + s.words { omega }");
}

#[test]
fn a_field_of_a_call_and_of_a_field_are_atoms() {
    ok("theorem v6(s: WcState, sp: Bool, h: wc_next(sp, s).words <= s.words + 1): wc_next(sp, s).words < s.words + 2 { omega }");
    ok("theorem v7(o: Outer, a: Nat, h: o.inner.bytes = a + 1): a < o.inner.bytes + o.n { omega }");
}

#[test]
fn a_fact_about_a_field_in_scope_does_not_sink_an_unrelated_goal() {
    ok("theorem v5(w: Nat, s: WcState, sp: Bool, h: wc_next(sp, s).bytes = w): w + 0 = w { omega }");
}

#[test]
fn a_field_read_off_a_record_value_is_what_it_computes_to() {
    ok("theorem lit(x: Nat, h: WcState(0, 3, 0, False).words + x = 5): x = 2 { omega }");
    // Through a `let`, which inlines the value into the fact's type.
    ok("theorem via_let(x: Nat): x + 0 = x { let z = WcState(0, 3, 0, False); let h: (z.words + x = x + 3) = omega; omega }");
}

const MOTIVE: &str = "(match i as λ _ => WcState { True => WcState(s.lines, Succ(s.words), s.bytes, True), False => s }).words";

#[test]
fn a_motive_field_at_a_literal_is_what_it_computes_to() {
    ok(&format!(
        "theorem m(s: WcState, b: Bool): (match b as λ _ => WcState {{ True => WcState(s.lines, Succ(s.words), s.bytes, True), False => s }}).words <= s.words + 1 {{\n\
            match b as λ i => {MOTIVE} <= s.words + 1 {{ True => omega, False => omega }}\n\
        }}"
    ));
}

#[test]
fn a_motive_field_that_computes_to_a_successor_is_not_below_the_field() {
    let msg = elab_err(&format!(
        "theorem m_bad(s: WcState, b: Bool): (match b as λ _ => WcState {{ True => WcState(s.lines, Succ(s.words), s.bytes, True), False => s }}).words <= s.words {{\n\
            match b as λ i => {MOTIVE} <= s.words {{ True => omega, False => omega }}\n\
        }}"
    ));
    assert!(msg.contains("got stuck"), "{msg}");
    assert!(msg.contains("s.words"), "{msg}");
}

#[test]
fn field_reads_whose_receivers_convert_are_one_atom() {
    ok("theorem conv(g: List<Nat> → WcState, h: g(list::List::append(Nil, Nil)).words = g(Nil).words + 1): False { omega }");
}

#[test]
fn a_field_at_an_open_element_type_is_an_atom() {
    ok("record Tally<A> { item: A, count: Nat }\n\
        theorem open_tally<A>(t: Tally<A>, u: Tally<A>, h: t.count + 2 = u.count): t.count < u.count { omega }");
}

#[test]
fn a_field_atom_in_a_checking_position() {
    ok("theorem chk(s: WcState, t: WcState, h: s.words = t.words + 3): t.words < s.words {\n\
            let k: (t.words + 3 = s.words) = omega;\n\
            omega\n\
        }");
}

#[test]
fn a_false_claim_over_fields_is_refused_and_names_them() {
    let msg = elab_err("theorem bad(s: WcState): s.words + 1 = s.bytes { omega }");
    assert!(msg.contains("got stuck"), "{msg}");
    assert!(msg.contains("s.words") && msg.contains("s.bytes"), "{msg}");
}

/// A goal a definition unfolds to (docs/native-stream-filter-design.md §2.4):
/// `filter_program`'s `advances` default meets `counts_advance` at no count and
/// at one, which omega reads only once the head is unfolded, stopping at the
/// relation rather than inside `Le`'s recursor, with the count applied.
const ADVANCE: &str = "fn advance<C>(counts: List<C → Nat>) → C → C → Type {\n\
        match counts {\n\
            Nil => λ next carry => True,\n\
            Cons(count, rest) => match rest {\n\
                Nil => λ next carry => count(next) <= Succ(count(carry)),\n\
                Cons(_, _) => λ next carry => (count(next) <= Succ(count(carry))) ∧ advance(rest)(next, carry),\n\
            },\n\
        }\n\
    }\n";

#[test]
fn a_goal_a_definition_unfolds_to_is_read_unfolded() {
    ok(&format!("{ADVANCE}theorem none(s: WcState): advance<WcState>(Nil)(wc_next(True, s), s) {{ omega }}"));
    ok(&format!("{ADVANCE}theorem one(s: WcState, sp: Bool): advance<WcState>([λ t => t.bytes])(wc_next(sp, s), s) {{ \
        match sp as λ b => advance<WcState>([λ t => t.bytes])(wc_next(b, s), s) {{ True => omega, False => omega }} }}"));
    let msg = elab_err(&format!("{ADVANCE}theorem two(s: WcState): advance<WcState>([λ t => t.bytes])(WcState(0, 0, Succ(Succ(s.bytes)), False), s) {{ omega }}"));
    assert!(msg.contains("got stuck"), "{msg}");
}

/// A field of a definition that unfolds to a constructor reads as what was
/// put there (docs/native-stream-filter-design.md §2.4): a counting step's
/// `.next` is its fold's next count, which `split_all`'s leaf hands omega
/// instead of a spelling of the projection omega can't re-elaborate.
#[test]
fn a_field_of_an_unfolding_definition_is_what_it_holds() {
    let counting = "record Out { next: Nat, flag: Bool }\n\
        fn counting(g: Nat → Nat) → Nat → Out { λ s => Out(g(s), False) }\n";
    ok(&format!("{counting}theorem grows(x: Nat): counting(λ n => Succ(n))(x).next <= Succ(x) {{ split_all; all_goals {{ omega }} }}"));
    let msg = elab_err(&format!("{counting}theorem leaps(x: Nat): counting(λ n => Succ(Succ(n)))(x).next <= Succ(x) {{ split_all; all_goals {{ omega }} }}"));
    assert!(msg.contains("got stuck"), "{msg}");
}
