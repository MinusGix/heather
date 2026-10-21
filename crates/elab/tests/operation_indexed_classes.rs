//! Operation-indexed classes — `class Monoid<A>(op)`
//! (`docs/operation-indexed-classes-design.md`, round one of §13).
//!
//! The one sentence the whole feature is: the operation moves from field to
//! **index**, so `Mon<Bool>(Bool::and)` and `Mon<Bool>(Bool::or)` are different *types*,
//! both register as equals, and a goal whose value slot nothing pins is
//! refused by name rather than answered by a nomination.
//!
//! The classes here are the test's own — `lib_algebra.rs` is where the
//! *library's* declarations are checked — but the carriers are `std/bool`,
//! `std/nat` and `std/list`, deliberately. A one-element carrier was tried
//! first and thrown away: its values are all definitionally equal, so every
//! negative control passed vacuously (`docs/testing-generated-terms.md`'s axis
//! 4, met the hard way). Two genuinely different operations on one genuinely
//! two-element carrier is the minimum this feature can be tested at.
//!
//! The other axes are varied deliberately too: every rule appears at an
//! **open** carrier (a constrained type parameter) and at a **concrete** one,
//! in a **checking** position (a `theorem` whose statement is the equation),
//! with a **negative control** beside it, and — where a fold is involved — at
//! a **literal** scrutinee that has to compute as well as at a **neutral** one
//! that cannot.
//!
//! The load-bearing tests, if only four are read: `one_law_three_structures`
//! (§13 item 1), `the_value_slot_refusal_lists_every_answer` (item 4),
//! `the_equal_arity_rule_and_its_negative_control` (item 7), and
//! `the_linked_slot_forward_references` (item 8).

use std::sync::OnceLock;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");

/// The classes and the instances, declared in the probe module itself so that
/// every one of them is this test's own claim and not the library's.
const P: &str = r#"
class Sem<A>(op: A -> A -> A) {
    assoc: (x: A) -> (y: A) -> (z: A) -> op(op(x, y), z) = op(x, op(y, z)),
}
class Mon<A>(op: A -> A -> A) extends Sem<A>(op) {
    unit: A,
    unit_l: (x: A) -> op(unit, x) = x,
    unit_r: (x: A) -> op(x, unit) = x,
}
class CMon<A>(op: A -> A -> A) extends Mon<A>(op) {
    comm: (x: A) -> (y: A) -> op(x, y) = op(y, x),
}

instance CMon<Bool>(Bool::and) {
    assoc := Bool::and_assoc, unit := True,
    unit_l := Bool::and_true_l, unit_r := Bool::and_true_r, comm := Bool::and_comm,
}
instance CMon<Bool>(Bool::or) {
    assoc := Bool::or_assoc, unit := False,
    unit_l := Bool::or_false_l, unit_r := Bool::or_false_r, comm := Bool::or_comm,
}
instance CMon<Nat>(Nat::add) {
    assoc := Nat::add_assoc, unit := 0,
    unit_l := Nat::add_left_zero, unit_r := λ (x: Nat) => refl, comm := Nat::add_comm,
}
instance<A> Mon<List<A>>(List::append) {
    assoc := List::append_assoc, unit := Nil,
    unit_l := λ (xs: List<A>) => refl, unit_r := List::append_nil,
}
"#;

// The fixed prefix, built once per process and forked per probe
// (`support::process_base`): isolated committed state, not a shared mutable
// elaborator.
static BASE: OnceLock<Result<SemanticImage, String>> = OnceLock::new();

fn build_base() -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in
        [("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION), ("pair", PAIR), ("list", LIST)]
    {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(format!("{name}: {err}"));
        }
    }
    let src = format!("import bool;\nimport nat;\nimport option;\nimport list;\n{P}");
    match e.elab_module_source("probe", &src) {
        Ok(()) => Ok(e),
        Err(ElabError::Elab { msg, .. }) => Err(msg),
        Err(other) => Err(format!("{other}")),
    }
}

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = support::process_base(&BASE, build_base)?;
    let src = format!("import bool;\nimport nat;\nimport option;\nimport list;\n{extra}");
    match e.elab_module_source("probe", &src) {
        Ok(()) => Ok(e),
        Err(ElabError::Elab { msg, .. }) => Err(msg),
        Err(other) => Err(format!("{other}")),
    }
}

fn ok(extra: &str) -> Elaborator {
    run(extra).unwrap_or_else(|e| panic!("expected this to check, got: {e}"))
}

fn bad(extra: &str) -> String {
    match run(extra) {
        Err(e) => e,
        Ok(_) => panic!("expected a refusal, but it checked"),
    }
}

// ---------------------------------------------------------------------------
// §13 item 1 — the headline.

/// One generic law, proved once against `CMon`, spent at three structures —
/// **two of them on one carrier**. Each corollary's goal names its operation,
/// so the index is pinned by unification alone (§4.2); nothing is passed and
/// nothing is searched for in a value slot.
#[test]
fn one_law_three_structures() {
    ok("
theorem op_unit_of_comm<A: CMon>(x: A): op(x, A.unit) = x {
  trans(A.comm(x, A.unit), A.unit_l(x))
}
theorem at_add(x: Nat):  x.add(0)     = x { op_unit_of_comm(x) }
theorem at_and(x: Bool): x.and(True)  = x { op_unit_of_comm(x) }
theorem at_or(x: Bool):  x.or(False)  = x { op_unit_of_comm(x) }
");
}

/// The negative control for the headline: the law is about *this* structure's
/// unit, so the wrong one is refused rather than derived. Without it a proof
/// that silently found the other Bool monoid would pass every test above.
#[test]
fn slow_acceptance_the_wrong_unit_is_refused() {
    let e = bad("
theorem law<A: CMon>(x: A): op(x, A.unit) = x {
  trans(A.comm(x, A.unit), A.unit_l(x))
}
theorem nope(x: Bool): x.or(True) = x { law(x) }
");
    // The refusal is unmoved; what it reads like moved on 2026-09-15 with
    // `docs/telescoped-record-projections-design.md`'s device — `A.unit` is a
    // named projection, so the mismatch is caught in the checking position and
    // the message names the two types rather than the declaration. Assert the
    // substance (see `lib_algebra.rs`'s twin).
    assert!(
        e.contains(".unit") && e.contains("or(x, True) = x"),
        "the wrong unit must be refused, naming both sides: {e}"
    );
}

// ---------------------------------------------------------------------------
// §13 item 2 — coexistence.

/// Both structures registered at one carrier, and a ground goal at each finds
/// its own — including down the whole `extends` chain, which is synthesized
/// twice at `Bool` and never meets itself.
#[test]
fn slow_acceptance_both_structures_register_and_each_ground_goal_finds_its_own() {
    ok("
theorem and_unit(): Bool::Mon(Bool::and).unit = True  { refl }
theorem or_unit():  Bool::Mon(Bool::or).unit  = False { refl }
theorem and_left(x: Bool): Bool::and(True, x)  = x { Bool::Mon(Bool::and).unit_l(x) }
theorem or_left(x: Bool):  Bool::or(False, x)  = x { Bool::Mon(Bool::or).unit_l(x) }
// the index is the key at every level of the chain.
theorem chain(): Bool::Sem(Bool::or).assoc = Bool::CMon(Bool::or).assoc { refl }
");
}

/// …and the negative control: the two chains at one carrier do not leak into
/// each other.
#[test]
fn slow_acceptance_the_two_chains_at_one_carrier_do_not_meet() {
    let e = bad("theorem nope(): Bool::Mon(Bool::or).unit = True { refl }");
    assert!(e.contains("nope"), "{e}");
}

/// A duplicate at one key is the declaration error it always was, and the
/// message names the **index** as part of the key.
#[test]
fn slow_acceptance_a_duplicate_at_one_index_names_the_index() {
    let e = bad("instance Sem<Bool>(Bool::and) { assoc := Bool::and_assoc }");
    assert!(e.contains("already has an instance"), "{e}");
    assert!(e.contains("index"), "{e}");
    // The positive control beside it: the same declaration at a *third* index
    // is an ordinary declaration, because the key distinguishes it.
    ok("
fn nand(a: Bool, b: Bool) -> Bool { a.and(b).not() }
class Mag<A>(op: A -> A -> A) { pt: A }
instance Mag<Bool>(nand) { pt := True }
instance Mag<Bool>(Bool::and)  { pt := True }
instance Mag<Bool>(Bool::or)   { pt := False }
");
}

// ---------------------------------------------------------------------------
// §13 item 3 — the binder.

/// The EMPTY slot binds the index under the class's own declared parameter
/// name, so the body writes `op` as an ordinary variable and `A.unit` is
/// answered by the binder in scope. The index arrives at the call by
/// unification from the *statement* (theory's case, §4.1's style rule).
#[test]
fn slow_acceptance_the_empty_slot_binds_the_index_under_its_declared_name() {
    ok("
theorem twice<A: Mon>(x: A): op(x, A.unit) = op(x, A.unit) { refl }
// at an open carrier the binder answers; at a concrete one the statement pins
// the index and the registry answers.
theorem at_and(x: Bool): x.and(True) = x.and(True) { twice(x) }
theorem at_add(x: Nat):  x.add(0)    = x.add(0)    { twice(x) }
");
}

/// The index filled **from the room**: a generic function calling another
/// generic function has nothing in its own statement to pin the callee's
/// index, and the binder it already holds is what pins it (§5's ladder, step
/// 2). This is the recursive-call case in its smallest honest form.
#[test]
fn slow_acceptance_a_generic_call_fills_its_index_from_the_room() {
    ok("
fn twice<A: Mon>(x: A) -> A { op(x, A.unit) }
fn quad<A: Mon>(x: A) -> A { twice(twice(x)) }
// …and it computes at carriers the generic code never mentioned, with the
// index supplied at the outermost call and nowhere else.
theorem at_and(x: Bool):
  @quad(Bool::and, Bool::Mon(Bool::and), x) = x.and(True).and(True) { refl }
theorem at_or(x: Bool):
  @quad(Bool::or, Bool::Mon(Bool::or), x) = x.or(False).or(False) { refl }
");
}

/// The `@` escape supplies an empty slot's index by hand — §4.1's interim
/// form until named arguments land. Note what it costs: `@` suppresses *all*
/// implicit insertion, so the dictionary has to be written beside the index.
/// That is the whole reason the design routes programs to the linked slot and
/// leaves the empty one to theory.
#[test]
fn slow_acceptance_an_empty_slot_can_be_supplied_by_hand() {
    ok("
fn twice<A: Mon>(x: A) -> A { op(x, A.unit) }
fn conj(x: Bool) -> Bool { @twice(Bool::and, Bool::Mon(Bool::and), x) }
fn disj(x: Bool) -> Bool { @twice(Bool::or, Bool::Mon(Bool::or), x) }
theorem they_differ(): conj(False) = False { refl }
theorem and_the_other(): disj(True) = True { refl }
");
}

/// The generic instance at an **open** element type, reached by backchaining
/// with the index instantiated at the same time as the carrier.
#[test]
fn slow_acceptance_a_generic_instance_answers_at_an_open_element_type() {
    ok("
fn fold<A: Mon(o)>(o: A -> A -> A, xs: List<A>) -> A {
  match xs { Nil => A.unit, Cons(h, t) => o(h, fold(o, t)) }
}
// open: `B` is the probe's own parameter, so only `instance<A> Mon<List<A>>`
// can answer, and its index is `append` at that very `B`.
fn flatten<B>(xss: List<List<B>>) -> List<B> { fold(List::append, xss) }
// …and it computes at a closed one.
theorem flattens(): flatten(Cons(Cons(1, Nil), Nil)) = Cons(1, Nil) { refl }
// checking position at the open type, dictionary never named.
fn flatten_then<B>(xss: List<List<B>>, ys: List<B>) -> List<B> {
  flatten(xss).append(ys)
}
");
}

// ---------------------------------------------------------------------------
// §13 item 4 — refusals as data.

/// A value slot that survives the ladder is refused **by name**, and the
/// refusal lists every registered instance that would answer *at this
/// carrier*, with its index. Checked for content: the slot, the class, both
/// structures — and the absence of the ones at other carriers.
#[test]
fn the_value_slot_refusal_lists_every_answer() {
    // (a) `T.f` at an indexed class with no scope binder — the boundary
    //     `docs/traits-type-projection-design.md` §6 left open, decided here
    //     as scope-then-refuse.
    let e = bad("fn nope() -> Bool { Bool.unit }");
    assert!(e.contains("not pinned"), "{e}");
    assert!(e.contains("`op`") && e.contains("Mon"), "the slot and the class: {e}");
    assert!(e.contains("Mon<Bool>(Bool::and)") && e.contains("Mon<Bool>(Bool::or)"), "both: {e}");
    assert!(!e.contains("Mon<Nat>(Nat::add)"), "\"would answer\" means at this carrier: {e}");

    // (b) a call whose index nothing pins.
    let e = bad("
fn twice<A: Mon>(x: A) -> A { op(x, A.unit) }
fn go(x: Bool) -> Bool { twice(x) }
");
    assert!(e.contains("not pinned"), "{e}");
    assert!(e.contains("`op`"), "{e}");

    // (c) an unspellable instance-head index, refused at the declaration with
    //     the scope alternative stated.
    let e = bad("instance Sem<Bool>(λ (a: Bool) (b: Bool) => a) { assoc := Bool::and_assoc }");
    assert!(e.contains("spellable"), "{e}");
    assert!(e.contains("scope"), "the alternative is stated: {e}");
}

/// A receiver at a concrete carrier is the same refusal: the receiver fixes
/// the carrier and nothing fixes the operation (§5.1).
#[test]
fn slow_acceptance_receiver_dispatch_at_a_concrete_carrier_is_refused_by_name() {
    let e = bad("theorem nope(a: Bool, b: Bool, c: Bool):
  a.and(b).and(c) = a.and(b.and(c)) { a.assoc(b, c) }");
    assert!(e.contains("not pinned"), "{e}");
    assert!(e.contains("Sem<Bool>(Bool::and)") && e.contains("Sem<Bool>(Bool::or)"), "{e}");
    // …and the spelling the refusal points at does work.
    ok("theorem yes(a: Bool, b: Bool, c: Bool):
  a.and(b).and(c) = a.and(b.and(c)) { Bool::Sem(Bool::and).assoc(a, b, c) }");
}

/// Under a binder the same receiver dispatches, at the class that *declares*
/// the member, with the index taken from the binder and the answer reached by
/// upcast — two hops up the chain from `CMon`.
#[test]
fn slow_acceptance_receiver_dispatch_under_a_binder_upcasts_with_the_index() {
    ok("
theorem assoc_from_a_monoid<A: Mon(o)>(o: A -> A -> A, x: A, y: A, z: A):
  o(o(x, y), z) = o(x, o(y, z)) { x.assoc(y, z) }
theorem assoc_from_a_comm_monoid<A: CMon(o)>(o: A -> A -> A, x: A, y: A, z: A):
  o(o(x, y), z) = o(x, o(y, z)) { x.assoc(y, z) }
");
}

// ---------------------------------------------------------------------------
// §13 item 5 — keying up to conversion.

/// A definitionally-equal alias and an eta-expansion both find the
/// `and`-keyed instance: selection is by checked trial, and the kernel is what
/// compares two operations.
#[test]
fn slow_acceptance_an_alias_and_an_eta_expansion_find_the_keyed_instance() {
    ok("
fn conj(x: Bool, y: Bool) -> Bool { x.and(y) }
fn need<A: Mon(o)>(o: A -> A -> A, x: A) -> A { o(x, A.unit) }
theorem by_alias(x: Bool): need(conj, x) = conj(x, True) { refl }
theorem by_eta(x: Bool):
  need(λ (a: Bool) (b: Bool) => a.and(b), x) = x.and(True) { refl }
");
}

/// The negative control: an operation that is genuinely a different function
/// does **not** match. Without this, "up to conversion" would be
/// indistinguishable from "any operation of the right type".
#[test]
fn slow_acceptance_a_different_operation_does_not_match() {
    let e = bad("
fn nand(a: Bool, b: Bool) -> Bool { a.and(b).not() }
fn need<A: Mon(o)>(o: A -> A -> A, x: A) -> A { o(x, A.unit) }
fn go(x: Bool) -> Bool { need(nand, x) }
");
    assert!(e.contains("Mon<A>(o)") || e.contains("no instance"), "{e}");
    // …and the trace is data: each candidate is named with the index it is
    // keyed at, which is the observability hook of §11.
    assert!(e.contains("index `bool::Bool::and`"), "{e}");
    assert!(e.contains("index `bool::Bool::or`"), "{e}");
}

// ---------------------------------------------------------------------------
// §13 item 6 — checking position, and the agreement pins.

/// The two spellings reach **one term**: the anonymous one that projects from
/// the type and the one that names the dictionary, related by `refl`, at an
/// open carrier and at a concrete one, with a literal case that computes.
#[test]
fn slow_acceptance_the_spellings_are_one_term() {
    ok("
fn anon<A: Mon(o)>(o: A -> A -> A, x: A) -> A { o(x, A.unit) }
theorem anon_is_the_dictionary<A> requires m: Mon<A>(o) (o: A -> A -> A, x: A):
  anon(o, x) = o(x, m.unit) { refl }
// concrete, through the index-bearing spelling.
theorem at_and(x: Bool): anon(Bool::and, x) = x.and(Bool::Mon(Bool::and).unit) { refl }
// literal, and it has to compute.
theorem computes(): anon(Bool::or, False) = False { refl }
// neutral, and it cannot.
theorem neutral(x: Nat): anon(Nat::add, x) = x.add(0) { refl }
");
}

// ---------------------------------------------------------------------------
// §13 item 7 — the unifier rule and its negative control.

/// The equal-arity flex-rigid rule (§4.2): the corollary's goal is
/// `?op(x, ?u) ≟ add(x, 0)` — a flex-headed spine against a rigid
/// global-headed one of the *same* length — so the head is solved and the
/// arguments decompose. Without the rule `?op` survives and the ladder
/// refuses.
#[test]
fn the_equal_arity_rule_and_its_negative_control() {
    ok("
theorem law<A: CMon>(x: A): op(x, A.unit) = x {
  trans(A.comm(x, A.unit), A.unit_l(x))
}
theorem spent(x: Nat): x.add(0) = x { law(x) }
");
    // The guard's own recorded counterexample, kept as this rule's control: a
    // flex spine of length 1 against a rigid spine of length 2 still learns
    // nothing, so nothing is peeled and the call is refused rather than
    // "solved" as `?f := add(a)`.
    let e = bad("
theorem apply1<A>({f: A -> A}, {a: A}): f(a) = f(a) { refl }
theorem peeled(x: Nat): x.add(x) = x.add(x) { apply1() }
");
    assert!(e.contains("could not infer") || e.contains("cannot infer"), "{e}");
}

// ---------------------------------------------------------------------------
// §13 item 8 — the linked slot.

/// The NAME referent: the index is linked to an explicit parameter of the same
/// declaration, **written before it**, and supplied positionally at the call.
/// The written order stays authoritative for the call site.
#[test]
fn the_linked_slot_forward_references() {
    ok("
fn fold<A: Mon(o)>(o: A -> A -> A, xs: List<A>) -> A {
  match xs { Nil => A.unit, Cons(h, t) => o(h, fold(o, t)) }
}
// positional, no `:= infer` tail, no `requires`.
theorem all_of(): fold(Bool::and, Cons(True, Cons(False, Nil))) = False { refl }
theorem any_of(): fold(Bool::or,  Cons(True, Cons(False, Nil))) = True  { refl }
theorem empty_and(): fold(Bool::and, Nil) = True  { refl }
theorem empty_or():  fold(Bool::or,  Nil) = False { refl }
// neutral scrutinee: nothing reduces past the element.
theorem single(x: Nat): fold(Nat::add, Cons(x, Nil)) = x.add(0) { refl }
");
}

/// A name in an index slot that is neither a parameter of this declaration nor
/// a global is refused, naming the one forward reference the language has.
#[test]
fn slow_acceptance_an_index_that_names_nothing_is_refused() {
    let e = bad("fn f<A: Mon(nope)>(x: A) -> A { x }");
    assert!(e.contains("not a parameter"), "{e}");
}

/// The cycle: the constraint's index names a parameter whose own type names
/// the constraint. Refused **by name** rather than ordered by guess.
#[test]
fn slow_acceptance_a_dependency_cycle_is_refused_by_name() {
    let e = bad(
        "theorem cyc<A> requires m: Mon<A>(o) (p: m.unit = m.unit, o: A -> A -> A):
  m.unit = m.unit { refl }",
    );
    assert!(e.contains("depend on each other"), "{e}");
    assert!(e.contains("`m`") && e.contains("`p`"), "both named: {e}");
}

/// Two constraints of one class, distinguished by their linked names (§5.2) —
/// and the bare declared name, which binds nothing there, refused naming both.
#[test]
fn slow_acceptance_two_constraints_of_one_class() {
    ok("
fn both<A: Mon(f) + Mon(g)>(f: A -> A -> A, g: A -> A -> A, x: A) -> A {
  f(g(x, x), x)
}
theorem at_bool(x: Bool): both(Bool::and, Bool::or, x) = x.or(x).and(x) { refl }
");
    let e = bad("fn bare<A: Mon + Mon>(x: A) -> A { op(x, x) }");
    assert!(e.contains("twice"), "{e}");
    assert!(e.contains("Mon<A>"), "both constraints named: {e}");
}

// ---------------------------------------------------------------------------
// §13 item 9 — the index pseudo-projection.

/// `d.op` at `d: Mon<A>(and)` is `and`, read off the dictionary's type — at a
/// concrete carrier and at an open one.
#[test]
fn slow_acceptance_the_index_pseudo_projection() {
    ok("
theorem concrete requires m: Mon<Bool>(Bool::and) (x: Bool, y: Bool):
  m.op(x, y) = x.and(y) { refl }
theorem open<A> requires m: Mon<A>(o) (o: A -> A -> A, x: A, y: A):
  m.op(x, y) = o(x, y) { refl }
");
}

/// The negative control: a name that is a **field** still resolves as a field,
/// and a name that is neither is still the ordinary error.
#[test]
fn slow_acceptance_a_field_is_still_a_field() {
    ok("theorem the_unit requires m: Mon<Bool>(Bool::and) (x: Bool): m.unit.and(x) = x {
  m.unit_l(x)
}");
    let e = bad("theorem nope requires m: Mon<Bool>(Bool::and) (): m.wat = True { refl }");
    assert!(e.contains("wat"), "{e}");
}

// ---------------------------------------------------------------------------
// The growth invariant: unindexed classes are untouched.

/// Nothing in this round changes a class with no value parameters — every rule
/// above is gated on a non-empty index list, and this is the control that says
/// so.
#[test]
fn slow_acceptance_unindexed_classes_are_unchanged() {
    ok("
class Def<A> { d: A }
instance Def<Bool> { d := False }
instance Def<Nat>  { d := 0 }
fn get<A: Def>() -> A { A.d }
fn at_bool() -> Bool { get() }
theorem computes(): at_bool() = False { refl }
");
    // …and a second instance at one carrier is still the duplicate error, with
    // no index in the message because there is none.
    let e = bad("
class Def2<A> { d: A }
instance Def2<Bool> { d := False }
instance Def2<Bool> { d := True }
");
    assert!(e.contains("already has an instance"), "{e}");
    assert!(!e.contains("at the index"), "{e}");
}
