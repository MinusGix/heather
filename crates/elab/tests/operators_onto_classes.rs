//! Designations and `Monoid(+)` — operators onto classes
//! (`docs/operators-onto-classes-design.md`, the acceptance list of §10).
//!
//! The one sentence the whole feature is: an operator symbol is a **name in a
//! namespace of its own**, and a `designation` is what puts a meaning in it at
//! a carrier — so `+` means `add` at `Nat`, `or` at `Bool` and `append` at
//! `List<A>`, and a constraint that names the symbol (`<A: Monoid(+)>`) both
//! installs it locally and fills its index from the table at the caller's
//! carrier.
//!
//! The symbol's resolution is a three-rung ladder — a constraint binder that
//! named it, then the designation at the operand's carrier, then the symbol's
//! fixed fallback name — and the third rung *is* the parser desugaring this
//! round replaced. That is the **growth invariant**, and it has its own
//! section here: `crates/elab/tests/operators.rs` still pins the whole Nat
//! suite written in `+` with no designation in sight, and the tests below add
//! the two cases that suite cannot make (a file that defines its *own* `add`,
//! and a file where the library's designation is loaded).
//!
//! Carriers are `std/bool`, `std/nat` and `std/list`, for the reason
//! `operation_indexed_classes.rs` records: `Bool` has two genuinely different
//! operations, so nothing passes vacuously. `docs/testing-generated-terms.md`'s
//! axes are varied deliberately — every rule appears at an **open** element
//! type and at a **concrete** carrier, in a **checking** position (a `theorem`
//! whose statement is the equation), with a **negative control** beside it,
//! and at a **literal** scrutinee that has to compute as well as a **neutral**
//! one that cannot.
//!
//! The load-bearing tests, if only four are read:
//! `one_fold_three_carriers_no_caller_names_an_operation` (§10 item 1),
//! `the_fallback_rung_is_the_old_desugaring` (item 3),
//! `two_symbols_at_one_carrier_nominate_nothing` (item 4), and
//! `the_concrete_carrier_refusal_names_the_designations` (item 8 — the
//! regression this round decided to *keep*, pinned positively).

use heather_elab::{ElabError, Elaborator};

const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");

/// The test's own chain and instances, plus the four designations the library
/// declares. `Sem` → `Mon` → `CMon` at one index each, so the upcast machinery
/// is exercised without the library's names being the thing under test.
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

instance CMon<Nat>(add) {
    unit := 0, assoc := add_assoc, unit_l := add_left_zero,
    unit_r := λ (x: Nat) => refl, comm := add_comm,
}
instance CMon<Bool>(and) {
    unit := True, assoc := and_assoc, unit_l := and_true_l,
    unit_r := and_true_r, comm := and_comm,
}
instance CMon<Bool>(or) {
    unit := False, assoc := or_assoc, unit_l := or_false_l,
    unit_r := or_false_r, comm := or_comm,
}
instance<A> Mon<List<A>>(append) {
    unit := Nil, assoc := append_assoc,
    unit_l := λ (xs: List<A>) => refl, unit_r := append_nil,
}

designation + at Nat := add
designation + at Bool := or
designation * at Bool := and
designation<A> + at List<A> := append

fn fold<A: Mon(op)>(op: A -> A -> A, xs: List<A>) -> A {
    match xs { Nil => A.unit, Cons(h, t) => op(h, fold(op, t)) }
}

fn sum_all<A: Mon(+)>(xs: List<A>) -> A { fold(+, xs) }
"#;

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [("bool", BOOL), ("nat", NAT), ("option", OPTION), ("list", LIST)] {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(format!("{name}: {err}"));
        }
    }
    let src = format!("import bool;\nimport nat;\nimport option;\nimport list;\n{P}\n{extra}");
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
        Ok(_) => panic!("expected a refusal, but it checked:\n{extra}"),
    }
}

/// A source with **no** designation anywhere: the prelude, and whatever the
/// caller declares. This is what every file written before this round looks
/// like, and it is where the fallback rung has to be the only thing that runs.
fn bare(src: &str) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => Ok(e),
        Err(ElabError::Elab { msg, .. }) => Err(msg),
        Err(other) => Err(format!("{other}")),
    }
}

// -- §10 item 1: the headline ----------------------------------------------

/// One generic fold, written in notation, spent at **three** carriers with no
/// caller naming an operation — `Nat` (→ `add`), `Bool` (→ `or`), and an
/// **open** element type (→ `append`, where the generic designation and the
/// generic instance have to meet).
///
/// Each is pinned by `refl` against the positional spelling, so the sugar and
/// the written form are one term and not merely two things that both check.
/// The literal/neutral axis is varied at every carrier.
#[test]
fn one_fold_three_carriers_no_caller_names_an_operation() {
    ok("
        fn s(ns: List<Nat>) -> Nat { sum_all(ns) }
        fn a(bs: List<Bool>) -> Bool { sum_all(bs) }
        fn c<B>(xss: List<List<B>>) -> List<B> { sum_all(xss) }

        // The designation and the positional index are one term.
        theorem s_is_add(ns: List<Nat>): s(ns) = fold(add, ns) { refl }
        theorem a_is_or(bs: List<Bool>): a(bs) = fold(or, bs) { refl }
        theorem c_is_append<B>(xss: List<List<B>>): c(xss) = fold(append, xss) { refl }

        // A **literal** scrutinee, which has to compute all the way.
        theorem s_lit(): s(Cons(2, Cons(3, Nil))) = 5 { refl }
        theorem a_lit(): a(Cons(False, Cons(True, Nil))) = True { refl }

        // A **neutral** one, which cannot: the fold is stuck on `ns`, and the
        // agreement above is what carries it.
        theorem s_neutral(n: Nat, ns: List<Nat>): s(Cons(n, ns)) = add(n, s(ns)) { refl }
    ");
}

/// The negative control on the headline: the designation at `Nat` does **not**
/// answer at `Bool`. `sum_all` at `Bool` is disjunction, and saying it is
/// conjunction is a kernel rejection.
#[test]
fn a_designation_does_not_travel_between_carriers() {
    let e = bad("
        fn a(bs: List<Bool>) -> Bool { sum_all(bs) }
        theorem wrong(bs: List<Bool>): a(bs) = fold(and, bs) { refl }
    ");
    assert!(e.contains("NotConvertible") || e.contains("kernel"), "{e}");
}

// -- §10 item 2: theory in notation ----------------------------------------

/// The statement is the mathematics: `x + A.unit = x` at a `CMon(+)` binder,
/// where the `+` is the **bound index** and not an ambient operator — the
/// signature, not only the body, so the installation has to cover the whole
/// declaration.
///
/// Its three corollaries still pin their index by **unification alone**, from
/// their own goals. `bool_and_true` is the one that says the ladder's order
/// out loud: `+` designates `or` at `Bool`, the goal says `and`, and
/// unification is the first rung, so the designation is never consulted. A
/// designation supplies an index nothing else pinned; it never overrides one.
#[test]
fn theory_is_written_in_notation_and_its_corollaries_still_unify() {
    ok("
        theorem unit_of_comm<A: CMon(+)>(x: A): x + A.unit = x {
            trans(A.comm(x, A.unit), A.unit_l(x))
        }
        theorem nat_add_zero(x: Nat): add(x, 0) = x { unit_of_comm(x) }
        theorem bool_and_true(x: Bool): and(x, True) = x { unit_of_comm(x) }
        theorem bool_or_false(x: Bool): or(x, False) = x { unit_of_comm(x) }
    ");
}

/// The negative control beside it: the *wrong* unit is still refused. `or`'s
/// unit is `False`, and `unit_of_comm` cannot be made to say otherwise.
#[test]
fn the_wrong_unit_is_still_refused_under_a_symbol_binder() {
    let e = bad("
        theorem unit_of_comm<A: CMon(+)>(x: A): x + A.unit = x {
            trans(A.comm(x, A.unit), A.unit_l(x))
        }
        theorem nope(x: Bool): or(x, True) = x { unit_of_comm(x) }
    ");
    assert!(!e.is_empty(), "{e}");
}

/// The symbol installs for this declaration and **no further**: a second
/// declaration with no `(+)` gets the fallback rung, not the neighbour's
/// binder.
#[test]
fn an_installed_symbol_does_not_leak_out_of_its_declaration() {
    // `+` here is `add` by designation at `Nat`, not the previous
    // declaration's index — which is what makes it type-check at all.
    ok("
        theorem inside<A: CMon(+)>(x: A): x + A.unit = x {
            trans(A.comm(x, A.unit), A.unit_l(x))
        }
        theorem outside(x: Nat, y: Nat): x + y = add(x, y) { refl }
    ");
}

// -- §10 item 3: the growth invariant --------------------------------------

/// The third rung **is** the parser desugaring this round replaced, so a file
/// with no designation gets exactly the term it got before — including a file
/// whose `add` is its *own*, which is the case the fallback exists for and the
/// one a designation would silently change if the rungs were the other way
/// round.
#[test]
fn the_fallback_rung_is_the_old_desugaring() {
    // (a) A file's own `add`, no designations anywhere. `+` is that `add`.
    bare("
        fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
        theorem t(x: Nat, y: Nat): x + y = add(x, y) { refl }
        theorem lit(): 2 + 2 = 4 { refl }
    ")
    .expect("a file with no designation is the fallback rung, unchanged");

    // (b) `<=` and `<` have no designations in the library and never had one
    //     here: `<=` is `Le`, the *proposition*, exactly as before.
    bare("
        fn Le(n: Nat, m: Nat) -> Type<0> { n = m }
        theorem t(n: Nat, m: Nat, h: n <= m): Le(n, m) { h }
        theorem u(n: Nat, m: Nat, h: Le(n, m)): n <= m { h }
    ")
    .expect("`<=` still names `Le` by the fallback rung");
}

/// (c) With the library's designation *loaded*, `+` at `Nat` is still
/// `nat::add` — same term, pinned by `refl`. The designation and the fallback
/// agree at `Nat` by construction, which is the whole reason the migration is
/// not a behaviour change.
#[test]
fn a_designation_at_nat_agrees_with_the_name_it_replaced() {
    ok("
        theorem t(x: Nat, y: Nat): x + y = add(x, y) { refl }
        theorem lit(): 2 + 2 = 4 { refl }
        // Left-associative and precedence-respecting, as ever.
        theorem chain(a: Nat, b: Nat, c: Nat): a + b + c = add(add(a, b), c) { refl }
    ");
}

// -- §10 item 4: two symbols at one carrier --------------------------------

/// `+` is `or` and `*` is `and` at `Bool`, both monoids still registered, and
/// a fold under each symbol gives its own operation. This is the sentence that
/// no nomination happened: the design's whole claim is that two structures at
/// one carrier coexist, and here they coexist *in notation*.
#[test]
fn two_symbols_at_one_carrier_nominate_nothing() {
    ok("
        fn prod_all<A: Mon(*)>(xs: List<A>) -> A { fold(*, xs) }

        theorem plus_is_or(x: Bool, y: Bool): x + y = or(x, y) { refl }
        theorem star_is_and(x: Bool, y: Bool): x * y = and(x, y) { refl }

        theorem sum_is_or(bs: List<Bool>): sum_all(bs) = fold(or, bs) { refl }
        theorem prod_is_and(bs: List<Bool>): prod_all(bs) = fold(and, bs) { refl }

        // Both compute, at a literal scrutinee, to different answers.
        theorem sum_lit(): sum_all(Cons(False, Cons(True, Nil))) = True { refl }
        theorem prod_lit(): prod_all(Cons(False, Cons(True, Nil))) = False { refl }
    ");
}

/// The negative control: the two are not interchangeable. If they were, the
/// coexistence above would be vacuous.
#[test]
fn the_two_symbols_do_not_meet() {
    let e = bad("
        fn prod_all<A: Mon(*)>(xs: List<A>) -> A { fold(*, xs) }
        theorem nope(bs: List<Bool>): sum_all(bs) = prod_all(bs) { refl }
    ");
    assert!(!e.is_empty(), "{e}");
}

// -- §10 item 5: refusals as data ------------------------------------------

/// Every refusal the declaration form owes, checked for **content**.
#[test]
fn the_designation_declaration_refuses_by_name() {
    // A duplicate at one key names the previous entry and where it was written.
    let e = bad("designation + at Nat := add");
    assert!(e.contains("already designates"), "{e}");
    assert!(e.contains("nat::add"), "{e}");
    assert!(e.contains("one entry per (symbol, carrier head)"), "{e}");
    // ... and the reason two operations at one carrier are not a duplicate.
    assert!(e.contains("two *symbols*"), "{e}");

    // A right-hand side that is not a bare name, with the reason.
    let e = bad("designation * at Nat := λ (a: Nat) (b: Nat) => a");
    assert!(e.contains("must be a bare global name"), "{e}");
    assert!(e.contains("instantiated there"), "{e}");

    // An unknown right-hand side, caught where it is written.
    let e = bad("designation * at Nat := no_such_operation");
    assert!(e.contains("no_such_operation"), "{e}");

    // A carrier that names no type in scope.
    let e = bad("designation * at NoSuchType := add");
    assert!(e.contains("NoSuchType"), "{e}");
    assert!(e.contains("attaches to nothing"), "{e}");

    // A carrier with no head at all.
    let e = bad("designation * at (Nat -> Nat) := add");
    assert!(e.contains("no head type name"), "{e}");

    // The positive control: a *third* symbol at `Nat` is not a duplicate, and
    // a fourth carrier for `+` is not either.
    ok("designation * at Nat := add
        designation + at Option := add");
}

/// An instance head names its index by the **operation**, never by a symbol —
/// otherwise the registry key would depend on the designation table's state at
/// declaration time, which is the one thing the key exists not to depend on.
#[test]
fn an_instance_head_will_not_take_a_symbol() {
    let e = bad("instance Mon<Option<Nat>>(+) { unit := None, assoc := ?a, unit_l := ?b, unit_r := ?c }");
    assert!(e.contains("by the **operation**, not by a symbol"), "{e}");
    assert!(e.contains("designation"), "{e}");
}

/// A symbol with no rung at all reports the **symbol as written** and what
/// would have had to be true — never "unbound name `mul`", which names
/// something the writer did not type.
#[test]
fn a_symbol_with_no_rung_names_the_symbol() {
    // `*` at `Nat`: no binder named it, no designation covers `Nat`, and its
    // fallback name `mul` is nowhere.
    let e = bad("theorem t(x: Nat, y: Nat): x * y = x { ?p }");
    assert!(e.contains("`*` has no meaning here"), "{e}");
    assert!(e.contains("<A: Monoid(*)>"), "{e}");
    assert!(e.contains("fallback name `mul`"), "{e}");
    // It says where `*` *does* mean something, as data.
    assert!(e.contains("`Bool`"), "{e}");
    assert!(e.contains("bool::and"), "{e}");
}

/// §5.1: each of the index slot's three referents binds exactly one spelling,
/// and a symbol slot's is the symbol. A bare `op` under `<A: Mon(+)>` is
/// therefore bound by nothing, and says which spelling works instead of
/// "unbound name".
#[test]
fn a_symbol_slot_binds_the_symbol_and_not_the_declared_name() {
    let e = bad("fn f<A: Mon(+)>(x: A, y: A) -> A { op(x, y) }");
    assert!(e.contains("binds it under the SYMBOL"), "{e}");
    assert!(e.contains("write `x + y`"), "{e}");
    assert!(e.contains("three referents"), "{e}");
    // The positive control, physically beside it: the symbol *is* the binder.
    ok("fn f<A: Mon(+)>(x: A, y: A) -> A { x + y }");
    // And the empty slot still binds the declared name, untouched.
    ok("fn g<A: Mon>(x: A, y: A) -> A { op(x, y) }");
}

// -- §10 item 8: the concrete-carrier regression, kept on purpose ----------

/// The decision this round was asked to make and made **against** recovering:
/// a designation is keyed per *symbol*, the dot sugar names no symbol, and
/// choosing among the symbols designated at a carrier would be a nomination
/// mechanism — which is §9.2 of the operation-indexed design rebuilt under a
/// new name. So `Bool.unit` is still refused.
///
/// What the round does instead is the polish: the refusal **names the
/// designations that exist** and spells the binder that would use them. Pinned
/// positively, because it is a decision and not an accident.
#[test]
fn the_concrete_carrier_refusal_names_the_designations() {
    let e = bad("theorem t(): Bool { Bool.unit }");
    // The refusal itself, and the three-rung ladder in its sentence.
    assert!(e.contains("not pinned here"), "{e}");
    assert!(e.contains("a designation the binder names"), "{e}");
    assert!(e.contains("never by search"), "{e}");
    // Both structures, as data — neither preferred.
    assert!(e.contains("Mon<Bool>(and)"), "{e}");
    assert!(e.contains("Mon<Bool>(or)"), "{e}");
    // The polish: the designations here, and the spelling that works.
    assert!(e.contains("`+` designates `bool::or`"), "{e}");
    assert!(e.contains("`*` designates `bool::and`"), "{e}");
    assert!(e.contains("take the class as a constraint that names the symbol"), "{e}");
    // And it still offers the dictionary spelling.
    assert!(e.contains("Bool::Mon("), "{e}");

    // The two positive controls, physically beside it: the dictionary
    // spelling, and the constraint that names the symbol.
    ok("theorem t(): Bool::Mon(or).unit = False { refl }");
    ok("fn u<A: Mon(+)>() -> A { A.unit }");

    // A carrier with *no* designation gets the refusal without the clause,
    // rather than a dangling sentence about nothing.
    let e = bad("
        inductive Col { R, G }
        class Mag<A>(op: A -> A -> A) { tag: A }
        fn cfst(a: Col, b: Col) -> Col { a }
        instance Mag<Col>(cfst) { tag := R }
        theorem t(): Col { Col.tag }
    ");
    assert!(e.contains("not pinned here"), "{e}");
    assert!(!e.contains("designates"), "{e}");
}

// -- the ladder's own order and the probe ----------------------------------

/// Rung 1 beats rung 2: inside `<A: Mon(+)>` the `+` is the bound index at
/// *every* carrier, including one where a designation exists and says
/// something else. Instantiating the generic function at `Bool` with `and`
/// gives `and`, not the designated `or`.
#[test]
fn a_binder_that_names_the_symbol_beats_the_table() {
    ok("
        fn f<A: Mon(+)>(x: A, y: A) -> A { x + y }
        theorem at_and(x: Bool, y: Bool): @f(and, Bool::Mon(and), x, y) = and(x, y) { refl }
        theorem at_or(x: Bool, y: Bool): @f(or, Bool::Mon(or), x, y) = or(x, y) { refl }
    ");
}

/// Rung 2's probe descends the left spine to the leftmost non-operator leaf
/// (§4.1), which is what keeps a chain linear rather than exponential and what
/// makes a mixed-symbol chain read its carrier correctly. Three deep, both
/// symbols, at both carriers.
#[test]
fn the_carrier_probe_descends_the_left_spine() {
    ok("
        theorem b3(x: Bool, y: Bool, z: Bool): x + y + z = or(or(x, y), z) { refl }
        theorem n3(a: Nat, b: Nat, c: Nat): a + b + c = add(add(a, b), c) { refl }
        // Mixed symbols: `*` binds tighter, and the outer `+`'s left operand
        // is the leaf `x` either way.
        theorem mixed(x: Bool, y: Bool, z: Bool): x * y + z = or(and(x, y), z) { refl }
        theorem mixed2(x: Bool, y: Bool, z: Bool): x + y * z = or(x, and(y, z)) { refl }
    ");
}

/// A bare symbol between delimiters is the designation reference, and it is a
/// *value* there: `fold(+, xs)` passes the binder's index positionally, which
/// is how the library's `sum_all` is one term with `fold`.
#[test]
fn a_bare_symbol_between_delimiters_is_the_index() {
    ok("
        theorem one_term<A: Mon(+)>(xs: List<A>): sum_all(xs) = fold(+, xs) { refl }
    ");
    // The one argument position where a bare symbol *does* have a carrier is
    // the qualified name, which wrote it: `Bool::Mon(+)` is the `or` monoid.
    ok("theorem d(): Bool::Mon(+).unit = False { refl }");
    // Elsewhere a bare symbol has no operand and so no carrier (§4): in an
    // ordinary argument it can only be rung 1 or the fallback, and the
    // boundary is pinned rather than assumed away.
    let e = bad("theorem c(bs: List<Bool>): fold(+, bs) = fold(or, bs) { refl }");
    assert!(!e.is_empty(), "{e}");
}

/// The receiver and type-projection sugars still work **under** a symbol
/// binder — the ladder's step 2 (scope) is unchanged by any of this, and the
/// upcast rides two hops up the chain with the symbol's binder as the index.
#[test]
fn the_dot_sugars_work_under_a_symbol_binder() {
    ok("
        theorem assoc_up<A: CMon(+)>(x: A, y: A, z: A): (x + y) + z = x + (y + z) {
            x.assoc(y, z)
        }
        fn unit_of<A: CMon(+)>() -> A { A.unit }
    ");
}

/// Unindexed classes are untouched, and so is every operator expression that
/// has nothing to do with them — the growth invariant stated once more from
/// the class side.
#[test]
fn unindexed_classes_and_ordinary_calls_are_unchanged() {
    ok("
        class Def<A> { d: A }
        instance Def<Nat> { d := 0 }
        instance Def<Bool> { d := False }
        fn get<A>(x: Def<A> := infer) -> A { x.d }
        theorem t(): get<Nat>() = 0 { refl }
        theorem u(): Nat.d = 0 { refl }
    ");
}
