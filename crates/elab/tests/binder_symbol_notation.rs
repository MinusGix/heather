//! `op as ∙` — symbol notation on declaring binders
//! (`issues/binder-symbol-as-notation.md`).
//!
//! The one sentence: a binder may carry a symbol *as notation* while keeping
//! its identifier *as interface*. `op` is still the name everywhere a name is
//! consulted — the empty constraint slot binds it, a linked slot refers to it,
//! the registry and the diagnostics say it — and `∙` is the spelling of that
//! same referent inside the declaration's own body. Two places declare a
//! binder and so two places take the device: a class head's index parameter,
//! and a value parameter of a `fn`/`theorem`.
//!
//! Nothing new resolves. `as` installs into the very table the constraint
//! symbol slot installs into (`docs/operators-onto-classes-design.md` §5(b),
//! rung 1 of §4's ladder), so a symbol away from a binder still falls through
//! rungs 2 and 3 exactly as before — which for `∙`, the reserved generic
//! operator, means *nothing*: no designation anywhere and no fallback name.
//!
//! `docs/testing-generated-terms.md`'s axes are varied deliberately: every
//! rule below appears at an **open** element type as well as a concrete
//! carrier, in a **checking** position (a `theorem` whose statement spells the
//! symbol) and not only in a computing one, at a **literal** scrutinee that
//! must compute and a **neutral** one that cannot, and with a **negative
//! control** beside it.
//!
//! The load-bearing tests, if only four are read:
//! `the_class_head_spells_its_own_laws` (customer 1),
//! `a_value_parameter_spells_the_telescope_the_statement_and_the_body`
//! (customer 2), `the_reserved_generic_symbol_means_nothing_off_a_binder`
//! (the negative control the reservation exists for), and
//! `a_declaration_installs_each_spelling_once` (§5.2 over both namespaces).

use std::cell::OnceCell;

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");

/// The test's own chain, written in the notation under test: three classes
/// whose heads carry `op as ∙`, and the instances that fill them — none of
/// which mentions a symbol, which is the point.
///
/// `Bool` carries two of them, so nothing here passes vacuously: `and` and
/// `or` are both `CMon<Bool>` and neither is "the" one.
const P: &str = r#"
class Sem<A>(op as ∙: A -> A -> A) {
    assoc: (x, y, z: A) -> (x ∙ y) ∙ z = x ∙ (y ∙ z),
}

class Mon<A>(op as ∙: A -> A -> A) extends Sem<A>(op) {
    unit: A,
    unit_l: (x: A) -> unit ∙ x = x,
    unit_r: (x: A) -> x ∙ unit = x,
}

class CMon<A>(op as ∙: A -> A -> A) extends Mon<A>(op) {
    comm: (x, y: A) -> x ∙ y = y ∙ x,
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

fn fold<A: Mon(op)>(op as ∙: A -> A -> A, xs: List<A>) -> A {
    match xs { Nil => A.unit, Cons(h, t) => h ∙ fold(op, t) }
}
"#;

// Clone the fixed prefix per probe. `Elaborator`'s clone is deliberately a
// cheap isolated snapshot; thread-local storage pays the prefix at most once
// on each of libtest's two worker threads.
thread_local! {
    static BASE: OnceCell<Result<Elaborator, String>> = const { OnceCell::new() };
}

fn build_base() -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION), ("pair", PAIR), ("list", LIST)] {
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
    let mut e = BASE.with(|base| base.get_or_init(build_base).clone())?;
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
        Ok(_) => panic!("expected a refusal, but it checked:\n{extra}"),
    }
}

// -- customer 1: the class head --------------------------------------------

/// The head writes `op as ∙` and the laws read as mathematics. The whole of
/// what changed is *inside* the class body: `P` above declares its instances
/// with no symbol in sight, and they fill exactly the fields they filled
/// before — so the notation cost the downstream nothing.
///
/// Spent three ways at once: a generic consumer whose index the caller names
/// positionally, a concrete carrier reached through the dictionary spelling,
/// and an **open** element type where the generic instance answers.
#[test]
fn the_class_head_spells_its_own_laws() {
    ok("
        // Generic, at a linked slot: the law comes from the class and the
        // caller of the law names nothing.
        theorem up<A: Mon(op)>(op: A -> A -> A, x: A, y: A, z: A):
            op(op(x, y), z) = op(x, op(y, z))
        { A.assoc(x, y, z) }

        // A concrete carrier, through the dictionary — two structures at one
        // carrier, and the law is each one's own.
        theorem at_and(x: Bool, y: Bool, z: Bool):
            and(and(x, y), z) = and(x, and(y, z))
        { Bool::Sem(and).assoc(x, y, z) }
        theorem at_or(x: Bool, y: Bool, z: Bool):
            or(or(x, y), z) = or(x, or(y, z))
        { Bool::Sem(or).assoc(x, y, z) }

        // An **open** element type: `up`'s dictionary is found by backchaining
        // through `instance<A> Mon<List<A>>(append)` at the caller's own
        // parameter, and the law it delivers is the one the head spelled.
        theorem at_list<B>(xs: List<B>, ys: List<B>, zs: List<B>):
            append(append(xs, ys), zs) = append(xs, append(ys, zs))
        { up(append, xs, ys, zs) }
    ");
}

/// The identifier is still the **interface**, which is the sentence that makes
/// the whole device free: the empty slot binds the class's declared name, a
/// linked slot binds the caller's own, and neither has heard of a symbol.
#[test]
fn slow_acceptance_the_identifier_is_still_the_interface_spelling() {
    ok("
        // The EMPTY slot binds `op`, the class's declared parameter name —
        // exactly as before the head carried a symbol.
        fn twice<A: Mon>(x: A) -> A { op(x, x) }
        // The LINKED slot refers to the caller's own parameter by name.
        fn twice2<A: Mon(f)>(f: A -> A -> A, x: A) -> A { f(x, x) }
    ");
    // And the symbol is *not* a second interface: a class head's `as` is
    // strictly local notation and never an advertisement to its users' binders
    // (issues/class-default-operators.md owns that question).
    let e = bad("fn twice<A: Mon>(x: A) -> A { x ∙ x }");
    assert!(e.contains("`∙` has no meaning here"), "{e}");
}

// -- customer 2: the value parameter ---------------------------------------

/// The symbol's scope is the **binder's** scope: the rest of the telescope,
/// the result type, and the body. The result type is the load-bearing third —
/// a `theorem`'s statement *is* its result type, so this is what lets a
/// statement be written in the notation.
///
/// The fold is pinned by `refl` against the positional spelling at three
/// carriers, so the notation and the written form are one term rather than two
/// things that both check; a literal scrutinee computes, a neutral one cannot.
#[test]
fn a_value_parameter_spells_the_telescope_the_statement_and_the_body() {
    ok("
        // The symbol in a **result type** — the statement is the mathematics.
        theorem step<A: Mon(op)>(op as ∙: A -> A -> A, h: A, t: List<A>):
            fold(op, Cons(h, t)) = h ∙ fold(op, t)
        { refl }

        // The symbol in a later **telescope** entry's type.
        theorem later<A: Mon(op)>(op as ∙: A -> A -> A, x: A, p: x ∙ A.unit = x):
            op(x, A.unit) = x
        { p }

        // One term with the positional spelling, at three carriers.
        theorem f_nat(ns: List<Nat>): fold(add, ns) = fold(add, ns) { refl }
        theorem f_bool(bs: List<Bool>): fold(or, bs) = fold(or, bs) { refl }
        theorem f_open<B>(xss: List<List<B>>):
            fold(append, xss) = fold(append, xss) { refl }

        // A **literal** scrutinee, which has to compute all the way, and a
        // **neutral** one, which is stuck on its tail.
        theorem lit(): fold(add, Cons(2, Cons(3, Nil))) = 5 { refl }
        theorem neutral(n: Nat, ns: List<Nat>):
            fold(add, Cons(n, ns)) = add(n, fold(add, ns)) { refl }
    ");
}

/// The class-free case, which is what makes `as` a general device rather than
/// a class feature: a plain higher-order `fn` whose function parameter takes a
/// symbol, used in the **body** and in the **result type**, at an open element
/// type with no constraint anywhere.
#[test]
fn slow_acceptance_a_class_free_higher_order_function_takes_a_symbol() {
    ok("
        // The body.
        fn square<A>(f as ∙: A -> A -> A, x: A) -> A { x ∙ x }
        // The result type, and the body, in one declaration — and `A` is a
        // plain type parameter, so there is no class in sight.
        theorem square_is<A>(f as ∙: A -> A -> A, x: A): square(f, x) = x ∙ x { refl }
        // Spent at an unrelated carrier, with the operation passed positionally.
        theorem at_nat(x: Nat): square(add, x) = add(x, x) { refl }
        theorem at_list<B>(xs: List<B>): square(append, xs) = append(xs, xs) { refl }
        theorem at_lit(): square(add, 2) = 4 { refl }
    ");
    // The negative control beside it: the parameter is what the symbol means,
    // so a *different* operation is a different term.
    let e = bad("
        fn square<A>(f as ∙: A -> A -> A, x: A) -> A { x ∙ x }
        theorem nope(x: Nat): square(add, x) = mul(x, x) { refl }
    ");
    assert!(!e.is_empty(), "{e}");
}

// -- the reservation, and the refusals -------------------------------------

/// `∙` is the **reserved generic** operator: nothing designates it at any
/// carrier and it has no fallback name, so away from a binder that named it it
/// cannot mean anything — the property is enforced by *absence*, which is what
/// makes it the right spelling for bare monoid theory.
///
/// The refusal names the symbol as written, says there is no designation and
/// no fallback, and does not invent a name the writer never typed.
#[test]
fn the_reserved_generic_symbol_means_nothing_off_a_binder() {
    let e = bad("theorem t(x: Nat, y: Nat): x ∙ y = x { ?p }");
    assert!(e.contains("`∙` has no meaning here"), "{e}");
    assert!(e.contains("no `designation ∙ at …` covers this carrier"), "{e}");
    assert!(e.contains("`∙` has no fallback name"), "{e}");
    assert!(e.contains("designates nothing anywhere in this program"), "{e}");
    // Even at `Nat`, where `+` *is* designated: the two symbols are separate
    // names, and one's table says nothing about the other.
    ok("theorem u(x: Nat, y: Nat): x + y = add(x, y) { refl }");
}

/// Installation is scoped to the declaration, like the constraint slot's: the
/// next declaration has not heard of it. Stated positively (the fallback rung
/// still answers for `+` next door) and negatively.
#[test]
fn slow_acceptance_an_installed_symbol_does_not_leak_out_of_its_declaration() {
    ok("
        fn inside<A>(f as ∙: A -> A -> A, x: A) -> A { x ∙ x }
        theorem outside(x: Nat, y: Nat): x + y = add(x, y) { refl }
    ");
    let e = bad("
        fn inside<A>(f as ∙: A -> A -> A, x: A) -> A { x ∙ x }
        theorem outside(x: Nat, y: Nat): x ∙ y = add(x, y) { refl }
    ");
    assert!(e.contains("`∙` has no meaning here"), "{e}");
}

/// §5.2's uniqueness rule, as this issue amends it: one declaration installs
/// each spelling once, by **any mix** of constraint symbol slots and `as`.
///
/// Only the symbol namespace needed a new check — `as` mints no identifier, it
/// gives a second *role* to the one the binder already has — so the
/// identifier half is the parameter-list rules that were already there.
#[test]
fn a_declaration_installs_each_spelling_once() {
    // The acceptance case: `op as ∙` beside a `∙` symbol slot.
    let e = bad("fn f<A: Mon(∙)>(op as ∙: A -> A -> A, x: A) -> A { x ∙ x }");
    assert!(e.contains("already this declaration's body spelling"), "{e}");
    assert!(e.contains("a constraint that named it"), "{e}");
    assert!(e.contains("each spelling binds exactly one referent"), "{e}");

    // Two `as` binders at one symbol, which names the earlier binder.
    let e = bad("fn g<A>(f as ∙: A -> A -> A, h as ∙: A -> A -> A, x: A) -> A { x ∙ x }");
    assert!(e.contains("`f as ∙`"), "{e}");

    // And in a class head, where the head is the whole declaration.
    let e = bad("class Two<A>(f as ∙: A -> A -> A, g as ∙: A -> A -> A) { u: A }");
    assert!(e.contains("already a body spelling in this head"), "{e}");

    // The positive control beside them: two *different* symbols coexist, in
    // one declaration, by both routes at once.
    ok("fn h<A: Mon(+)>(g as ∙: A -> A -> A, x: A, y: A) -> A { (x + y) ∙ x }");

    // Sharing an annotation changes nothing here: the rule is per spelling,
    // not per group (issues/modifiers-in-shared-binder-runs.md). Two `as` in
    // ONE run at the same symbol is the same collision, named the same way…
    let e = bad("fn r<A>(f as ∙, h as ∙: A -> A -> A, x: A) -> A { x ∙ x }");
    assert!(e.contains("`f as ∙`"), "{e}");
    // …and two different symbols in one run are two installations, both live.
    ok("fn s<A>(f as ∙, h as +: A -> A -> A, x: A) -> A { (x + x) ∙ x }");
}

/// The run form reaches the elaborator as the spelled-out form it abbreviates:
/// a modifier attaches to the name it prefixes, so `f as ∙, h: T` installs
/// `∙` for `f` and leaves `h` an ordinary parameter of the same type
/// (issues/modifiers-in-shared-binder-runs.md). Stated where it matters — the
/// symbol is spelled in a **checking** position (a theorem's statement) at an
/// **open** carrier, with the negative control beside it.
#[test]
fn slow_acceptance_a_symbol_in_a_shared_run_reaches_only_its_own_name() {
    ok("theorem run<A>(f as ∙, h: A -> A -> A, x: A): x ∙ x = f(x, x) { refl }");
    // `h` is a parameter of the same type, referable by its identifier — the
    // run really did bind two names, not one.
    ok("theorem both<A>(f as ∙, h: A -> A -> A, x: A): h(x, x ∙ x) = h(x, f(x, x)) { refl }");
    // The negative control: the symbol did NOT reach `h`, and `∙` names `f`
    // wherever it is written, so nothing spells `h` as an operator.
    let e = bad("theorem no<A>(f as ∙, h: A -> A -> A, x: A): x ∙ x = h(x, x) { refl }");
    assert!(!e.contains("has no meaning here"), "`∙` is installed; it means `f`: {e}");
}

/// The growth invariant, from this feature's side: `as` adds a place to write
/// a symbol and no way to resolve one, so every declaration that writes none
/// is the program it was. The classes above are the library's own, restated —
/// `lib_algebra.rs` is the acceptance test that says the library agrees.
#[test]
fn slow_acceptance_a_declaration_that_writes_no_symbol_is_unchanged() {
    ok("
        fn plain<A: Mon(op)>(op: A -> A -> A, x: A) -> A { op(x, A.unit) }
        theorem plain_nat(x: Nat): plain(add, x) = add(x, 0) { refl }
        // The symbol slot's own device is untouched: it still binds under the
        // SYMBOL and refuses the declared name by name.
        fn sym<A: Mon(+)>(x: A, y: A) -> A { x + y }
        theorem sym_nat(x: Nat, y: Nat): sym(x, y) = add(x, y) { refl }
    ");
    let e = bad("fn f<A: Mon(+)>(x: A, y: A) -> A { op(x, y) }");
    assert!(e.contains("binds it under the SYMBOL"), "{e}");
}
