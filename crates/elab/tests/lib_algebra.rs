//! `lib/std/algebra.hthr` — the library's classes and instances, checked as a
//! module closure (`docs/traits-design.md` §13, `issues/traits.md`).
//!
//! This is the traits feature's first *library* corpus rather than a corpus
//! written for a test, so what it pins is the library's own claims: which
//! instance is registered at each carrier, that the scope beats the registry
//! where the library says it does, that the extends chain reaches one value
//! from every direction, and that the generic instance answers at an element
//! type nobody enumerated.
//!
//! Everything an instance produces is a *generated term*
//! (`docs/testing-generated-terms.md`), so the axes are varied deliberately:
//! an **open** element type (`concat<A>` and its use at a type parameter, not
//! only at `Nat`), a **neutral** receiver and scrutinee (parameters, not only
//! literals) beside the **computing** cases, a **checking** position (each
//! theorem's `refl` compares a resolved dictionary against a written one), and
//! a **negative control** beside each positive.
//!
//! The load-bearing tests, if only four are read: `the_library_checks`
//! (the whole closure, which is the acceptance), `any_of_uses_the_local_monoid`
//! (the library's coherence policy is observable — `all_of` and `any_of` are
//! the same fold at the same carrier and they disagree),
//! `the_extends_chain_reaches_one_value` (the diamond collapses in real
//! library code), and `a_second_instance_at_a_carrier_is_refused` (the policy
//! is enforced, not just documented).

use heather_elab::{ElabError, Elaborator};

const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");

/// The closure in dependency order — the order the CLI's loader would pick.
fn modules() -> Vec<(&'static str, &'static str)> {
    vec![
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("list", LIST),
        ("algebra", ALGEBRA),
    ]
}

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in modules() {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => format!("{name}: {msg}"),
                other => format!("{name}: {other}"),
            });
        }
    }
    if !extra.is_empty() {
        // The probe module imports the whole closure, exactly as a user file
        // would; `import` lines have to come first, so they are prepended here.
        let src = format!(
            "import bool;\nimport nat;\nimport option;\nimport list;\nimport algebra;\n{extra}"
        );
        if let Err(err) = e.elab_module_source("probe", &src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
    }
    Ok(e)
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
// 1. The closure itself.

#[test]
fn the_library_checks() {
    ok("");
}

// ---------------------------------------------------------------------------
// 2. Which instance is registered, and that it is the one the library's
//    header says it is. Each of these *computes*, which is the only thing that
//    distinguishes a resolved dictionary from some other resolved dictionary.

#[test]
fn the_registered_monoids_are_the_declared_ones() {
    ok("
theorem nat_is_addition(): sum(Cons(2, Cons(3, Nil))) = 5 { refl }
theorem bool_is_conjunction(): all_of(Cons(True, Cons(False, Nil))) = False { refl }
theorem empty_fold_is_the_unit(): sum(Nil) = 0 { refl }
theorem empty_bool_fold_is_True(): all_of(Nil) = True { refl }
// neutral, not literal: the fold on a parameter reduces one step and stops at
// the element, which is where a wrong `unit` would still be visible.
theorem neutral_singleton(n: Nat): sum(Cons(n, Nil)) = n { sum_single(n) }
");
}

/// The coherence policy is *observable*: `all_of` and `any_of` are the same
/// generic fold at the same carrier, and they compute differently, because one
/// of them binds the other monoid locally. Scope beats registry
/// (`docs/traits-layer2-design.md` §4) in real library code.
#[test]
fn any_of_uses_the_local_monoid() {
    ok("
theorem any_is_disjunction(): any_of(Cons(True, Cons(False, Nil))) = True { refl }
theorem empty_any_is_False(): any_of(Nil) = False { refl }
theorem the_two_folds_disagree(): all_of(Cons(True, Cons(False, Nil))) = False { refl }
");
}

/// The negative control for the pair above: `any_of` is *not* `all_of`. A
/// positive test alone cannot tell a local dictionary from the registry's,
/// since both are `Monoid<Bool>` and both type-check.
#[test]
fn the_local_monoid_is_not_the_registered_one() {
    let e = bad("theorem wrong(): any_of(Cons(True, Cons(False, Nil))) = False { refl }");
    assert!(e.contains("wrong"), "{e}");
}

// ---------------------------------------------------------------------------
// 3. The generic instance, at an element type nobody enumerated.

/// **Open** element type: the goal is `Monoid<List<A>>` with `A` the probe's
/// own type parameter, so it can only be answered by backchaining through
/// `instance<A> Monoid<List<A>>`.
#[test]
fn the_list_monoid_answers_at_an_open_element_type() {
    ok("
fn join<A>(xss: List<List<A>>) -> List<A> { concat(xss) }
// checking position, at the open type: the result is used where `List<A>` is
// expected and the dictionary is never named.
fn join_then_append<A>(xss: List<List<A>>, ys: List<A>) -> List<A> { append(join(xss), ys) }
");
}

/// …and it *computes* at a closed one, which is what says the resolved
/// dictionary's `op` is `append` and not something else of the same type.
#[test]
fn the_list_monoid_computes() {
    ok("
theorem flattens(): concat(Cons(Cons(1, Nil), Cons(Cons(2, Nil), Nil))) = Cons(1, Cons(2, Nil)) {
  refl
}
// neutral: two parameters, nothing reduces past the first `append`.
theorem neutral(xs: List<Nat>, ys: List<Nat>):
  concat(Cons(xs, Cons(ys, Nil))) = append(xs, append(ys, Nil)) { refl }
");
}

/// The derivation is minted once per goal and reused — memoization *is*
/// canonicalization (`docs/traits-layer2-design.md` §7.1). Two use sites of
/// `mconcat` at a list carrier share one derived value.
#[test]
fn a_derived_list_monoid_is_shared_between_use_sites() {
    let e = ok("
fn f(xss: List<List<Nat>>) -> List<Nat> { mconcat(xss) }
fn g(xss: List<List<Nat>>) -> List<Nat> { mconcat(xss) }
theorem same(xss: List<List<Nat>>): f(xss) = g(xss) { refl }
");
    assert_eq!(e.derived_instances().len(), 1, "{:?}", e.derived_instances());
}

/// The negative control for the table, and a fact about the library worth
/// knowing: calling `concat` derives **nothing**. Its resolution happened once,
/// inside `concat`'s own body, at an open carrier — which is not a closed goal
/// and so is never minted. A caller only instantiates the type argument.
#[test]
fn calling_concat_derives_nothing() {
    let e = ok("
fn f(xss: List<List<Nat>>) -> List<Nat> { concat(xss) }
fn g(xss: List<List<Bool>>) -> List<Bool> { concat(xss) }
");
    assert!(e.derived_instances().is_empty(), "{:?}", e.derived_instances());
}

// ---------------------------------------------------------------------------
// 4. `extends`: the canonical value and the chain.

/// `Nat` declares the chain parent-first, so `AddMonoid<Nat>` fills `plus`
/// from `AddSemigroup<Nat>` by reference; `Bool` declares only the child, so
/// its two ancestors are synthesized. Both directions end at one value per
/// (class, carrier), and `refl` is the proof of that.
#[test]
fn the_extends_chain_reaches_one_value() {
    ok("
theorem nat_up(): Nat::AddCommMonoid.plus = Nat::AddSemigroup.plus { refl }
theorem nat_mid(): Nat::AddMonoid.plus = Nat::AddSemigroup.plus { refl }
theorem nat_zero(): Nat::AddCommMonoid.zero = Nat::AddMonoid.zero { refl }
theorem bool_synthesized(): Bool::AddCommMonoid.plus = Bool::AddSemigroup.plus { refl }
theorem bool_mid(): Bool::AddMonoid.zero = Bool::AddCommMonoid.zero { refl }
");
}

/// The library's other coherence claim: `Monoid<Nat>`'s `op` and the additive
/// hierarchy's `plus` are deliberately the *same function*, so the two
/// readings of a `Nat` fold agree definitionally rather than by a lemma.
#[test]
fn the_two_nat_structures_share_their_operation() {
    ok("theorem shared(): Nat::Monoid.op = Nat::AddSemigroup.plus { refl }");
}

/// The negative control for the whole `extends` story: `Bool`'s addition is
/// disjunction, so its `zero` is `False` and not the conjunction monoid's unit.
/// Without this, a synthesized parent that silently took the wrong components
/// would pass every test above.
#[test]
fn the_bool_hierarchy_is_disjunction_not_conjunction() {
    ok("theorem bool_zero_is_False(): Bool::AddMonoid.zero = False { refl }");
    let e = bad("theorem bool_zero_is_True(): Bool::AddMonoid.zero = True { refl }");
    assert!(e.contains("bool_zero_is_True"), "{e}");
}

// ---------------------------------------------------------------------------
// 5. The class lemmas, and the consumers that never name a dictionary.

/// One statement, two carriers, no re-proof — and in *checking* position: the
/// class lemma's instantiated type has to converge with each goal.
#[test]
fn one_class_lemma_serves_two_carriers() {
    ok("
theorem at_nat(n: Nat): sum(Cons(n, Nil)) = n { mconcat_single(n) }
theorem at_bool(b: Bool): all_of(Cons(b, Nil)) = b { mconcat_single(b) }
theorem hierarchy_at_nat(x: Nat): Nat::AddCommMonoid.plus(x, 0) = x { plus_zero_of_comm(x) }
theorem hierarchy_at_bool(x: Bool): Bool::AddCommMonoid.plus(x, False) = x {
  plus_zero_of_comm(x)
}
");
}

/// Receiver dispatch in library code: `max_of` is written `x.le(y)` and the
/// dictionary comes from its own `requires` binder. At a concrete carrier the
/// registry answers instead, and the result computes.
#[test]
fn the_order_class_dispatches_and_computes() {
    ok("
theorem picks_the_larger(): max_of(2, 5) = 5 { refl }
theorem picks_the_larger_the_other_way(): max_of(5, 2) = 5 { refl }
theorem on_bools(): max_of(False, True) = True { refl }
// neutral receiver, through the class lemma rather than by computation.
theorem idempotent(n: Nat): max_of(n, n) = n { max_of_self(n) }
");
}

/// `:= infer` on an ordinary (non-`requires`) binder: the caller of
/// `or_default` names neither the dictionary nor the fallback.
#[test]
fn or_default_infers_its_dictionary() {
    ok("
fn no_nat() -> Option<Nat> { None }
fn no_list() -> Option<List<Nat>> { None }
theorem nat_default(): or_default(no_nat()) = 0 { refl }
theorem list_default(): or_default(no_list()) = Nil { refl }
theorem some_wins(n: Nat): or_default(Some(n)) = n { refl }
// open element type: the dictionary is resolved at the probe's own parameter.
fn head_or_default<A> requires d: Default<A> (o: Option<A>) -> A { or_default(o) }
");
}

// ---------------------------------------------------------------------------
// 6. The policy, enforced.

/// One instance per (class, carrier): the library's `Monoid<Bool>` is
/// conjunction and a second registration is refused rather than shadowed.
#[test]
fn a_second_instance_at_a_carrier_is_refused() {
    let e = bad(
        "instance Monoid<Bool> {
  unit := False,
  op := or,
  assoc := or_assoc,
  unit_l := or_false_l,
  unit_r := or_false_r,
}",
    );
    assert!(e.contains("already has an instance"), "{e}");
}

/// A carrier with no instance is a resolution failure with a trace, not a
/// silent wrong answer.
#[test]
fn a_carrier_with_no_monoid_is_a_reported_failure() {
    let e = bad(
        "inductive Colour { Red, Green }
fn fold_colours(cs: List<Colour>) -> Colour { mconcat(cs) }",
    );
    assert!(e.contains("Monoid"), "the goal must be named: {e}");
}

/// The naming constraint the library discovered: a class field that shares its
/// spelling with a global in scope can never be reached by a receiver. `Cmp`'s
/// field is `le` for exactly this reason — `leb` would have collided with
/// `std/nat`'s function, and the elaborator names both readings rather than
/// choosing. Pinned so the rename is not undone by accident.
#[test]
fn a_member_name_that_shadows_a_global_is_ambiguous_at_a_receiver() {
    let e = bad(
        "class Cmp2<A> { leb: A -> A -> Bool }
instance Cmp2<Nat> { leb := leb }
fn f(a: Nat, b: Nat) -> Bool { a.leb(b) }",
    );
    assert!(e.contains("write one of them"), "{e}");
}

/// The finding this corpus exists to have produced: an **inherited** field is
/// undispatchable at every carrier, forever. `plus` is a field of all three
/// classes in the chain (flattening), and a child instance *synthesizes* its
/// parents, so every one of them has an instance at `Nat` and the receiver
/// rules — rightly — refuse to choose. It is not a `Nat` accident: it holds for
/// any `extends` hierarchy and any inherited member.
///
/// Pinned as the recorded limitation it is (`issues/traits.md`, 2026-08-07):
/// if the resolution rules ever learn to prefer the most-derived class, this
/// test fails and says so.
#[test]
fn an_inherited_member_cannot_be_reached_by_a_receiver() {
    let e = bad("fn f(a: Nat, b: Nat) -> Nat { a.plus(b) }");
    assert!(e.contains("AddCommMonoid<Nat>") && e.contains("AddSemigroup<Nat>"), "{e}");
    // …and the explicit spelling, which is what library code writes instead.
    ok("fn f(a: Nat, b: Nat) -> Nat { Nat::AddCommMonoid.plus(a, b) }");
}

/// The other half of the naming story, and the reason `Monoid` is declared
/// flat rather than as `Monoid<A> extends Semigroup<A>`: a member of exactly
/// one class dispatches, generically and concretely.
#[test]
fn a_member_of_one_class_dispatches() {
    ok("
theorem concrete(a: Nat, b: Nat): a.op(b) = add(a, b) { refl }
theorem on_bool(a: Bool, b: Bool): a.op(b) = and(a, b) { refl }
fn generic<A> requires m: Monoid<A> (x: A, y: A) -> A { x.op(y) }
theorem generic_agrees(a: Nat, b: Nat): generic(a, b) = add(a, b) { refl }
");
}
