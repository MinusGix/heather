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
//! (the whole closure, which is the acceptance),
//! `both_bool_monoids_are_registered` (two structures at one carrier, as
//! equals — the sentence the additive hierarchy existed to fail to say),
//! `one_law_three_structures` (`op_unit_of_comm` proved once and spent at
//! `add`, `and` and `or`, each pinning its index by unification alone), and
//! `a_second_instance_at_one_index_is_refused` (the key is the class, the
//! carrier head *and* the index).

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");

/// The closure in dependency order — the order the CLI's loader would pick.
fn modules() -> Vec<(&'static str, &'static str)> {
    vec![
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION), ("pair", PAIR),
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

/// Two structures on one carrier, **both registered**, as equals
/// (`docs/operation-indexed-classes-design.md` §3). `all_of` and `any_of` are
/// one generic fold at one carrier under two operations, and they compute
/// differently because the operation is part of the goal's *type* — no local
/// binding, no shadowing, and nothing anywhere nominates one of them.
#[test]
fn both_bool_monoids_are_registered() {
    ok("
theorem any_is_disjunction(): any_of(Cons(True, Cons(False, Nil))) = True { refl }
theorem empty_any_is_False(): any_of(Nil) = False { refl }
theorem the_two_folds_disagree(): all_of(Cons(True, Cons(False, Nil))) = False { refl }
// each ground goal finds its own, by the index and nothing else.
theorem and_unit(): Bool::Monoid(and).unit = True { refl }
theorem or_unit(): Bool::Monoid(or).unit = False { refl }
");
}

/// The negative control for the pair above: `any_of` is *not* `all_of`. A
/// positive test alone cannot tell one Bool monoid from the other, since both
/// are registered and both type-check.
#[test]
fn the_two_bool_monoids_are_not_interchangeable() {
    let e = bad("theorem wrong(): any_of(Cons(True, Cons(False, Nil))) = False { refl }");
    assert!(e.contains("wrong"), "{e}");
    let e = bad("theorem wrong2(): Bool::Monoid(or).unit = True { refl }");
    assert!(e.contains("wrong2"), "{e}");
}

/// The library's Boolean spelling is `&&`/`||`, not the semiring's `+`/`*`
/// (issues/bool-operator-designations.md): the doubled symbols resolve by the
/// library's designations, and `sum_all` at `Bool` — a `+`-fold — refuses,
/// because `+` means nothing there any more. The refusal is the review's
/// content, so it is pinned beside the spelling that replaced it.
#[test]
fn the_bool_spelling_is_the_doubled_symbols_not_the_semiring() {
    ok("
theorem and_notated(x: Bool, y: Bool): x && y = and(x, y) { refl }
theorem or_notated(x: Bool, y: Bool): x || y = or(x, y) { refl }
// The library's own corollaries are stated in this notation
// (`bool_and_true`/`bool_or_false`); their content is unchanged.
theorem consumed(x: Bool): or(x, False) = x { bool_or_false(x) }
");
    let e = bad("fn any2(bs: List<Bool>) -> Bool { sum_all(bs) }");
    assert!(!e.is_empty(), "{e}");
    let e = bad("theorem semiring(x: Bool, y: Bool): x + y = or(x, y) { refl }");
    assert!(!e.is_empty(), "{e}");
}

// ---------------------------------------------------------------------------
// 3. The generic instance, at an element type nobody enumerated.

/// **Open** element type: the goal is `Monoid<List<A>>(append)` with `A` the
/// probe's own type parameter, so it can only be answered by backchaining
/// through `instance<A> Monoid<List<A>>(append)` — with the index instantiated
/// at the same time as the carrier.
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

#[test]
fn a_generic_class_lemma_instantiates_at_a_wf_carrier() {
    ok("
theorem neutral_concat_single<A>(xs: List<A>): concat(Cons(xs, Nil)) = xs {
    concat_single(xs)
}
");
}

/// The library spelling for list concatenation is `++`, not arithmetic `+`
/// (issues/list-append-symbol.md). The generic designation must work at an
/// open element type, and the literal control must compute.
#[test]
fn the_list_spelling_is_append_not_add() {
    ok("
theorem neutral<A>(xs: List<A>, ys: List<A>): xs ++ ys = append(xs, ys) { refl }
theorem literal(): Cons(1, Nil) ++ Cons(2, Nil) = Cons(1, Cons(2, Nil)) { refl }
theorem concat_is_positional<A>(xss: List<List<A>>):
  concat(xss) = mconcat(append, xss) { refl }
");

    let e = bad("theorem old<A>(xs: List<A>, ys: List<A>): xs + ys = append(xs, ys) { refl }");
    assert!(e.contains("`+` has no designation at `List`"), "{e}");
    assert!(e.contains("fallback name `add`"), "{e}");
}

/// The canonical derived table (`docs/traits-layer2-design.md` §7.1) does
/// **not** fire for a goal with a value index, and this pins the fact rather
/// than hiding it: the index is a *term* in the goal type, and a term
/// elaborated at a use site carries that site's identity substitution, so the
/// table's closedness test — asked in the empty context, which is where a
/// minted global has to live — says no. Two use sites therefore each inline
/// their own derivation. Sharing, never correctness, which is the table's
/// standing bargain; recorded as a residue by the round that found it.
#[test]
fn a_derived_list_monoid_is_not_shared_between_use_sites() {
    let e = ok("
fn f(xss: List<List<Nat>>) -> List<Nat> { mconcat(append, xss) }
fn g(xss: List<List<Nat>>) -> List<Nat> { mconcat(append, xss) }
theorem same(xss: List<List<Nat>>): f(xss) = g(xss) { refl }
");
    assert!(e.derived_instances().is_empty(), "{:?}", e.derived_instances());
    // …and the unindexed classes still canonicalize, unchanged: `Default` has
    // a generic instance at `List<A>` and one goal mints one global.
    let e = ok("
fn p(o: Option<List<Nat>>) -> List<Nat> { or_default(o) }
fn q(o: Option<List<Nat>>) -> List<Nat> { or_default(o) }
theorem same2(o: Option<List<Nat>>): p(o) = q(o) { refl }
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

/// Every carrier declares its chain CHILD-first now — one `CommMonoid`
/// declaration, two ancestors synthesized as its own projections — and the
/// index rides along: the synthesized `Monoid<Bool>(or)` is keyed at `or` and
/// the synthesized `Monoid<Bool>(and)` at `and`, so one carrier carries two
/// whole chains that never meet.
#[test]
fn the_extends_chain_reaches_one_value() {
    ok("
theorem nat_up(): Nat::CommMonoid(add).unit = Nat::Monoid(add).unit { refl }
theorem bool_and_up(): Bool::CommMonoid(and).unit = Bool::Monoid(and).unit { refl }
theorem bool_or_up(): Bool::CommMonoid(or).unit = Bool::Monoid(or).unit { refl }
");
}

/// The negative control for the whole `extends` story: the two Bool chains do
/// not leak into each other. Without this, a synthesized parent that silently
/// took the wrong components would pass every test above.
#[test]
fn the_two_bool_chains_do_not_meet() {
    ok("theorem or_zero_is_False(): Bool::Monoid(or).unit = False { refl }");
    let e = bad("theorem or_zero_is_True(): Bool::Monoid(or).unit = True { refl }");
    assert!(e.contains("or_zero_is_True"), "{e}");
}

/// **The headline** (`docs/operation-indexed-classes-design.md` §13 item 1):
/// one generic law, proved once against `CommMonoid`, spent at three
/// structures — two of them on one carrier. Each corollary's goal *names* its
/// operation, so the index is pinned by unification alone (§4.2's equal-arity
/// flex-rigid rule) and the ground goal hits the registry key.
#[test]
fn one_law_three_structures() {
    ok("
theorem at_add(x: Nat): add(x, 0) = x { op_unit_of_comm(x) }
theorem at_and(x: Bool): and(x, True) = x { op_unit_of_comm(x) }
theorem at_or(x: Bool): or(x, False) = x { op_unit_of_comm(x) }
");
    // …and the negative control: the law is about the registered unit, so a
    // wrong one is refused rather than derived.
    let e = bad("theorem nope(x: Bool): or(x, True) = x { op_unit_of_comm(x) }");
    assert!(e.contains("nope"), "{e}");
}

// ---------------------------------------------------------------------------
// 5. The class lemmas, and the consumers that never name a dictionary.

/// One statement, two carriers, no re-proof — and in *checking* position: the
/// class lemma's instantiated type has to converge with each goal.
#[test]
fn one_class_lemma_serves_two_carriers() {
    ok("
theorem at_nat(n: Nat): sum(Cons(n, Nil)) = n { mconcat_single(add, n) }
theorem at_bool(b: Bool): all_of(Cons(b, Nil)) = b { mconcat_single(and, b) }
theorem at_bool_again(b: Bool): any_of(Cons(b, Nil)) = b { mconcat_single(or, b) }
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
fn head_or_default<A: Default>(o: Option<A>) -> A { or_default(o) }
");
}

// ---------------------------------------------------------------------------
// 6. The policy, enforced.

/// One instance per (class, carrier head, **index**): a second `Monoid<Bool>`
/// at an index already registered is refused, and the message names the index
/// that collided (`docs/operation-indexed-classes-design.md` §3.1, §11).
#[test]
fn a_second_instance_at_one_index_is_refused() {
    let e = bad(
        "instance Monoid<Bool>(or) {
  unit := False,
  assoc := or_assoc,
  unit_l := or_false_l,
  unit_r := or_false_r,
}",
    );
    assert!(e.contains("already has an instance"), "{e}");
    assert!(e.contains("index"), "the index is part of the key: {e}");
}

/// …and the positive control beside it: a *third* structure at one carrier is
/// an ordinary declaration, because the key distinguishes it.
#[test]
fn a_third_structure_at_one_carrier_registers() {
    ok("
fn andnot(a: Bool, b: Bool) -> Bool { and(a, not(b)) }
class Mag<A>(op: A -> A -> A) { pt: A, fixes: op(pt, pt) = pt }
instance Mag<Bool>(andnot) { pt := False, fixes := refl }
instance Mag<Bool>(and) { pt := True, fixes := refl }
instance Mag<Bool>(or) { pt := False, fixes := refl }
");
}

/// An instance head whose index is not spellable is refused **at the
/// declaration**, with the scope alternative stated (§3.1).
#[test]
fn an_unspellable_instance_head_is_refused() {
    let e = bad(
        "instance Monoid<Bool>(λ (a: Bool) (b: Bool) => a) {
  unit := True,
  assoc := and_assoc,
  unit_l := and_true_l,
  unit_r := and_true_r,
}",
    );
    assert!(e.contains("spellable"), "{e}");
}

/// A carrier with no instance is a resolution failure with a trace, not a
/// silent wrong answer.
#[test]
fn a_carrier_with_no_monoid_is_a_reported_failure() {
    let e = bad(
        "inductive Colour { Red, Green }
fn first(a: Colour, b: Colour) -> Colour { a }
fn fold_colours(cs: List<Colour>) -> Colour { mconcat(first, cs) }",
    );
    assert!(e.contains("Monoid"), "the goal must be named: {e}");
}

/// The naming constraint the library discovered: a class field that shares its
/// spelling with a global in scope can never be reached by a receiver. `Cmp`'s
/// field is `le` for exactly this reason — `leb` would have collided with
/// `std/nat`'s function, and the elaborator names both readings rather than
/// choosing. Pinned so the rename is not undone by accident.
///
/// The shadowed global is `sub` and not `leb` as of 2026-08-17: `std/bool`
/// dropped its `_bool` suffixes (`docs/instance-resolved-key-design.md` §6), so
/// two modules declare `leb` and a bare one resolves to *neither*. That is a
/// different refusal — ambiguity at the value, not at the receiver — and it
/// would have made this test pass for the wrong reason, so the fixture moved to
/// a global only `std/nat` declares.
#[test]
fn a_member_name_that_shadows_a_global_is_ambiguous_at_a_receiver() {
    let e = bad(
        "class Cmp2<A> { sub: A -> A -> A }
instance Cmp2<Nat> { sub := sub }
fn f(a: Nat, b: Nat) -> Nat { a.sub(b) }",
    );
    assert!(e.contains("write one of them"), "{e}");
}

/// Owner-keyed dispatch (`docs/traits-owner-dispatch-design.md` §2) builds the
/// goal at the class that *declares* the member, and at an indexed class the
/// index comes from the binder in scope: `x.assoc(y, z)` inside a `Monoid`
/// binder is a `Semigroup` goal at that binder's own operation, answered by
/// upcast. The two that merely inherit `assoc` are not candidates at all.
#[test]
fn an_inherited_member_is_reached_at_its_owner() {
    ok("
theorem assoc_from_a_monoid<A: Monoid(o)>(o: A -> A -> A, x: A, y: A, z: A):
  o(o(x, y), z) = o(x, o(y, z)) { x.assoc(y, z) }
// two hops: `CommMonoid` inherits `assoc` from `Semigroup` through `Monoid`.
theorem assoc_from_a_comm_monoid<A: CommMonoid(o)>(o: A -> A -> A, x: A, y: A, z: A):
  o(o(x, y), z) = o(x, o(y, z)) { x.assoc(y, z) }
");
}

/// The negative control the index adds: at a **concrete** carrier a receiver
/// fixes the carrier and nothing fixes the operation, so the dispatch is
/// refused by name with both Bool monoids listed
/// (`docs/operation-indexed-classes-design.md` §5.1). Scope, then refuse — and
/// here there is no scope.
#[test]
fn dispatch_at_a_concrete_carrier_is_refused_by_name() {
    let e = bad("theorem nope(a: Bool, b: Bool, c: Bool): and(and(a, b), c) = and(a, and(b, c)) {
  a.assoc(b, c)
}");
    assert!(e.contains("not pinned"), "{e}");
    assert!(e.contains("Semigroup<Bool>(and)") && e.contains("Semigroup<Bool>(or)"), "{e}");
    // …and the spelling that works instead, which is what the refusal names.
    ok("theorem yes(a: Bool, b: Bool, c: Bool): and(and(a, b), c) = and(a, and(b, c)) {
  Bool::Semigroup(and).assoc(a, b, c)
}");
}

/// The **open** carrier, which is what the upcast exists for: the dictionary in
/// scope is `AddCommMonoid<G>` and the dispatched goal is `AddSemigroup<G>`,
/// two records that no conversion relates. Nothing here is concrete, so no
/// registry entry and no synthesized parent global can be the one answering.
#[test]
fn dispatch_upcasts_from_a_child_dictionary_at_an_open_carrier() {
    ok("
theorem unit_r_from_a_comm_monoid<G> requires m: CommMonoid<G>(o) (o: G -> G -> G, x: G):
  o(x, m.unit) = x { x.unit_r() }
// checking position at the open carrier: the dispatched projection is the
// proof a stated equation wants, and the dictionary is never named.
theorem two_hops<G> requires m: CommMonoid<G>(o) (o: G -> G -> G, x: G, y: G, z: G):
  o(o(x, y), z) = o(x, o(y, z)) { x.assoc(y, z) }
");
}

/// The upcast as a *resolution* rule rather than a dispatch one, which is the
/// half the issue said would bite the first deep library proof: a lemma stated
/// at `AddMonoid<G>` is discharged from an `AddCommMonoid<G>` binder, at an
/// open `G`, with the dictionary never written at the use site.
#[test]
fn a_parent_lemma_resolves_from_a_child_binder_at_an_open_carrier() {
    ok("
theorem left_unit<G> requires m: Monoid<G>(o) (o: G -> G -> G, x: G): o(m.unit, x) = x {
  m.unit_l(x)
}
// `use_it` has only the child; the goal `Monoid<G>(o)` is answered by upcast,
// and the index travels with it.
theorem use_it<G> requires m: CommMonoid<G>(o) (o: G -> G -> G, x: G):
  o(m.unit, x) = x { left_unit(o, x) }
// two steps up the chain, and the grandparent is one hop (`ancestors` is
// transitive), still at an open carrier.
fn assoc_of<G> requires m: Semigroup<G>(o) (o: G -> G -> G, x: G) -> G { o(x, o(x, x)) }
fn use_grandparent<G> requires m: CommMonoid<G>(o) (o: G -> G -> G, x: G) -> G {
  assoc_of(o, x)
}
");
}

/// A dispatched projection reads **through** the upcast
/// (`docs/traits-named-upcast-design.md`), so the anonymous spelling and the
/// named-dictionary one are not merely equal — they are one term.
/// `plus_zero_of_comm` is the library's own case: `plus` is declared by
/// `AddSemigroup` and `zero` by `AddMonoid`, so both projections in its
/// statement go through an ancestor.
///
/// This is the pin that retired
/// `issues/upcast-assembly-cost-at-open-carriers.md`: the same file checked in
/// 35.9 s before it and 0.94 s after, because the two spellings stopped being
/// two terms.
#[test]
fn a_projection_through_an_upcast_is_the_childs_own_field() {
    ok("
fn anon<G: CommMonoid(o)>(o: G -> G -> G, x: G) -> G { o(x, G.unit) }
theorem anon_is_the_dictionary<G> requires a: CommMonoid<G>(o) (o: G -> G -> G, x: G):
  anon(o, x) = o(x, a.unit) { refl }
// two hops up the chain, at an open carrier, in one expression.
fn deep<G: CommMonoid(o)>(o: G -> G -> G, x: G) -> G { o(o(x, G.unit), x) }
theorem deep_is_the_dictionary<G> requires a: CommMonoid<G>(o) (o: G -> G -> G, x: G):
  deep(o, x) = o(o(x, a.unit), x) { refl }
// and it still computes at the concrete carriers the generic proof never
// mentioned — the library's own `nat_add_zero`/`bool_or_false` consume it.
theorem at_nat(a: Nat): anon(add, a) = add(a, 0) { refl }
theorem at_bool(a: Bool): anon(or, a) = or(a, False) { refl }
");
}

/// An **override** with an agreement certificate, dispatched through an upcast.
/// Reading through takes the CHILD's field, which for an overriding instance is
/// the override; layer 1 §4.5's certificate is what makes that
/// indistinguishable from the ancestor's value. This pins both halves — that
/// the dispatch lands on the child's field, and that the certificate holds — so
/// the rewrite is seen to agree with owner-dispatch §2.2 rather than to lean on
/// it.
#[test]
fn an_override_still_upcasts_to_its_own_field() {
    ok("
class Sg<A> { sop: A -> A -> A }
class Mn<A> extends Sg<A> { munit: A }
instance Sg<Nat> { sop := add }
// the child re-states the inherited field: an override, which owes `refl`
// against the registered `Nat::Sg.sop` and gets it.
instance Mn<Nat> { munit := 0, sop := add }
// open carrier, dispatched at the OWNER `Sg` and answered by upcast from `Mn`.
fn twice_over<G> requires m: Mn<G> (x: G) -> G { x.sop(x) }
theorem twice_over_is_the_child<G> requires m: Mn<G> (x: G):
  twice_over(x) = m.sop(x, x) { refl }
// …and the child's field is the ancestor's, which is what the certificate says.
theorem the_override_agrees(a: Nat, b: Nat):
  Nat::Mn.sop(a, b) = Nat::Sg.sop(a, b) { refl }
theorem at_nat(a: Nat, b: Nat): twice_over(a) = add(a, a) { refl }
");
}

/// The negative control for the upcast: it fires between a class and its
/// ancestors and nowhere else. `Cmp<A>` and `AddMonoid<A>` are unrelated, so a
/// `Cmp` binder answers no `AddMonoid` goal — the goal reports its search
/// rather than quietly building a record out of the wrong dictionary. The
/// statement mentions no dictionary, so resolution is the *only* thing that
/// can fail here.
#[test]
fn upcast_does_not_fire_between_unrelated_classes() {
    let e = bad(
        "fn dbl<G> requires m: Monoid<G>(o) (o: G -> G -> G, x: G) -> G { o(m.unit, x) }
fn nope<G> requires c: Cmp<G> (o: G -> G -> G, x: G) -> G { dbl(o, x) }",
    );
    assert!(e.contains("no instance for `Monoid<G>(o)`"), "{e}");
    // …and the positive control beside it: the same call with an ancestor-
    // related binder resolves.
    ok("fn dbl2<G> requires m: Monoid<G>(o) (o: G -> G -> G, x: G) -> G { o(m.unit, x) }
fn yes<G> requires m: CommMonoid<G>(o) (o: G -> G -> G, x: G) -> G { dbl2(o, x) }");
}

/// Owner-keying is not a tiebreak, and this is the case that says so: two
/// **unrelated** classes each *declaring* `plus` at one carrier are two owners,
/// and the receiver still refuses to choose, naming both
/// (`docs/traits-receiver-dispatch-design.md` §4 rule 3, unchanged).
#[test]
fn two_unrelated_owners_of_one_name_are_still_ambiguous() {
    let e = bad(
        "class Ordish<A> { le: A -> A -> Bool }
instance Ordish<Nat> { le := nat::leb }
fn f(a: Nat, b: Nat) -> Bool { a.le(b) }",
    );
    assert!(e.contains("Cmp<Nat>") && e.contains("Ordish<Nat>"), "{e}");
}

/// A member of exactly one class dispatches, generically and concretely — and
/// `Monoid` is now the hierarchy it always wanted to be, with `op` declared by
/// `Semigroup` and reached through the child dictionary by upcast.
#[test]
fn a_member_of_one_class_dispatches() {
    ok("
// generic, at the linked index: the operation is a variable and the member is
// reached through the binder.
fn generic<A: Monoid(o)>(o: A -> A -> A, x: A, y: A) -> A { o(x, y) }
theorem generic_agrees(a: Nat, b: Nat): generic(add, a, b) = add(a, b) { refl }
// the whole chain is synthesized from one `CommMonoid` declaration and every
// class in it is keyed at the same index.
theorem one_unit(): Nat::Monoid(add).unit = Nat::CommMonoid(add).unit { refl }
");
}

/// The library's own type projections (`docs/traits-type-projection-design.md`),
/// pinned where the file uses them: at an **open** carrier inside `mconcat`
/// and `mconcat_single`, and at a **concrete** one in the hierarchy lemmas.
/// The load-bearing claim is that `Nat.zero` is the very term
/// `Nat::AddMonoid.zero` is, so the migration moved a spelling and not a value.
#[test]
fn the_library_projects_from_its_types() {
    ok("
// open, which is where `A.unit` lives in the library: the binder in scope
// pins the index and the projection is an ordinary field read.
theorem the_empty_fold_is_the_projected_unit<A: Monoid(o)>(o: A -> A -> A):
  mconcat(o, Nil) = A.unit { refl }
// concrete, through the index-bearing spelling `T::C(args)` — an indexed
// class has no shorter one at a carrier with two structures.
theorem the_unit_is_the_same_value(): Nat::Monoid(add).unit = 0 { refl }
theorem the_bool_unit_too(): Bool::Monoid(and).unit = True { refl }
// …and it computes: the empty fold at a carrier is that carrier's unit.
theorem the_empty_nat_fold(): sum(Nil) = Nat::Monoid(add).unit { refl }
");
}

/// The negative control for the above: a type parameter with no constraint
/// providing the field reports the *value slot*, with every registered
/// instance listed — the diagnosis a reader needs in order to know which
/// structure was wanted (`docs/operation-indexed-classes-design.md` §11).
#[test]
fn an_unconstrained_type_parameter_reports_the_search() {
    let e = bad("fn nope<A>() -> A { A.unit }");
    assert!(e.contains("not pinned"), "{e}");
    assert!(e.contains("Monoid<Nat>(add)") && e.contains("Monoid<Bool>(or)"), "{e}");
    // …and the unindexed classes still report the *search*, unchanged.
    let e = bad("fn nope2<A>() -> A { A.default }");
    assert!(e.contains("Default<A>"), "{e}");
    assert!(e.contains("binder(s) consulted"), "{e}");
}
