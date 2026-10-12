//! Traits, layer 2: the instance resolver and `:= infer`
//! (`docs/traits-layer2-design.md`, `issues/traits.md`).
//!
//! Everything resolution produces is a *generated term*
//! (`docs/testing-generated-terms.md`), so the four axes are varied
//! deliberately throughout: an **open** carrier (a class reached through a
//! `fn`'s own type parameter, and a generic instance whose carrier is built
//! from two of them), a **checking** position (every resolution runs against
//! an expected type, and the derived value is used where the class type is
//! wanted), a **neutral** scrutinee (dictionaries reached through parameters
//! and through computed calls, not only through literals), and a **negative
//! control** beside each positive.
//!
//! The load-bearing tests, if only four are read:
//! `a_derived_instance_is_minted_once_and_reused` (memoization *is*
//! canonicalization — the coherence invariant, not a cache),
//! `a_local_dictionary_shadows_the_registry` (ascending scopes, which is what
//! makes a scoped override possible at all), `a_self_feeding_instance_is_refused`
//! (termination is a declaration-time property) and
//! `an_unresolvable_goal_reports_its_search` (the trace is the diagnostic).

use heather_elab::Elaborator;

fn ok(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
    e
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(src),
    }
}

/// The record's own example (§6): a class, a declared instance at a concrete
/// carrier, and a conditional instance over a two-parameter carrier.
const MONOID: &str = r#"
class Mag<A> { op: A -> A -> A }
record Pair<A, B> { fst: A, snd: B }
inductive Z { Z0, Z1 }

instance Mag<Z> { fn op(x: Z, y: Z) -> Z { y } }

instance<A, B> Mag<Pair<A, B>> requires ma: Mag<A>, mb: Mag<B> {
  fn op(x: Pair<A, B>, y: Pair<A, B>) -> Pair<A, B> {
    Pair { fst: ma.op(x.fst, y.fst), snd: mb.op(x.snd, y.snd) }
  }
}
"#;

// -- 1: the resolver core --------------------------------------------------

#[test]
fn a_requires_argument_is_resolved_rather_than_passed() {
    // The headline: `combine` is dictionary-valued in an **open** carrier, and
    // the call site names neither dictionary.
    ok(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
fn use1(p: Pair<Z, Z>, q: Pair<Z, Z>) -> Pair<Z, Z> {{ combine(p, q) }}
"
    ));
}

#[test]
fn resolution_computes_at_a_concrete_carrier() {
    // Neutral is not enough: the resolved dictionary has to *be* the right
    // one, which only computation says. `Mag<Pair<Z, Z>>`'s `op` takes the
    // second argument in each component, so this is the value or the
    // resolution picked something else.
    ok(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
theorem computes():
  combine(Pair {{ fst: Z0, snd: Z1 }}, Pair {{ fst: Z1, snd: Z0 }}).fst = Z1 {{ refl }}
"
    ));
}

#[test]
fn a_derived_instance_is_minted_once_and_reused() {
    // Memoization is canonicalization (record §6.1): two use sites of
    // `Mag<Pair<Z, Z>>` derive **one** value, and the second reaches it by
    // reference. What is observable from outside is the count — and that the
    // two use sites are definitionally the same value, which is the invariant
    // the count exists for.
    let e = ok(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
fn use1(p: Pair<Z, Z>, q: Pair<Z, Z>) -> Pair<Z, Z> {{ combine(p, q) }}
fn use2(p: Pair<Z, Z>, q: Pair<Z, Z>) -> Pair<Z, Z> {{ combine(p, q) }}
theorem same(p: Pair<Z, Z>, q: Pair<Z, Z>): use1(p, q) = use2(p, q) {{ refl }}
"
    ));
    let derived = e.derived_instances();
    assert_eq!(derived.len(), 1, "expected one canonical derivation, got {derived:?}");
}

#[test]
fn nothing_is_minted_when_nothing_is_derived() {
    // The negative control for the table: a program whose every resolution is
    // answered by the scope mints nothing. (`Mag<Z>` is *declared*, so its
    // resolution is a reference to the declared instance and not a
    // derivation.)
    let e = ok(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
fn twice<A> requires m: Mag<A> (x: A) -> A {{ combine(x, x) }}
"
    ));
    assert!(e.derived_instances().is_empty(), "{:?}", e.derived_instances());
}

#[test]
fn a_declared_instance_is_found_at_its_own_carrier() {
    ok(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
theorem at_z(): combine(Z0, Z1) = Z1 {{ refl }}
"
    ));
}

#[test]
fn a_nested_derivation_backchains() {
    // `Mag<Pair<Z, Pair<Z, Z>>>` needs `Mag<Pair<Z, Z>>` needs `Mag<Z>` — the
    // subgoal of a subgoal, which is where a resolver that only looks one deep
    // stops working.
    let e = ok(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
fn deep(p: Pair<Z, Pair<Z, Z>>, q: Pair<Z, Pair<Z, Z>>) -> Pair<Z, Pair<Z, Z>> {{
  combine(p, q)
}}
"
    ));
    // Both the inner and the outer derivation are canonical, and the inner one
    // is minted first (it completes inside the outer's derivation).
    assert_eq!(e.derived_instances().len(), 2, "{:?}", e.derived_instances());
}

// -- 2: ascending scopes ---------------------------------------------------

#[test]
fn a_local_dictionary_shadows_the_registry() {
    // Scope beats registry (record §5): `m` is a parameter of the goal type,
    // so it is what resolution returns even though `Mag<Z>` is registered.
    // Pinned by *computation*: this `m` takes the first argument where the
    // registered instance takes the second.
    ok(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
fn first(x: Z, y: Z) -> Z {{ x }}
fn withm(m: Mag<Z>, x: Z, y: Z) -> Z {{ combine(x, y) }}
theorem shadows(): withm(Mag {{ op: first }}, Z0, Z1) = Z0 {{ refl }}
theorem registry(): combine(Z0, Z1) = Z1 {{ refl }}
"
    ));
}

#[test]
fn a_let_bound_dictionary_is_in_scope_for_resolution() {
    // The `let instance` case without the keyword (design §10): a `let` of the
    // goal type is a local, and locals are the first scope.
    ok(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
fn first(x: Z, y: Z) -> Z {{ x }}
fn scoped(x: Z, y: Z) -> Z {{
  let m: Mag<Z> = Mag {{ op: first }};
  combine(x, y)
}}
theorem shadows(): scoped(Z0, Z1) = Z0 {{ refl }}
"
    ));
}

#[test]
fn a_solver_parameter_can_still_be_passed_by_hand() {
    // An instance is an ordinary value; resolution only fills what is omitted.
    // `@` is the spelling — type arguments are never passed at a call site,
    // even under `@` (issues/at-and-type-arguments.md).
    ok(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
fn first(x: Z, y: Z) -> Z {{ x }}
theorem by_hand(): @combine(Mag<Z> {{ op: first }}, Z0, Z1) = Z0 {{ refl }}
"
    ));
}

#[test]
fn a_solver_parameter_has_no_positional_slot() {
    // The negative control for the positive above: passing it positionally is
    // an arity error, not a second spelling.
    let e = bad(&format!(
        "{MONOID}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
fn first(x: Z, y: Z) -> Z {{ x }}
fn oops() -> Z {{ combine(Mag<Z> {{ op: first }}, Z0, Z1) }}
"
    ));
    // The dictionary lands in `x`'s slot, so the rejection is a type error at
    // the argument — which is what "no positional slot" *means* here.
    assert!(e.contains("expected type") || e.contains("combine"), "{e}");
}

// -- 3: negative controls of the disciplines -------------------------------

#[test]
fn overlapping_instances_are_refused_at_the_declaration() {
    // Record §6.2 with layer 1's key: two instances whose input heads unify
    // cannot both be registered, and the refusal names both.
    let e = bad(
        "class Mag<A> { op: A -> A -> A }
record Pair<A, B> { fst: A, snd: B }
inductive Z { Z0, Z1 }
instance<A, B> Mag<Pair<A, B>> requires ma: Mag<A>, mb: Mag<B> {
  fn op(x: Pair<A, B>, y: Pair<A, B>) -> Pair<A, B> { x }
}
instance<B> Mag<Pair<Z, B>> requires mb: Mag<B> {
  fn op(x: Pair<Z, B>, y: Pair<Z, B>) -> Pair<Z, B> { y }
}
",
    );
    assert!(e.contains("Pair") && e.contains("Mag"), "{e}");
}

#[test]
fn a_self_feeding_instance_is_refused() {
    // Termination is a declaration-time property (record §6.3): the subgoal
    // grows, so the search would feed itself, and the refusal names the
    // offending binder rather than hanging at some later use site.
    let e = bad(
        "class Mag<A> { op: A -> A -> A }
record Box<A> { v: A }
instance<A> Mag<Box<A>> requires m: Mag<Box<Box<A>>> {
  fn op(x: Box<A>, y: Box<A>) -> Box<A> { x }
}
",
    );
    assert!(e.contains("m: Mag<Box<Box<A>>>"), "{e}");
    assert!(e.contains("smaller"), "{e}");
}

#[test]
fn a_duplicating_subgoal_is_refused() {
    // The second half of Paterson's condition: the sizes could agree while a
    // variable is duplicated, which is the other way a search grows.
    let e = bad(
        "class Mag<A> { op: A -> A -> A }
record Pair<A, B> { fst: A, snd: B }
instance<A, B> Mag<Pair<A, B>> requires m: Mag<Pair<A, A>> {
  fn op(x: Pair<A, B>, y: Pair<A, B>) -> Pair<A, B> { x }
}
",
    );
    assert!(e.contains("more often"), "{e}");
}

#[test]
fn a_decreasing_instance_is_accepted() {
    // The positive control for the two refusals above, and the shape the whole
    // corpus depends on.
    ok(MONOID);
}

#[test]
fn a_goal_that_stays_meta_bearing_is_reported_at_the_call() {
    // Scheduling (record §6.4): resolution fires only at a meta-free goal.
    // Here nothing ever determines `A`, so the honest report is "the goal is
    // unknown", not "there is no instance".
    let e = bad(&format!(
        "{MONOID}
fn pick<A> requires m: Mag<A> () -> Nat {{ 0 }}
fn oops() -> Nat {{ pick() }}
"
    ));
    assert!(e.contains("could not be inferred"), "{e}");
    assert!(e.contains("pick"), "{e}");
}

#[test]
fn an_unresolvable_goal_reports_its_search() {
    // Trace-as-data (record §7): the diagnostic says which scopes were
    // consulted and what the registry held, as records rather than as prose.
    let e = bad(
        "class Mag<A> { op: A -> A -> A }
inductive Z { Z0, Z1 }
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A { m.op(x, y) }
fn oops(x: Z, y: Z) -> Z { combine(x, y) }
",
    );
    assert!(e.contains("no instance for `Mag<A>`"), "{e}");
    assert!(e.contains("goal:"), "{e}");
    assert!(e.contains("scope:") && e.contains("binder(s) consulted"), "{e}");
    assert!(e.contains("no-instance:"), "{e}");
}

#[test]
fn a_failed_subgoal_appears_nested_in_the_trace() {
    // The nesting is what makes a trace a trace: `Mag<Pair<Z, Y>>` matches the
    // conditional instance, whose `mb` subgoal is what actually fails.
    let e = bad(&format!(
        "{MONOID}
inductive Y {{ Y0 }}
fn combine<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
fn oops(p: Pair<Z, Y>, q: Pair<Z, Y>) -> Pair<Z, Y> {{ combine(p, q) }}
"
    ));
    // The candidate is named as the **registry** holds it — module-qualified
    // (`docs/instance-resolved-key-design.md` §4). A trace line is data about
    // the registry and not a quotation of what the writer typed, and in a
    // program with two `Pair::Mag`s a bare line would name neither.
    assert!(e.contains("candidate: main::Pair::Mag"), "{e}");
    // The subgoal's own search, one level in: the trace nests rather than
    // collapsing to the outermost failure.
    assert!(e.contains("\n      goal: Mag<B>"), "{e}");
}

// -- 4: `:= infer` ---------------------------------------------------------

#[test]
fn infer_finds_a_proof_in_scope() {
    // The general mechanism under instance search (record §8): the goal is an
    // ordinary proposition, and the caller's scope is where it is found.
    ok(
        "theorem uses(n: Nat, h: n = n := infer) : n = n { h }
theorem caller(n: Nat, p: n = n) : n = n { uses(n) }
",
    );
}

#[test]
fn infer_at_a_non_class_goal_says_so() {
    // The negative control, and the trace's other vocabulary: with no value in
    // scope and no registry to consult, the report names the reason.
    let e = bad(
        "theorem uses(n: Nat, h: n = n := infer) : n = n { h }
theorem caller(n: Nat) : n = n { uses(n) }
",
    );
    assert!(e.contains("no instance for `n = n`"), "{e}");
    assert!(e.contains("not a class"), "{e}");
}

#[test]
fn infer_is_refused_on_an_implicit_parameter() {
    // One filling discipline per parameter (design §1).
    let e = bad("theorem t(n: Nat, {h: n = n := infer}) : n = n { h }\n");
    assert!(e.contains("filling discipline") || e.contains("infer"), "{e}");
}

/// `infer` is the only solver; any other expression after `:=` is a
/// parameter default (docs/named-arguments-design.md §9.6), which runs at the
/// call. Here the call runs `omega` with its certificate library absent, and
/// the refusal names both the default and the missing import.
#[test]
fn a_non_solver_after_colon_eq_is_a_default() {
    ok("theorem t(n: Nat, h: n = n := omega) : n = n { h }\n");
    let e = bad("theorem t(n: Nat, h: n = n := omega) : n = n { h }\ntheorem u(k: Nat): k = k { t(k) }\n");
    assert!(e.contains("left to its default") && e.contains("import omega"), "{e}");
}

/// Candidates keyed at the goal carrier's own head are tried before the
/// rest (docs/reflection-through-decide-instances-design.md §3). Both
/// instances below *fit* `Tag<Wrap(3)>` — `Wrap(3)` unfolds to `Nat`, so the
/// `Nat` instance verifies too — and canonical order (`Nat::Tag` before
/// `Wrap::Tag`) would pick the general one. The head-keyed instance is the
/// specific one and wins; where no instance is keyed at the head, the
/// unfolding fit still answers, so nothing that resolved before stops.
///
/// The two general goals come first on purpose: the value-generic winner is
/// minted as the canonical derivation of `Tag<Wrap(3)>`, and the table is
/// keyed by *conversion* (design §9.2), under which `Tag<Nat>` is the same
/// goal — two instances that fit one goal are an overlap the head key does
/// not see, and this test wants the order, not that overlap.
#[test]
fn a_head_keyed_instance_is_tried_before_one_that_fits_by_unfolding() {
    // `id` is what puts the carrier into the lowered goal: a class whose
    // fields never mention `T` lowers to the same Σ at every carrier, and then
    // no instance's parameter has anything to unify against.
    ok("class Tag<T> { tag: Nat, id: T -> T }
fn Wrap(n: Nat) -> Type { Nat }
fn Wrap2(n: Nat) -> Type { Nat }
instance Tag<Nat> { tag := 1, id := λ x => x }
instance(n: Nat) Tag<Wrap(n)> { tag := 2, id := λ x => x }
fn get<T: Tag>() -> Nat { T.tag }
theorem plain(): get<Nat>() = 1 { refl }
theorem unfolding_still_answers(): get<Wrap2(3)>() = 1 { refl }
theorem head_keyed_wins(): get<Wrap(3)>() = 2 { refl }
");
    // The preference is a trace line, so a failed search shows what it read.
    let e = bad(
        "class Tag<T> { tag: Nat, id: T -> T }
fn Wrap(n: Nat) -> Type { Nat }
fn get<T: Tag>() -> Nat { T.tag }
fn oops() -> Nat { get<Wrap(3)>() }
",
    );
    assert!(e.contains("head: main::Wrap"), "{e}");
}
