//! The inline constraint form — `<A: Monoid>`, stacked with `+`
//! (`issues/requires-placement-syntax.md` §R2-A, decided 2026-08-07).
//!
//! The whole feature is a *parse-time desugaring*: `A: C` is the parameter
//! `requires _: C<A>` would have produced — implicit, `Solver::Infer`, at the
//! front of the value-parameter list. So the load-bearing tests are the ones
//! that pin the two spellings as the SAME term
//! (`the_two_spellings_are_one_term`, and its open-carrier twin), the ones
//! that pin the order `+` gives the binders (`stacking_order_is_binder_order`,
//! read through `@`, the only place the order is observable), and the ones
//! that pin what the form deliberately does NOT offer — a name for the
//! dictionary (`the_constraint_binder_is_unspellable`).
//!
//! `docs/testing-generated-terms.md`'s axes are varied deliberately: every
//! positive appears at a **concrete** carrier and at an **open** one (a
//! constrained `fn` calling another), in **checking** position (a `theorem`
//! whose statement is the equation, checked against `refl`), with a negative
//! control beside each rule.

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

/// Two one-field classes at one carrier — two classes, because the whole point
/// of `+` is that a binder can carry more than one structure — plus a
/// container to make an **open** carrier available.
const P: &str = r#"
class Mag<A> { op: A -> A -> A }
class Pt<A> { pt: A }
record Box<A> { v: A }
inductive Z { Z0, Z1 }

fn zop(x: Z, y: Z) -> Z { y }
instance Mag<Z> { op := zop }
instance Pt<Z> { pt := Z0 }
"#;

// -- 1: the desugaring is the feature --------------------------------------

#[test]
fn an_inline_constraint_is_resolved_like_a_requires_binder() {
    ok(&format!(
        "{P}
fn combine<A: Mag>(x: A, y: A) -> A {{ x.op(y) }}
fn at_z(p: Z, q: Z) -> Z {{ combine(p, q) }}
"
    ));
}

#[test]
fn the_two_spellings_are_one_term() {
    // The headline. `refl` here is the kernel agreeing that the inline form
    // and the `requires` form built the same telescope, in the same order,
    // with the same solver — checked at a concrete carrier.
    ok(&format!(
        "{P}
fn inline<A: Mag>(x: A, y: A) -> A {{ x.op(y) }}
fn spelt<A> requires m: Mag<A> (x: A, y: A) -> A {{ x.op(y) }}
theorem same(p: Z, q: Z): inline(p, q) = spelt(p, q) {{ refl }}
"
    ));
}

#[test]
fn the_two_spellings_are_one_term_at_an_open_carrier() {
    // The same pin with the carrier **open** — the axis that hid three of the
    // five defects `docs/testing-generated-terms.md` records. Both dictionaries
    // are found in the room, from a binder nobody wrote a name for.
    ok(&format!(
        "{P}
fn inline<A: Mag>(x: A, y: A) -> A {{ x.op(y) }}
fn spelt<A> requires m: Mag<A> (x: A, y: A) -> A {{ x.op(y) }}
theorem same_open<A: Mag>(x: A, y: A): inline(x, y) = spelt(x, y) {{ refl }}
"
    ));
}

#[test]
fn a_constrained_function_calls_another_from_its_own_binder() {
    // The recursion/room case: `twice`'s dictionary is its own constraint, and
    // `combine`'s goal is answered from it rather than from the registry.
    ok(&format!(
        "{P}
fn combine<A: Mag>(x: A, y: A) -> A {{ x.op(y) }}
fn twice<A: Mag>(x: A) -> A {{ combine(x, x) }}
fn at_z(p: Z) -> Z {{ twice(p) }}
"
    ));
}

#[test]
fn the_bracket_still_takes_one_type_argument() {
    // §R2-A's concrete advantage over grouped generics: a constraint is an
    // *annotation on an entry*, not an entry, so explicit type application is
    // untouched — the declaration bracket and the call bracket keep saying the
    // same thing.
    ok(&format!(
        "{P}
fn combine<A: Mag>(x: A, y: A) -> A {{ x.op(y) }}
fn at_z(p: Z, q: Z) -> Z {{ combine<Z>(p, q) }}
"
    ));
}

#[test]
fn a_constraint_is_not_a_type_argument() {
    // The negative control for the above: two type arguments is still an arity
    // error. Nothing about `<A: Mag>` added a slot.
    let e = bad(&format!(
        "{P}
fn combine<A: Mag>(x: A, y: A) -> A {{ x.op(y) }}
fn oops(p: Z, q: Z) -> Z {{ combine<Z, Z>(p, q) }}
"
    ));
    assert!(e.contains("type argument"), "{e}");
}

// -- 2: `+` stacking --------------------------------------------------------

#[test]
fn stacking_resolves_both_constraints() {
    // Both structures are really there and really used: `op` through receiver
    // dispatch on the binder, `pt` through a `requires`-spelt helper whose own
    // goal is answered from the stacked constraint.
    ok(&format!(
        "{P}
fn ptof<A> requires p: Pt<A> (x: A) -> A {{ p.pt }}
fn twiddle<A: Mag + Pt>(x: A) -> A {{ x.op(ptof(x)) }}
fn at_z(z: Z) -> Z {{ twiddle(z) }}
"
    ));
}

#[test]
fn stacking_order_is_binder_order() {
    // `@` is the only place the order of solver parameters is observable
    // (docs/traits-layer2-design.md §1), so it is where the order is pinned:
    // left-to-right across the whole bracket, `Mag` before `Pt`.
    ok(&format!(
        "{P}
fn twiddle<A: Mag + Pt>(x: A) -> A {{ x.op(x) }}
theorem by_hand(z: Z): @twiddle(Z::Mag, Z::Pt, z) = twiddle(z) {{ refl }}
"
    ));
}

#[test]
fn stacking_order_reversed_is_refused() {
    // The negative control: the order is a fact, not a preference.
    let e = bad(&format!(
        "{P}
fn twiddle<A: Mag + Pt>(x: A) -> A {{ x.op(x) }}
theorem by_hand(z: Z): @twiddle(Z::Pt, Z::Mag, z) = twiddle(z) {{ refl }}
"
    ));
    // The dictionaries are swapped, so the term the caller wrote is not the
    // term resolution builds, and the kernel says so at the declaration gate.
    assert!(e.contains("NotConvertible"), "{e}");
}

#[test]
fn constraints_lead_the_requires_binders() {
    // Both spellings on one declaration — the documented coexistence. The
    // inline constraints come first, then the written `requires` binders, and
    // `@` says so.
    ok(&format!(
        "{P}
fn mixed<A: Mag> requires p: Pt<A> (x: A) -> A {{ x.op(p.pt) }}
theorem by_hand(z: Z): @mixed(Z::Mag, Z::Pt, z) = mixed(z) {{ refl }}
"
    ));
}

#[test]
fn several_parameters_may_each_be_constrained() {
    ok(&format!(
        "{P}
fn two<A: Mag, B: Pt>(x: A, y: B) -> A {{ x.op(x) }}
fn at_z(p: Z, q: Z) -> Z {{ two(p, q) }}
"
    ));
}

#[test]
fn a_mixed_list_may_leave_a_parameter_unconstrained() {
    ok(&format!(
        "{P}
fn pick<A: Mag, B>(x: A, y: B) -> A {{ x.op(x) }}
fn at_z(p: Z, q: Box<Z>) -> Z {{ pick(p, q) }}
"
    ));
}

#[test]
fn a_class_may_carry_arguments_after_its_carrier() {
    // `A: C<X>` is `C<A, X>` — the annotated binder is always the class's
    // FIRST argument, which is what makes the inline form a hoist of the
    // sentence `A: C` rather than a second feature.
    ok(&format!(
        "{P}
class Coe<A, B> {{ co: A -> B }}
fn zbox(x: Z) -> Box<Z> {{ Box {{ v: x }} }}
instance Coe<Z, Box<Z>> {{ co := zbox }}
fn coerce<A, B> requires c: Coe<A, B> (x: A) -> B {{ c.co(x) }}
fn up<A: Coe<Box<Z>>>(x: A) -> Box<Z> {{ coerce(x) }}
fn at_z(p: Z) -> Box<Z> {{ up(p) }}
"
    ));
}

// -- 3: the two nouns under one colon --------------------------------------

#[test]
fn the_universe_annotation_still_parses() {
    ok("fn id<A: Type<1>>(x: A) -> A { x }");
}

#[test]
fn a_universe_and_a_class_stack() {
    // `<A: Type<1> + Monoid>` — one says where `A` lives, the other what it
    // carries, and a binder may state both (§R2-A).
    ok(&format!(
        "{P}
fn combine<A: Type<1> + Mag>(x: A, y: A) -> A {{ x.op(y) }}
"
    ));
}

#[test]
fn the_universe_annotation_must_lead() {
    // A universe is not a structure, so it cannot be a later entry in a list
    // of structures. Refused by name rather than parsed into a class called
    // `Type`.
    let e = bad(&format!(
        "{P}
fn combine<A: Mag + Type<1>>(x: A, y: A) -> A {{ x.op(y) }}
"
    ));
    assert!(e.contains("can only lead"), "{e}");
}

#[test]
fn a_word_that_is_neither_names_both_readings() {
    let e = bad(&format!(
        "{P}
fn combine<A: Bogus>(x: A) -> A {{ x }}
"
    ));
    assert!(e.contains("is not a class"), "{e}");
    assert!(e.contains("Type<n>"), "{e}");
    assert!(e.contains("class"), "{e}");
}

#[test]
fn a_type_that_is_not_a_class_names_both_readings() {
    // The sharper case: `Box` exists, so "unknown type" would be a lie, and
    // the complaint has to be about the *reading* rather than the name.
    let e = bad(&format!(
        "{P}
fn combine<A: Box>(x: A) -> A {{ x }}
"
    ));
    assert!(e.contains("`Box` is not a class"), "{e}");
    assert!(e.contains("Type<n>"), "{e}");
}

#[test]
fn a_non_name_after_the_colon_names_both_readings() {
    let e = bad("fn combine<A: 3>(x: A) -> A { x }");
    assert!(e.contains("Type<n>"), "{e}");
    assert!(e.contains("class constraint"), "{e}");
}

// -- 4: what the form deliberately does not offer --------------------------

#[test]
fn the_constraint_binder_is_unspellable() {
    // The inline form is anonymous by construction: there is no name to reach
    // the dictionary by, which is exactly why a body that needs one writes
    // `requires`. Nothing is bound under any spellable name.
    let e = bad(&format!(
        "{P}
fn combine<A: Mag>(x: A) -> A {{ m }}
"
    ));
    assert!(e.contains("unbound name `m`"), "{e}");
    // …and the generated name cannot be written either: `#` does not begin an
    // identifier in this grammar.
    let e = bad(&format!(
        "{P}
fn combine<A: Mag>(x: A) -> A {{ #constraint0.op(x, x) }}
"
    ));
    assert!(e.contains("parse error"), "{e}");
}

#[test]
fn a_named_constraint_is_refused_by_name() {
    let e = bad(&format!(
        "{P}
fn combine<A: Mag as m>(x: A) -> A {{ m.op(x, x) }}
"
    ));
    assert!(e.contains("not implemented"), "{e}");
    assert!(e.contains("requires m: Monoid<A>"), "{e}");
}

#[test]
fn the_carrier_slot_wildcard_is_refused_by_name() {
    let e = bad(&format!(
        "{P}
class Coe<A, B> {{ co: A -> B }}
fn back<A: Coe<_, Z>>(x: A) -> A {{ x }}
"
    ));
    assert!(
        e.contains("`_` in a constraint's arguments is not implemented"),
        "{e}"
    );
    assert!(e.contains("FIRST slot"), "{e}");
}

#[test]
fn a_given_clause_is_refused_by_name() {
    let e = bad(&format!(
        "{P}
fn flatten<A>(x: Box<Box<A>>) -> Box<A> given Box<A>: Mag {{ x.v }}
"
    ));
    assert!(e.contains("`given` clause is not implemented"), "{e}");
    assert!(e.contains("requires"), "{e}");
}

#[test]
fn section_variables_and_bundles_are_refused_by_name() {
    for w in ["section", "given", "context"] {
        let e = bad(&format!("{w} A: Mag;\n"));
        assert!(e.contains("not implemented"), "{w}: {e}");
        assert!(e.contains("requires"), "{w}: {e}");
    }
}

// -- 5: the instance head ---------------------------------------------------

#[test]
fn a_generic_instance_takes_inline_constraints() {
    // `instance<A: Mag> Mag<Box<A>>` — the same sentence at the instance head,
    // where round 1's in-list candidates could not reach. Paterson accepts it:
    // the subgoal `Mag<A>` is structurally smaller than the head `Mag<Box<A>>`.
    ok(&format!(
        "{P}
fn boxop<A: Mag>(x: Box<A>, y: Box<A>) -> Box<A> {{ Box {{ v: x.v.op(y.v) }} }}
instance<A: Mag> Mag<Box<A>> {{ op := boxop }}
fn at_box(p: Box<Z>, q: Box<Z>) -> Box<Z> {{ p.op(q) }}
"
    ));
}

#[test]
fn a_generic_instance_agrees_with_the_requires_spelling() {
    // The instance-head twin of `the_two_spellings_are_one_term`: written both
    // ways at two carriers, the resolved dictionaries compute alike.
    ok(&format!(
        "{P}
record Cell<A> {{ c: A }}
fn boxop<A: Mag>(x: Box<A>, y: Box<A>) -> Box<A> {{ Box {{ v: x.v.op(y.v) }} }}
fn cellop<A> requires m: Mag<A> (x: Cell<A>, y: Cell<A>) -> Cell<A> {{
    Cell {{ c: m.op(x.c, y.c) }}
}}
instance<A: Mag> Mag<Box<A>> {{ op := boxop }}
instance<A> Mag<Cell<A>> requires m: Mag<A> {{ op := cellop }}
theorem agree(p: Box<Z>, q: Box<Z>, r: Cell<Z>, s: Cell<Z>):
    p.op(q).v = @boxop(Z::Mag, p, q).v
{{ refl }}
"
    ));
}

#[test]
fn the_inline_form_cannot_state_a_nonterminating_instance() {
    // A correction found while implementing, recorded on the issue: because an
    // inline constraint is always `C<A>` on a *binder*, the only head that
    // could fail Paterson's size test is a bare `C<A>` — and that carrier has
    // no head type name, so layer 1's canonical-name rule refuses it one step
    // earlier. The `requires` spelling remains the one that can state a loop
    // (`instance<A> Mag<Box<A>> requires m: Mag<Box<Box<A>>>`, pinned in
    // `traits_resolution.rs`), and it remains refused.
    let e = bad(&format!(
        "{P}
fn magop<A: Mag>(x: A, y: A) -> A {{ x.op(y) }}
instance<A: Mag> Mag<A> {{ op := magop }}
"
    ));
    // The owner rule's wording widened 2026-08-17 ("a type or a type former",
    // `docs/decide-class-design.md` §2.3); a bare type parameter is neither, so
    // this is refused on exactly the path it always was.
    assert!(
        e.contains("head type name") || e.contains("not a type"),
        "{e}"
    );
}
