//! Type-level dot projection — `A.unit`, `G.plus(x, y)`, `Nat.zero`
//! (`docs/traits-type-projection-design.md`, candidate 23 of
//! `issues/requires-placement-syntax.md` §R2-C).
//!
//! The feature is receiver dispatch with one word changed: the **subject is a
//! type**, so the goal is built at the class that declares the field with the
//! subject itself as the carrier, and the subject is not an argument. The
//! emitted term is therefore an ordinary field projection — the very term
//! `⟨dictionary⟩.f` elaborates to — which is why the load-bearing test is
//! `the_two_spellings_are_one_term`: `G.op(x, y)` and `m.op(x, y)` related by
//! `refl`, at a concrete carrier and at an open one.
//!
//! `docs/testing-generated-terms.md`'s axes are varied deliberately: every
//! positive appears at an **open** carrier (a constrained type parameter) and
//! at a **concrete** one (a declared type, and `Nat`, which has no
//! declaration behind it), in **checking** position (a `theorem` whose
//! statement is the equation), and with a **negative control** beside each
//! rule. The growth invariant has its own control: an unbound name's `.f`
//! errors exactly as it did.

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

/// Two one-field classes at one carrier, a law-carrying class, a hierarchy,
/// and a container to make a *derived* carrier available.
const P: &str = r#"
class Mag<A> { op: A -> A -> A }
class Pt<A> { pt: A }
class Sem<A> { sop: A -> A -> A }
class Mon<A> extends Sem<A> {
    unit: A,
    unit_r: (x: A) -> sop(x, unit) = x,
}
record Box<A> { v: A }
inductive Z { Z0, Z1 }

fn zop(x: Z, y: Z) -> Z { y }
instance Mag<Z> { op := zop }
instance Pt<Z> { pt := Z0 }
instance Pt<Nat> { pt := 0 }
fn zfst(x: Z, y: Z) -> Z { x }
instance Mon<Z> {
    sop := zfst,
    unit := Z0,
    unit_r := λ (x: Z) => refl,
}
"#;

// -- 1: the projection itself ----------------------------------------------

#[test]
fn a_type_parameter_projects_an_operation() {
    // The open carrier: nothing concrete anywhere, the dictionary is the
    // inline constraint's own unspellable binder, and the subject of the dot
    // is the type parameter itself.
    ok(&format!(
        "{P}
fn combine<A: Mag>(x: A, y: A) -> A {{ A.op(x, y) }}
fn at_z(p: Z, q: Z) -> Z {{ combine(p, q) }}
"
    ));
}

#[test]
fn a_type_parameter_projects_a_bare_field() {
    // No parentheses. A bare `p.f` is never a *method* call, but a type
    // projection is not a method call — the subject is not an argument — so
    // the bare form is the ordinary one and `A.unit` is a value.
    ok(&format!(
        "{P}
fn zero_of<A: Mon>() -> A {{ A.unit }}
fn at_z() -> Z {{ zero_of() }}
"
    ));
}

#[test]
fn a_concrete_carrier_projects_through_the_registry() {
    // The same sentence with the carrier closed: the goal `Pt<Z>` is answered
    // by the registered instance and nothing is open.
    ok(&format!(
        "{P}
fn z_pt() -> Z {{ Z.pt }}
theorem it_computes(): Z.pt = Z0 {{ refl }}
"
    ));
}

#[test]
fn a_kernel_type_with_no_declaration_projects() {
    // `Nat` names a type nothing declared, so the subject reading cannot come
    // from the inductive table — it comes from reading the expression as a
    // type, which is what makes `Nat.zero` the same sentence as `A.unit`.
    ok(&format!(
        "{P}
fn n_pt() -> Nat {{ Nat.pt }}
theorem it_computes(): Nat.pt = 0 {{ refl }}
"
    ));
}

#[test]
fn a_derived_carrier_projects() {
    // No declared instance at this carrier and no binder in scope: the goal is
    // answered by backchaining through the generic instance, which the
    // projection inherits from `resolve_goal` rather than restating.
    ok(&format!(
        "{P}
instance<A: Pt> Pt<Box<A>> {{ pt := Box {{ v: A.pt }} }}
fn boxed() -> Box<Z> {{ Box<Z>.pt }}
"
    ));
}

#[test]
fn an_inherited_member_projects_at_its_owner() {
    // `sop` is declared by `Sem` and the constraint is a `Mon`, so the goal is
    // built at the ancestor and answered by the resolver's **upcast** — at an
    // open carrier, where no synthesized parent exists to be found instead
    // (docs/traits-owner-dispatch-design.md §3).
    ok(&format!(
        "{P}
fn twice<A: Mon>(x: A) -> A {{ A.sop(x, x) }}
fn at_z(p: Z) -> Z {{ twice(p) }}
"
    ));
}

#[test]
fn a_proof_field_projects_like_an_operation() {
    // The whole point of emitting a projection rather than a call: a law field
    // is a field, so `A.unit_r(x)` needs nothing of its own — and this is a
    // **checking** position, the statement being what the proof is checked
    // against.
    ok(&format!(
        "{P}
theorem right_unit<A: Mon>(x: A): A.sop(x, A.unit) = x {{ A.unit_r(x) }}
theorem at_z(x: Z): Z.sop(x, Z.unit) = x {{ right_unit(x) }}
"
    ));
}

#[test]
fn a_bare_operation_field_is_a_value() {
    // The consequence of the subject not being an argument: a class member is
    // partially applicable through a type, where through a receiver it is not
    // (`docs/traits-receiver-dispatch-design.md` §8). Recorded as residue
    // there; pinned as behaviour here.
    ok(&format!(
        "{P}
fn partial() -> Z -> Z -> Z {{ Z.op }}
theorem it_is_the_dictionary_field(): Z.op = Z::Mag.op {{ refl }}
"
    ));
}

// -- 2: agreement ----------------------------------------------------------

#[test]
fn the_two_spellings_are_one_term() {
    // The headline. `refl` is the kernel agreeing that projecting from the
    // TYPE and projecting from a named dictionary build the same term — at a
    // concrete carrier, where the dictionary is the registered global.
    ok(&format!(
        "{P}
theorem same(x: Z, y: Z): Z.op(x, y) = Z::Mag.op(x, y) {{ refl }}
"
    ));
}

#[test]
fn the_two_spellings_are_one_term_at_an_open_carrier() {
    // The same pin with the carrier **open** and the dictionary a binder: the
    // `requires` spelling names it, the projection does not, and the two
    // functions are related by `refl` at a neutral argument.
    ok(&format!(
        "{P}
fn by_type<A: Mag>(x: A, y: A) -> A {{ A.op(x, y) }}
fn by_name<A> requires m: Mag<A> (x: A, y: A) -> A {{ m.op(x, y) }}
theorem same(p: Z, q: Z): by_type(p, q) = by_name(p, q) {{ refl }}
"
    ));
}

#[test]
fn a_type_projection_and_a_receiver_dispatch_are_one_term() {
    // `G.plus(x, y)` and `x.plus(y)` — the two sugars the last two rounds
    // added — reach the same projection of the same dictionary.
    ok(&format!(
        "{P}
fn by_type<A: Mag>(x: A, y: A) -> A {{ A.op(x, y) }}
fn by_recv<A: Mag>(x: A, y: A) -> A {{ x.op(y) }}
theorem same(p: Z, q: Z): by_type(p, q) = by_recv(p, q) {{ refl }}
"
    ));
}

// -- 3: the escape ---------------------------------------------------------

#[test]
fn the_escape_names_the_class_at_an_open_carrier() {
    // Two classes declare `pt`, so the bare projection is ambiguous (below);
    // `A::Pt2.pt` says which, and it is the same path spelling the library
    // already used at a concrete carrier.
    ok(&format!(
        "{P}
class Pt2<A> {{ pt: A }}
instance Pt2<Z> {{ pt := Z1 }}
fn one<A: Pt + Pt2>() -> A {{ A::Pt2.pt }}
fn at_z() -> Z {{ one() }}
"
    ));
}

#[test]
fn the_escape_is_a_value_and_not_only_a_dot_receiver() {
    // `A::Pt` resolves to the dictionary itself, so it can be bound, passed,
    // and projected by the ordinary record path — no second rule.
    ok(&format!(
        "{P}
fn one<A: Pt>() -> A {{ let d: Pt<A> = A::Pt; d.pt }}
fn at_z() -> Z {{ one() }}
"
    ));
}

#[test]
fn the_escape_at_a_concrete_carrier_is_the_registered_instance() {
    // At a closed carrier the qualified name is an ordinary global and never
    // reaches the new fallback, which is what keeps the library's existing
    // `Nat::AddCommMonoid.plus` spelling meaning exactly what it meant.
    ok(&format!(
        "{P}
theorem same(x: Z, y: Z): Z::Mag.op(x, y) = Z.op(x, y) {{ refl }}
"
    ));
}

#[test]
fn the_escape_reports_the_search_when_nothing_answers() {
    let msg = bad(&format!(
        "{P}
fn one<A>() -> A {{ A::Pt.pt }}
"
    ));
    assert!(msg.contains("Pt<A>"), "{msg}");
    assert!(msg.contains("the search") || msg.contains("goal:"), "{msg}");
}

// -- 4: ambiguity and the negative controls --------------------------------

#[test]
fn two_classes_declaring_one_name_at_one_type_are_ambiguous() {
    // Receiver dispatch's rule 3, verbatim: name every hit, never pick, and
    // say what to write instead.
    let msg = bad(&format!(
        "{P}
class Pt2<A> {{ pt: A }}
instance Pt2<Z> {{ pt := Z1 }}
fn z_pt() -> Z {{ Z.pt }}
"
    ));
    assert!(msg.contains("Pt<Z>") && msg.contains("Pt2<Z>"), "{msg}");
    assert!(msg.contains("class you meant"), "{msg}");
}

#[test]
fn an_unconstrained_type_parameter_names_the_search() {
    // NOT "unbound name": the subject is a type, the field is some class's,
    // and what failed is a resolution — so the trace is the diagnosis.
    let msg = bad(&format!(
        "{P}
fn one<A>() -> A {{ A.pt }}
"
    ));
    assert!(msg.contains("Pt<A>"), "{msg}");
    assert!(msg.contains("goal:"), "{msg}");
    assert!(msg.contains("binder(s) consulted"), "{msg}");
}

#[test]
fn a_type_with_no_instance_names_the_search() {
    // The concrete twin of the above: `Box<Z>` has no `Pt` instance, and the
    // registry's own account of why is what is printed.
    let msg = bad(&format!(
        "{P}
fn one() -> Box<Z> {{ Box<Z>.pt }}
"
    ));
    assert!(msg.contains("Pt<Box>"), "{msg}");
    assert!(msg.contains("candidate") || msg.contains("instance"), "{msg}");
}

#[test]
fn a_value_binder_shadows_the_type_reading() {
    // The growth invariant's sharpest case: a parameter named like a type.
    // Its own field wins and the class is never consulted, because the subject
    // reading asks the receiver's *type* — a universe or nothing.
    let e = ok(&format!(
        "{P}
record Holder {{ pt: Z }}
fn f(Z: Holder) -> Z {{ Z.pt }}
theorem it_is_the_field(h: Holder): f(h) = h.pt {{ refl }}
"
    ));
    let _ = e;
}

#[test]
fn an_unbound_name_still_errors_as_before() {
    // No existing program is reinterpreted: a `.f` whose subject names neither
    // a value nor a type reports what it always reported.
    let msg = bad(&format!(
        "{P}
fn f() -> Z {{ Q.pt }}
"
    ));
    assert!(msg.contains("could not be inferred"), "{msg}");
}

#[test]
fn a_record_field_still_wins_over_the_class() {
    // Rule 1 of receiver dispatch, untouched: a value receiver whose own type
    // has the field projects it, whatever classes exist.
    ok(&format!(
        "{P}
record Holder {{ pt: Z }}
fn f(h: Holder) -> Z {{ h.pt }}
"
    ));
}

// -- 5: the other-reading rule ---------------------------------------------

#[test]
fn a_global_that_cannot_take_a_type_is_not_a_competing_reading() {
    // `op` is an ambient global here, so `x.op(y)` on a RECEIVER is ambiguous
    // against it. On a **type** subject it is not: the desugaring would put a
    // type in `op`'s first `Z` slot, and that is decided from `op`'s own
    // telescope rather than by trying the call.
    ok(&format!(
        "{P}
fn op(x: Z, y: Z) -> Z {{ x }}
fn f(x: Z, y: Z) -> Z {{ Z.op(x, y) }}
theorem it_is_the_class(x: Z, y: Z): Z.op(x, y) = Z::Mag.op(x, y) {{ refl }}
"
    ));
}

#[test]
fn a_global_that_can_take_a_type_names_both_readings() {
    // The control for the rule above: when the ambient global's subject slot
    // really is at a universe, both readings exist and the answer is an
    // ambiguity naming both — never a preference.
    let msg = bad(&format!(
        "{P}
fn op(A: Type<0>, x: Z, y: Z) -> Z {{ x }}
fn f(x: Z, y: Z) -> Z {{ Z.op(x, y) }}
"
    ));
    assert!(msg.contains("Mag<Z>"), "{msg}");
    assert!(msg.contains("a name in scope on its own"), "{msg}");
}

#[test]
fn a_bare_projection_has_no_other_reading() {
    // A bare `T.f` is not a call, so the method desugaring is not a reading of
    // it at all and the ambient global cannot make it ambiguous.
    ok(&format!(
        "{P}
fn pt(A: Type<0>) -> Z {{ Z1 }}
theorem it_is_the_class(): Z.pt = Z::Pt.pt {{ refl }}
"
    ));
}

// -- 6: the shape narrowings, refused by name ------------------------------

#[test]
fn a_member_of_a_multi_parameter_class_is_refused_by_name() {
    // §2.1's narrowing, inherited: the subject fixes the carrier and nothing
    // fixes the rest, so the goal would carry a meta — which layer 2 declines
    // to resolve on purpose. Refused by name rather than mis-projected.
    let msg = bad(&format!(
        "{P}
class Pair2<A, B> {{ both: A -> B -> A }}
fn f<A: Mag>(x: A, y: A) -> A {{ A.both(x, y) }}
"
    ));
    assert!(msg.contains("Pair2"), "{msg}");
    assert!(msg.contains("type parameters"), "{msg}");
}

#[test]
fn multi_parameter_projection_uses_a_complete_local_dictionary() {
    ok(r#"
class Mapping<S, A> { send: A → S, witness: S }
fn deliver<S, A> requires d: Mapping<S, A> (a: A) → S { S.send(a) }
theorem same_projection<S, A> requires d: Mapping<S, A> (a: A):
    S.send(a) = d.send(a) { refl }
fn under_binder<S, A> requires d: Mapping<S, A> () → (a: A) → S { λ a => S.send(a) }
fn alias<S, A>(d: Mapping<S, A>, a: A) → S {
    let d: Mapping<S, A> = d;
    S.send(a)
}
"#);
    let ambiguous = bad(r#"
class Mapping<S, A> { send: A → S }
fn ambiguous<S, A, B> requires first: Mapping<S, A>, second: Mapping<S, B> (a: A) → S { S.send(a) }
"#);
    assert!(ambiguous.contains("each has an instance"), "{ambiguous}");
    ok(r#"
class Mapping<S, A> { send: A → S }
fn explicit<S, A, B> requires first: Mapping<S, A>, second: Mapping<S, B> (a: A) → S { first.send(a) }
"#);
    let unrelated = bad(r#"
class Mapping<S, A> { send: A → S }
fn unrelated<S, T, A> requires d: Mapping<T, A> (a: A) → S { S.send(a) }
"#);
    assert!(unrelated.contains("type parameters"), "{unrelated}");
    let shadowed = bad(r#"
class Mapping<S, A> { send: A → S }
fn shadowed<S, A> requires d: Mapping<S, A> (a: A) → S {
    let d = 0;
    S.send(a)
}
"#);
    assert!(shadowed.contains("type parameters"), "{shadowed}");
}

#[test]
fn multi_parameter_projection_follows_tagged_parents_without_guessing_carriers() {
    ok(r#"
class Mapping<S, A> { send: A → S }
class WithOps<S, A> extends Mapping<S, A> as operations {}
theorem inherited<S, A> requires d: WithOps<S, A> (a: A):
    S.send(a) = d.operations.send(a) { refl }
"#);
    let ambiguous = bad(r#"
class Mapping<S, A> { send: A → S }
class Two<S, A, B> extends Mapping<S, A> as first, Mapping<S, B> as second {}
fn ambiguous<S, A, B> requires d: Two<S, A, B> (a: A) → S { S.send(a) }
"#);
    assert!(ambiguous.contains("each has an instance"), "{ambiguous}");
    let wrong_carrier = bad(r#"
class Mapping<S, A> { send: A → S }
class Swapped<S, A> extends Mapping<A, S> as operations {}
fn wrong<S, A> requires d: Swapped<S, A> (s: S) → A { S.send(s) }
"#);
    assert!(wrong_carrier.contains("type parameters"), "{wrong_carrier}");
}
