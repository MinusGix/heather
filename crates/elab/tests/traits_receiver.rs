//! Receiver dispatch through instances: `x.op(y)`
//! (`docs/language/classes/traits-receiver-dispatch-design.md`, `issues/traits.md`).
//!
//! Everything dispatch emits is a *generated term*
//! (`docs/testing-generated-terms.md`) — a projection of a term the writer
//! never wrote — so the four axes are varied throughout: an **open** carrier
//! (a class reached through a `fn`'s own type parameter), a **checking**
//! position (the dispatched call as a checked argument and as an annotated
//! `let`), a **neutral** receiver (parameters, and a receiver that is itself a
//! computed call, not only a constructor literal), and a **negative control**
//! beside each positive.
//!
//! The load-bearing tests, if only four are read:
//! `a_concrete_carrier_dispatches_to_the_explicit_spelling` (the whole point,
//! and the pin that the emitted term *is* the projection),
//! `a_generic_carrier_dispatches_through_its_binder` (the case layer 1 could
//! not reach at all), `a_local_dictionary_beats_the_registry_at_dispatch`
//! (layer 2's ascending scopes survive the new caller — pinned with a
//! dictionary that is *not* the registry's), and
//! `two_classes_sharing_a_member_name_are_ambiguous` (a dispatch never picks).

use heather_elab::{ElabError, Elaborator};

/// Elaborate modules in order into one accumulator — the shape of one
/// `heather check` run, borrowed from `tests/modules.rs`.
fn run(mods: &[(&str, &str)]) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in mods {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
    }
    Ok(e)
}

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

/// A one-field class, a concrete carrier, and a generic one — the same corpus
/// layer 2's suite uses, so the two rounds' claims are about one program.
const MAG: &str = r#"
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

// -- 1: the concrete carrier -----------------------------------------------

/// The headline. `a.op(b)` at a declared instance's carrier elaborates, and
/// the term it emits is the explicit projection — `refl` between them is
/// syntactic agreement, not a conversion that happened to go through
/// (design §2.2).
#[test]
fn a_concrete_carrier_dispatches_to_the_explicit_spelling() {
    ok(&format!(
        "{MAG}
         fn dispatched(a: Z, b: Z) -> Z {{ a.op(b) }}
         fn explicit(a: Z, b: Z) -> Z {{ Z::Mag.op(a, b) }}
         theorem agrees(a: Z, b: Z) : dispatched(a, b) = explicit(a, b) {{ refl }}
         // and it *computes*: the instance's `op` returns its second argument.
         theorem computes(a: Z, b: Z) : a.op(b) = b {{ refl }}
         // a kernel type with no declaration is a carrier like any other:
         // `type_namespace` answers for `Nat`, and so does the goal builder.
         instance Mag<Nat> {{ fn op(x: Nat, y: Nat) -> Nat {{ Succ(y) }} }}
         theorem on_Nat(a: Nat, b: Nat) : a.op(b) = Succ(b) {{ refl }}"
    ));
}

/// The receiver is neutral in every test above (a parameter); here it is a
/// *computed call*, which is the harder neutral — the dispatch has to infer a
/// receiver whose type comes off an application.
#[test]
fn a_computed_receiver_dispatches() {
    ok(&format!(
        "{MAG}
         fn f(x: Z) -> Z {{ x }}
         theorem computed(a: Z, b: Z) : f(a).op(b) = b {{ refl }}
         // and a literal receiver, the other half of the axis.
         theorem literal(b: Z) : Z0.op(b) = b {{ refl }}"
    ));
}

/// Checking position, twice: as a checked argument of a callee that fixes the
/// type, and under an annotated `let`. Dispatch has no inference-only route,
/// and this is what says so.
#[test]
fn dispatch_works_in_checking_position() {
    ok(&format!(
        "{MAG}
         fn snd(x: Z, y: Z) -> Z {{ y }}
         fn checked(a: Z, b: Z) -> Z {{ snd(a, a.op(b)) }}
         fn annotated(a: Z, b: Z) -> Z {{ let c: Z = a.op(b); c }}
         theorem both(a: Z, b: Z) : checked(a, b) = annotated(a, b) {{ refl }}"
    ));
}

// -- 2: the generic carrier -------------------------------------------------

/// The case layer 1 could not reach: an **open** carrier, where the
/// dictionary is a binder and there is no registry entry to find. The pin is
/// that the emitted term uses `m` — `refl` against the explicit `m.op(x, y)`
/// at a neutral receiver, where nothing computes. `twice` is written in the
/// inline constraint form and `uses_m` in the `requires` one, because the pin
/// needs a name to project and the dispatching declaration does not.
#[test]
fn a_generic_carrier_dispatches_through_its_binder() {
    ok(&format!(
        "{MAG}
         fn twice<A: Mag>(x: A, y: A) -> A {{ x.op(y) }}
         theorem uses_m<A> requires m: Mag<A> (x: A, y: A) : x.op(y) = m.op(x, y) {{ refl }}
         // instantiated at the concrete carrier, it is still the instance's.
         theorem at_Z(a: Z, b: Z) : twice(a, b) = b {{ refl }}"
    ));
}

/// No binder in scope and no declared instance at the carrier: the goal is
/// answered by *backchaining* through the generic `Pair` instance, which is
/// the case that decides dispatch goes through resolution rather than through
/// a scope scan (design §2).
#[test]
fn a_derivable_carrier_dispatches_with_no_binder_in_scope() {
    ok(&format!(
        "{MAG}
         fn combine(p: Pair<Z, Z>, q: Pair<Z, Z>) -> Pair<Z, Z> {{ p.op(q) }}
         // and it computes componentwise, through the derived dictionary.
         theorem computes(a: Z, b: Z, c: Z, d: Z)
           : combine(Pair {{ fst: a, snd: b }}, Pair {{ fst: c, snd: d }}).fst = c {{ refl }}"
    ));
}

// -- 3: the orders that must not change -------------------------------------

/// Layer 2's ascending scopes, observed through the new caller. The local
/// dictionary is deliberately **not** the registry's: its `op` returns the
/// first argument where `Z::Mag`'s returns the second, so `refl` can tell
/// which one dispatch used — a dictionary that happened to agree would pin
/// nothing (design §4 rule 4).
#[test]
fn a_local_dictionary_beats_the_registry_at_dispatch() {
    ok(&format!(
        "{MAG}
         theorem scoped(m: Mag<Z>, a: Z, b: Z) : a.op(b) = m.op(a, b) {{ refl }}"
    ));
}

/// The negative control for it: with that dictionary in scope, dispatch is
/// *not* the registry's instance any more, so the equation that held without
/// it fails.
#[test]
fn the_registry_does_not_win_when_a_dictionary_is_in_scope() {
    let e = bad(&format!(
        "{MAG}
         theorem no(m: Mag<Z>, a: Z, b: Z) : a.op(b) = Z::Mag.op(a, b) {{ refl }}"
    ));
    assert!(e.contains("kernel") || e.contains("refl"), "{e}");
}

/// A field of the receiver's **own** type wins, and dispatch is not attempted
/// (design §4 rule 1): `B` has a field `op` and an instance of `Mag<B>` at the
/// same time, and `b.op(z)` is the field — which the types make observable,
/// since the field takes a `Z` and the class member takes a `B`.
#[test]
fn a_field_of_the_receivers_own_type_wins() {
    ok(&format!(
        "{MAG}
         record B {{ op: Z -> Z }}
         instance Mag<B> {{ fn op(x: B, y: B) -> B {{ y }} }}
         fn field(b: B, z: Z) -> Z {{ b.op(z) }}
         // the class member is still reachable, by its own spelling.
         fn member(x: B, y: B) -> B {{ B::Mag.op(x, y) }}"
    ));
}

// -- 4: the ambiguities -----------------------------------------------------

/// Two classes with one member name, both with an instance at the carrier:
/// an error naming **both**, never a pick (design §4 rule 3).
#[test]
fn two_classes_sharing_a_member_name_are_ambiguous() {
    let e = bad(&format!(
        "{MAG}
         class Mag2<A> {{ op: A -> A -> A }}
         instance Mag2<Z> {{ fn op(x: Z, y: Z) -> Z {{ x }} }}
         fn f(a: Z, b: Z) -> Z {{ a.op(b) }}"
    ));
    assert!(e.contains("Mag<Z>") && e.contains("Mag2<Z>"), "{e}");
}

/// An ordinary type-owned member and a class member at one carrier: an error
/// naming both, by the same growth invariant that makes `member_head` refuse
/// to race a bare name against a `D::name`
/// (issues/type-owned-members-receiver-slice.md, design §4 rule 2).
#[test]
fn an_ordinary_member_and_a_class_member_are_ambiguous() {
    let e = bad(&format!(
        "{MAG}
         fn Z::op(x: Z, y: Z) -> Z {{ x }}
         fn f(a: Z, b: Z) -> Z {{ a.op(b) }}"
    ));
    assert!(e.contains("both"), "{e}");
    // Both spellings still work on their own.
    ok(&format!(
        "{MAG}
         fn Z::op(x: Z, y: Z) -> Z {{ x }}
         fn viaMember(a: Z, b: Z) -> Z {{ Z::op(a, b) }}
         fn viaClass(a: Z, b: Z) -> Z {{ Z::Mag.op(a, b) }}"
    ));
}

/// A bare name in scope beside the class member: the same refusal. This is
/// the case that keeps a library's new `instance` from reinterpreting an
/// existing call.
#[test]
fn a_bare_name_in_scope_beside_a_class_member_is_ambiguous() {
    let e = bad(&format!(
        "{MAG}
         fn op(x: Z, y: Z) -> Z {{ x }}
         fn f(a: Z, b: Z) -> Z {{ a.op(b) }}"
    ));
    assert!(e.contains("both"), "{e}");
}

/// No instance and no dictionary: the layer-2 trace, naming what was
/// consulted — not "unknown name `op`" (design §4 rule 5).
#[test]
fn a_carrier_with_no_instance_reports_the_search() {
    let e = bad(&format!(
        "{MAG}
         inductive W {{ W0 }}
         fn f(a: W, b: W) -> W {{ a.op(b) }}"
    ));
    assert!(e.contains("no instance for"), "{e}");
    assert!(e.contains("Mag<W>"), "{e}");
    assert!(e.contains("scope") || e.contains("no-instance"), "{e}");
}

/// A failed dispatch removes no reading: with a bare `op` in scope and a
/// receiver whose carrier has no instance, the ordinary call still runs
/// (design §4 rule 5). The pair with
/// `a_bare_name_in_scope_beside_a_class_member_is_ambiguous` is the whole
/// rule: the ambiguity is about a *successful* dispatch.
#[test]
fn a_failed_dispatch_falls_back_to_the_bare_reading() {
    ok(&format!(
        "{MAG}
         inductive W {{ W0 }}
         fn op(x: W, y: W) -> W {{ x }}
         theorem f(a: W, b: W) : a.op(b) = a {{ refl }}"
    ));
}

/// A two-parameter class is refused by name rather than mis-dispatched: the
/// receiver fixes the carrier and nothing fixes the rest (design §2.1).
#[test]
fn a_two_parameter_class_member_is_not_dispatched() {
    let e = bad(&format!(
        "{MAG}
         class Act<A, B> {{ act: A -> B -> B }}
         instance Act<Z, Z> {{ fn act(x: Z, y: Z) -> Z {{ y }} }}
         fn f(a: Z, b: Z) -> Z {{ a.act(b) }}"
    ));
    assert!(e.contains("type parameters"), "{e}");
    // The projection spelling is what it points at, and it works.
    ok(&format!(
        "{MAG}
         class Act<A, B> {{ act: A -> B -> B }}
         instance Act<Z, Z> {{ fn act(x: Z, y: Z) -> Z {{ y }} }}
         fn f(a: Z, b: Z) -> Z {{ Z::Act.act(a, b) }}"
    ));
}

/// Modules (design §4 rule 6): a class and its instance are reached from an
/// importing module and are invisible to a module that does not import them —
/// the ordinary §4 regime, not a second visibility rule for dispatch.
#[test]
fn dispatch_sees_exactly_the_classes_a_reference_would() {
    let algebra = "class Mag<A> { op: A -> A -> A }
                   inductive Z { Z0, Z1 }
                   instance Mag<Z> { fn op(x: Z, y: Z) -> Z { y } }";
    run(&[
        ("algebra", algebra),
        ("user", "import algebra;\n theorem f(a: Z, b: Z) : a.op(b) = b { refl }"),
    ])
    .expect("an imported class dispatches");
    // Without the import, `Z` is not visible either — so the receiver itself
    // is what fails, and that is the honest report: nothing about `op` was
    // consulted, because nothing was in scope to consult.
    let Err(e) = run(&[
        ("algebra", algebra),
        ("stranger", "fn f(a: Nat, b: Nat) -> Nat { a.op(b) }"),
    ]) else {
        panic!("an unimported class must not capture a call");
    };
    assert!(e.contains("op"), "{e}");
}

// -- 5: what must not have changed ------------------------------------------

/// The cheap negative test: a `.` call on a name that is nobody's class field
/// is untouched, including the receiver-shaped builtins that no declaration
/// backs. (`shadowed` cannot see them, which is why they are named
/// explicitly in `BUILTIN_METHODS`.)
#[test]
fn ordinary_dot_calls_are_untouched() {
    ok(&format!(
        "{MAG}
         theorem sym_still_works(a: Z, b: Z, p: a = b) : b = a {{ p.sym() }}
         fn map_still_works(xs: [Z; 3]) -> [Z; 3] {{ xs.map(fun (x: Z) => x) }}"
    ));
}

/// A class field named like a builtin makes the builtin call *ambiguous*, not
/// silently the class's — the growth invariant, at the one place `shadowed`
/// could not see.
#[test]
fn a_class_field_named_like_a_builtin_is_ambiguous_not_silent() {
    let e = bad(
        "class Mapper<A> { map: A -> A }
         inductive Z { Z0, Z1 }
         instance Mapper<Z> { fn map(x: Z) -> Z { x } }
         fn f(a: Z) -> Z { a.map() }",
    );
    assert!(e.contains("both"), "{e}");
}

// -- 5: readings that coincide ---------------------------------------------
//
// issues/receiver-dispatch-coinciding-readings.md: rule 2 refuses only
// readings that *differ*. When the dictionary dispatch resolves fills the
// field with the very global the other reading calls, there is one meaning,
// and the call takes the other reading's path — so the emitted term is the
// direct global, byte for byte what it is with no class in scope. Every
// positive below is pinned on the **term**, against the direct spelling in
// an otherwise identical program, not on acceptance alone.

/// A one-field class and a carrier whose own members can fill it by name.
const PICK: &str = r#"
class Pick<A> { pick: A -> A -> A }
inductive Q { Q0, Q1 }
fn Q::pick(self x: Q, y: Q) -> Q { y }
fn Q::other(self x: Q, y: Q) -> Q { x }
"#;

/// The last declaration's binding — statement and body — which is what two
/// programs with one identical prefix are compared on.
fn last(e: &Elaborator) -> heather_kernel::term::GlobalBinding {
    e.psi().bindings.last().expect("a binding").clone()
}

/// The headline: a literal-form instance whose field *is* `Q::pick`, and
/// `a.pick(b)` checks — elaborating to exactly `Q::pick(a, b)`, not to the
/// projection `Q::Pick.pick(a, b)` (the control: the comparison can tell
/// those two apart).
#[test]
fn a_coinciding_literal_instance_emits_the_direct_global() {
    let prefix = format!("{PICK}\ninstance Pick<Q> {{ pick := Q::pick }}\n");
    let dispatched = ok(&format!("{prefix} fn f(a: Q, b: Q) -> Q {{ a.pick(b) }}"));
    let direct = ok(&format!("{prefix} fn f(a: Q, b: Q) -> Q {{ Q::pick(a, b) }}"));
    let projected = ok(&format!("{prefix} fn f(a: Q, b: Q) -> Q {{ Q::Pick.pick(a, b) }}"));
    assert!(last(&dispatched) == last(&direct), "the call is not the direct global");
    assert!(last(&dispatched) != last(&projected), "the control cannot distinguish");
}

/// The same in **checking** positions — a checked argument and an annotated
/// `let`, each against its direct spelling — and a proof whose statement has
/// to convert.
#[test]
fn a_coinciding_call_in_checking_position() {
    let prefix = format!(
        "{PICK}\ninstance Pick<Q> {{ pick := Q::pick }}\n fn snd(x: Q, y: Q) -> Q {{ y }}\n"
    );
    for (dispatched, direct) in [
        (
            "fn g(a: Q, b: Q) -> Q { snd(a, a.pick(b)) }",
            "fn g(a: Q, b: Q) -> Q { snd(a, Q::pick(a, b)) }",
        ),
        (
            "fn g(a: Q, b: Q) -> Q { let c: Q = a.pick(b); c }",
            "fn g(a: Q, b: Q) -> Q { let c: Q = Q::pick(a, b); c }",
        ),
    ] {
        let d = ok(&format!("{prefix} {dispatched}"));
        let e = ok(&format!("{prefix} {direct}"));
        assert!(last(&d) == last(&e), "{dispatched}");
    }
    ok(&format!(
        "{prefix} theorem t(a: Q, b: Q) : a.pick(b) = Q::pick(a, b) {{ refl }}"
    ));
}

/// The bare-name kind of other reading: a top-level `pick` in scope, filling
/// the field by that name.
#[test]
fn a_coinciding_bare_name_in_scope_emits_the_direct_global() {
    let prefix = "class Pick<A> { pick: A -> A -> A }
         inductive Q { Q0, Q1 }
         fn pick(x: Q, y: Q) -> Q { y }
         instance Pick<Q> { pick := pick }\n";
    let dispatched = ok(&format!("{prefix} fn f(a: Q, b: Q) -> Q {{ a.pick(b) }}"));
    let direct = ok(&format!("{prefix} fn f(a: Q, b: Q) -> Q {{ pick(a, b) }}"));
    assert!(last(&dispatched) == last(&direct));
}

/// A **generic** instance at an **open** carrier: `a: L<B>` with `B` a
/// binder. The field is `L::pick` applied to the instance's own type binder
/// and `L::pick`'s subject domain is that same carrier, so both readings
/// solve one equation against `L<B>` (`field_is_global`'s doc) — and the
/// call is `L::pick` at `B`, as written directly.
#[test]
fn a_generic_instance_coincides_at_an_open_carrier() {
    let prefix = "class Pick<A> { pick: A -> A -> A }
         inductive L<A> { N, C(A, L<A>) }
         fn L::pick<A>(self x: L<A>, y: L<A>) -> L<A> { y }
         instance<A> Pick<L<A>> { pick := L::pick }\n";
    let dispatched = ok(&format!("{prefix} fn h<B>(a: L<B>, b: L<B>) -> L<B> {{ a.pick(b) }}"));
    let direct = ok(&format!("{prefix} fn h<B>(a: L<B>, b: L<B>) -> L<B> {{ L::pick(a, b) }}"));
    assert!(last(&dispatched) == last(&direct));
}

/// Negative control for the positive above, **spelling**: the dictionary is a
/// `pair@` and writes no field carrier, so the carrier is read off the
/// instance's declared type — and a subject domain spelled through a
/// type-level function (`LL(A)`, convertible to `L<A>` but not the same
/// pattern) is not one equation with it. Still the rule-2 error.
#[test]
fn a_generic_instance_with_a_respelled_subject_domain_still_refuses() {
    let e = bad("class Pick<A> { pick: A -> A -> A }
         inductive L<A> { N, C(A, L<A>) }
         fn LL(A: Type) -> Type { L<A> }
         fn L::pick<A>(self x: LL(A), y: L<A>) -> L<A> { y }
         instance<A> Pick<L<A>> { pick := L::pick }
         fn h<B>(a: L<B>, b: L<B>) -> L<B> { a.pick(b) }");
    assert!(e.contains("both"), "{e}");
}

/// Negative control, **scope**: a local dictionary is what dispatch resolves
/// (rule 4), and it is a variable — it has no body saying its `pick` is
/// `Q::pick`, and a caller may pass one whose `pick` is `Q::other`. So the
/// registry instance coinciding is beside the point: still the rule-2 error.
#[test]
fn a_local_dictionary_does_not_coincide() {
    let e = bad(&format!(
        "{PICK}
         instance Pick<Q> {{ pick := Q::pick }}
         fn f(d: Pick<Q>, a: Q, b: Q) -> Q {{ a.pick(b) }}"
    ));
    assert!(e.contains("both"), "{e}");
}

/// Negative controls, **registry**: a field filled by another global, and by
/// a λ that merely calls the right one (equal after η, which is not the one
/// local step) — both still the error.
#[test]
fn a_registry_field_that_is_not_the_global_does_not_coincide() {
    let e = bad(&format!(
        "{PICK}
         instance Pick<Q> {{ pick := Q::other }}
         fn f(a: Q, b: Q) -> Q {{ a.pick(b) }}"
    ));
    assert!(e.contains("both"), "{e}");
    let e = bad(&format!(
        "{PICK}
         instance Pick<Q> {{ pick := fun (x: Q) => fun (y: Q) => Q::pick(x, y) }}
         fn f(a: Q, b: Q) -> Q {{ a.pick(b) }}"
    ));
    assert!(e.contains("both"), "{e}");
}

/// Negative control, **argument order**: the same global, but its `self` is
/// its *second* parameter, so the desugaring is `Q::pick(b, a)` where the
/// class reading is the field at `(a, b)` — two calls to one name.
#[test]
fn the_same_global_with_another_subject_slot_does_not_coincide() {
    let e = bad(
        "class Pick<A> { pick: A -> A -> A }
         inductive Q { Q0, Q1 }
         fn Q::pick(y: Q, self x: Q) -> Q { y }
         instance Pick<Q> { pick := Q::pick }
         fn f(a: Q, b: Q) -> Q { a.pick(b) }",
    );
    assert!(e.contains("both"), "{e}");
}

/// Pinned outside the honest rule: a generic instance with a `requires`
/// binder. Its dictionary's arguments are not all type binders, so the
/// field's instantiation is no longer one equation with the desugaring's
/// inference (`field_is_global`'s doc) — the error, as before.
#[test]
fn a_generic_instance_with_requires_binders_still_refuses() {
    let e = bad(
        "class Pick<A> { pick: A -> A -> A }
         inductive L<A> { N, C(A, L<A>) }
         inductive Q { Q0, Q1 }
         instance Pick<Q> { fn pick(x: Q, y: Q) -> Q { y } }
         fn L::pick<A>(self x: L<A>, y: L<A>) -> L<A> { y }
         instance<A> Pick<L<A>> requires pa: Pick<A> { pick := L::pick }
         fn h(a: L<Q>, b: L<Q>) -> L<Q> { a.pick(b) }",
    );
    assert!(e.contains("both"), "{e}");
}

/// The motivating shape is `Cmp`'s: several fields, the coinciding ones not
/// first — `le_dec` is the last of three. Every other positive above has a
/// one-field class, where the first field is also the last, so this pins the
/// spine walk at a middle and a final entry, and a sibling filled by a λ that
/// still refuses on the same instance.
#[test]
fn coincidence_reads_the_right_entry_of_a_multi_field_instance() {
    let prefix = "class Tri<A> { first: A -> A -> A, mid: A -> A -> A, last: A -> A -> A }
         inductive Q { Q0, Q1 }
         fn Q::mid(self x: Q, y: Q) -> Q { y }
         fn Q::last(self x: Q, y: Q) -> Q { x }
         fn Q::first(self x: Q, y: Q) -> Q { y }
         instance Tri<Q> {
             first := fun (x: Q) => fun (y: Q) => x,
             mid := Q::mid,
             last := Q::last,
         }\n";
    for (dispatched, direct) in [
        ("fn f(a: Q, b: Q) -> Q { a.mid(b) }", "fn f(a: Q, b: Q) -> Q { Q::mid(a, b) }"),
        ("fn f(a: Q, b: Q) -> Q { a.last(b) }", "fn f(a: Q, b: Q) -> Q { Q::last(a, b) }"),
    ] {
        let d = ok(&format!("{prefix} {dispatched}"));
        let e = ok(&format!("{prefix} {direct}"));
        assert!(last(&d) == last(&e), "{dispatched}");
    }
    let e = bad(&format!("{prefix} fn f(a: Q, b: Q) -> Q {{ a.first(b) }}"));
    assert!(e.contains("both"), "{e}");
}
