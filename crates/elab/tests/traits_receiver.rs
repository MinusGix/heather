//! Receiver dispatch through instances: `x.op(y)`
//! (`docs/traits-receiver-dispatch-design.md`, `issues/traits.md`).
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
/// at a neutral receiver, where nothing computes.
#[test]
fn a_generic_carrier_dispatches_through_its_binder() {
    ok(&format!(
        "{MAG}
         fn twice<A> requires m: Mag<A> (x: A, y: A) -> A {{ x.op(y) }}
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
