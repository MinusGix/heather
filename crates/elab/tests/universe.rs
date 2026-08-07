//! The surface universe: `Type<n>` in type and term position
//! (`docs/surface-universe.md` §11). Tracking issue: `issues/surface-universe.md`.
//!
//! Nothing here touches the kernel — `Type::Ty(l)` at level `l + 1` and its
//! code `TmTy(l)` have both been there since v0 (`typing.rs:457-460,756-759`).
//! Every term below is re-checked by the real kernel, so a wrong level is a
//! rejection rather than a wrong answer.
//!
//! Per `docs/testing-generated-terms.md` the suite varies: an **open** type (a
//! `Type`-valued binder, used before it can possibly be known), a **checking**
//! position and not only computation, a **neutral** as well as a literal
//! spelling, and negative controls — including the one this round exists to
//! make possible, a level mismatch under non-cumulativity.

use heather_elab::Elaborator;

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(src),
    }
}

// -- 1-2: the form parses, in both positions ------------------------------

// §11.1. `Type` in a parameter's type, which is the position the whole round
// exists for: a binder ranging over a universe.
#[test]
fn a_type_valued_parameter_declares() {
    ok("fn id_at(A: Type, x: A) -> A { x }");
}

// §11.1. `Type<n>` under every type former that can contain a type.
#[test]
fn a_universe_parses_in_every_type_position() {
    ok("fn f(A: Type<0>, g: Type<0> -> Type<0>) -> Type<0> { g(A) }");
    ok("fn h(A: Type<1>) -> Type<1> { A }");
    ok("fn dep(A: Type, k: (B: Type) -> Type) -> Type { k(A) }");
}

// -- 3: the hierarchy is real ---------------------------------------------

// §11.2. `Type<n> : Type<n+1>`, kernel-verified: the *value* `Type<0>` checks
// against the *type* `Type<1>`, and against nothing else (see the negative
// control in `a_level_mismatch_is_rejected`).
#[test]
fn a_universe_inhabits_the_next_universe_up() {
    ok("fn u0() -> Type<1> { Type<0> }");
    ok("fn u1() -> Type<2> { Type<1> }");
    ok("fn nat_is_a_type() -> Type<0> { Nat }");
}

// -- 4-5: the Expr/Ty bridge ----------------------------------------------

// §11.3. A type written where a term is expected, then used: `id_at(Nat, 3)`
// computes. This is the coercion `docs/surface-polymorphism.md` §5 retired,
// restored with a customer (docs/surface-universe.md §4).
#[test]
fn a_type_argument_passes_and_computes() {
    ok("fn id_at(A: Type, x: A) -> A { x }\nfn three() -> Nat { id_at(Nat, 3) }");
}

// §11.3, the **open** case: the argument is not a literal type but a binder
// still in the telescope, so `El` is the identity on it and the bridge has to
// quote back the variable itself rather than a code it built.
#[test]
fn a_type_valued_binder_passes_as_a_type_argument() {
    ok("fn id_at(A: Type, x: A) -> A { x }\n\
        fn twice(B: Type, y: B) -> B { id_at(B, id_at(B, y)) }");
}

// An applied type reaches the bridge too — `TyApp` is the one expression form
// that already carries type arguments.
#[test]
fn an_applied_type_passes_as_a_type_argument() {
    ok("inductive Opt<T> { None, Some(T) }\n\
        fn id_at(A: Type, x: A) -> A { x }\n\
        fn f(o: Opt<Nat>) -> Opt<Nat> { id_at(Opt<Nat>, o) }");
}

// -- 6: `<A: Type<n>>` ----------------------------------------------------

// §2's spelling decision: the sugar can say what its desugaring says, and an
// unannotated `<A>` still means `Type<0>`.
#[test]
fn a_type_parameter_can_annotate_its_universe() {
    ok("fn id<A>(x: A) -> A { x }");
    ok("fn id0<A: Type<0>>(x: A) -> A { x }");
    ok("fn id1<A: Type<1>>(x: A) -> A { x }");
}

// The annotated and unannotated forms are the *same* declaration, so a call
// infers its type argument either way.
#[test]
fn an_annotated_type_parameter_still_infers_at_a_call() {
    ok("fn id0<A: Type<0>>(x: A) -> A { x }\nfn use_it() -> Nat { id0(3) }");
}

// -- 7: nothing that used to work stopped ---------------------------------

// The round's flagged regression surface, which turned out not to exist. The
// `Ty l` arm carried a message for the pre-`<…>` spelling `@f(Nat, x)`, but
// that spelling never reached it: `@` does not make type parameters
// positional, so `Nat` lands at the *value* parameter's type and the arm is
// not consulted. Verified against a clean tree — `unbound name `Nat`` is what
// this produced before this round too, which is precisely what the arm's own
// comment predicted would happen *if the arm were removed*.
//
// So the behaviour to hold is the pre-existing one, not the message.
#[test]
fn an_at_call_with_a_positional_type_argument_is_still_rejected() {
    let e = bad("fn id<A>(x: A) -> A { x }\nfn f() -> Nat { @id(Nat, 3) }");
    assert!(e.contains("Nat"), "expected the argument to be reported, got: {e}");
}

// -- 8-10: the bundled record ---------------------------------------------

/// The case `docs/surface-records.md` §3 named as waiting on this round: a
/// record whose *first field is a type* and whose later fields are at it. It
/// is what makes the record land above level 0 for the first time, so the Σ
/// spine's join stops being vacuous.
const MON: &str = "record Mon {
    carrier: Type,
    unit: carrier,
    op: carrier -> carrier -> carrier,
}
";

const NAT_MON: &str = "fn nat_mon() -> Mon {
    Mon { carrier: Nat, unit: 0, op: λ (x: Nat) => λ (y: Nat) => y }
}
";

// §11.4. It declares, and the later fields really are typed by the earlier
// one — a field at a universe is a type name for the fields after it.
#[test]
fn a_bundled_record_declares() {
    ok(MON);
}

// §11.5. And it constructs: the literal's `carrier` field is a *type* in a
// term position, so the bridge runs inside a record literal too.
#[test]
fn a_bundled_record_constructs() {
    ok(&format!("{MON}{NAT_MON}"));
}

// §11.5, projection — both from a literal and from a **neutral** receiver,
// where `m.carrier` has to work *as a type* (the decoded-expression form).
#[test]
fn a_bundled_record_projects() {
    ok(&format!("{MON}{NAT_MON}fn u() -> Nat {{ nat_mon().unit }}"));
    ok(&format!("{MON}fn u(m: Mon) -> m.carrier {{ m.unit }}"));
}

// A decoded type is a real type: it is `El` of a code, so it converts with the
// type it decodes to rather than merely looking like it.
#[test]
fn a_decoded_type_converts_with_the_type_it_decodes_to() {
    ok(&format!("{MON}{NAT_MON}fn u() -> nat_mon().carrier {{ 0 }}"));
}

// The level really moved: a `Type`-valued field puts the record above 0, and
// a field's type can be read back out at `Type<0>`.
#[test]
fn a_type_valued_field_reads_back_as_a_type() {
    ok(&format!("{MON}fn c(m: Mon) -> Type<0> {{ m.carrier }}"));
}

// -- 11-15: negative controls ---------------------------------------------

// Non-cumulativity inside a record literal: a `Type<1>` where the field is at
// `Type<0>`.
#[test]
fn a_level_mismatch_in_a_record_field_is_rejected() {
    let e = bad(&format!(
        "{MON}fn bad() -> Mon {{ Mon {{ carrier: Type<0>, unit: 0, \
         op: λ (x: Nat) => λ (y: Nat) => y }} }}"
    ));
    assert!(e.contains("non-cumulative"), "expected the non-cumulativity message, got: {e}");
}

// A term that is not at a universe is not a type. Written as a *projection*
// because a bare name in type position is still `TyKind::Named` and keeps its
// own older message ("unknown type `x`") — only a compound expression reaches
// the decoded-type path.
#[test]
fn a_non_universe_expression_in_type_position_is_rejected() {
    let e = bad(&format!("{MON}fn f(m: Mon) -> m.unit {{ m.unit }}"));
    assert!(e.contains("not a type"), "expected the not-a-type message, got: {e}");
}

// The control this round exists to make reachable. Non-cumulativity is
// deliberate (DeLaM ch. 04 §Non-cumulativity, `conv.rs:291` comparing by `≈`),
// so a `Type<0>` does **not** inhabit `Type<1>` and there is no lift.
#[test]
fn a_level_mismatch_is_rejected() {
    let e = bad("fn f() -> Type<2> { Type<0> }");
    assert!(
        e.contains("non-cumulative") || e.contains("level"),
        "expected a level/non-cumulativity message, got: {e}"
    );
}

// A level variable is `UPi`, layer m (docs/surface-universe.md §7). Rejected
// at the *parser*, so the message can say why rather than reporting an
// unbound name.
#[test]
fn a_level_variable_is_rejected() {
    let e = bad("fn f<A: Type<l>>(x: A) -> A { x }");
    assert!(e.contains("numeral"), "expected the numeral message, got: {e}");
}

// Joins are computed, never written.
#[test]
fn a_level_expression_is_rejected() {
    let e = bad("fn f(A: Type<0>) -> Type<1> { A }");
    assert!(!e.is_empty());
    let e = bad("fn g() -> Type<n> { Nat }");
    assert!(e.contains("numeral"), "expected the numeral message, got: {e}");
}

// A type parameter's annotation is a *universe* or a *class*, never any other
// type: `<A: Nat>` is not a stricter bound, it is a category error. Since the
// inline constraint form landed (issues/requires-placement-syntax.md §R2-A)
// the colon carries two nouns, so the rejection names both readings rather
// than only the universe one.
#[test]
fn a_non_universe_type_parameter_annotation_is_rejected() {
    let e = bad("fn f<A: Nat>(x: A) -> A { x }");
    assert!(e.contains("UNIVERSE"), "expected the universe reading, got: {e}");
    assert!(e.contains("is not a class"), "expected the class reading, got: {e}");
}

// A term where a type is expected still fails, and the bridge does not
// silently accept it.
#[test]
fn a_non_type_expression_at_a_universe_is_rejected() {
    let e = bad("fn id_at(A: Type, x: A) -> A { x }\nfn f() -> Nat { id_at(3, 3) }");
    assert!(!e.is_empty());
}
