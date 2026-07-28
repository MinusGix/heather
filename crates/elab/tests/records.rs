//! Records: named-field Σ sugar and field access
//! (`docs/surface-records.md` §10). Tracking issue: `issues/surface-records.md`.
//!
//! Nothing here touches the kernel. A record is a one-constructor tier-0
//! inductive, so every term below is emitted by the generator that already
//! existed and is re-checked by the real kernel — a wrong projection index or
//! a wrong field permutation shows up as a rejection, not as a wrong answer.
//!
//! Per `docs/testing-generated-terms.md` the suite varies: an **open** field
//! type (inside a polymorphic `fn`), a **checking** position and not only
//! computation, a **neutral** receiver and not only a literal, and negative
//! controls.

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

/// The running example of `issues/surface-records.md`: a record of generic
/// operations, including a **dependent** law field whose type mentions two
/// earlier fields. Used at `Nat` so the laws are provable by `refl`.
const MONOID: &str = r#"
record Monoid<A> {
    unit: A,
    op: A -> A -> A,
    unit_l: (x: A) -> op(unit)(x) = x,
}
"#;

const NAT_MONOID: &str = r#"
fn nat_monoid() -> Monoid<Nat> {
    Monoid {
        unit: 0,
        op: λ (x: Nat) => λ (y: Nat) => y,
        unit_l: λ (x: Nat) => refl,
    }
}
"#;

// -- 1-2: declaration, and a dependent field ------------------------------

// §10.1/§10.2. The declaration checks, and `unit_l` — whose type mentions
// `unit` and `op` — is what makes the field spine a Σ rather than a product.
#[test]
fn a_record_with_a_dependent_field_declares() {
    ok(&format!("{MONOID}{NAT_MONOID}"));
}

// The dependent field's type is the *receiver's own* projections substituted
// in, which is what §4.3 says comes free from the Σ tail. Observed by feeding
// `m.unit_l` to a function whose parameter type spells that out at a neutral
// `m`: if the substitution were wrong the kernel would reject the call.
#[test]
fn a_dependent_field_type_mentions_the_receivers_own_fields() {
    ok(&format!(
        r#"
        {MONOID}
        fn use_law<A>(m: Monoid<A>, law: (x: A) -> m.op(m.unit)(x) = x, y: A) -> A {{
            m.op(m.unit)(y)
        }}
        fn apply_it<A>(m: Monoid<A>, y: A) -> A {{ use_law(m, m.unit_l, y) }}
        "#
    ));
}

// -- 3-4: computation and field order --------------------------------------

// §10.3. Projection out of a literal β-reduces to the field, definitionally.
#[test]
fn projection_out_of_a_literal_computes() {
    ok(&format!(
        r#"
        {MONOID}{NAT_MONOID}
        theorem unit_is_zero(): nat_monoid().unit = 0 {{ refl }}
        theorem op_computes(): nat_monoid().op(3)(4) = 4 {{ refl }}
        "#
    ));
}

// §10.4. Field order in a literal is free, and the two permutations are the
// same term — checked by `refl`, i.e. by kernel conversion.
#[test]
fn literal_field_order_is_free() {
    ok(r#"
        record P { x: Nat, y: Nat }
        fn a() -> P { P { x: 0, y: 1 } }
        fn b() -> P { P { y: 1, x: 0 } }
        theorem same(): a() = b() { refl }
        "#);
}

// -- 5: literal diagnostics ------------------------------------------------

#[test]
fn a_missing_field_is_rejected() {
    let e = bad("record P { x: Nat, y: Nat }
                 fn f() -> P { P { x: 0 } }");
    assert!(e.contains("missing field"), "{e}");
    assert!(e.contains('y'), "{e}");
}

#[test]
fn an_unknown_field_is_rejected() {
    let e = bad("record P { x: Nat }
                 fn f() -> P { P { x: 0, z: 1 } }");
    assert!(e.contains("no field `z`"), "{e}");
    // The message lists what the record does have.
    assert!(e.contains('x'), "{e}");
}

#[test]
fn a_field_given_twice_is_rejected() {
    let e = bad("record P { x: Nat }
                 fn f() -> P { P { x: 0, x: 1 } }");
    assert!(e.contains("twice"), "{e}");
}

#[test]
fn a_duplicate_field_name_in_the_declaration_is_rejected() {
    let e = bad("record P { x: Nat, x: Nat }");
    assert!(e.contains("duplicate field"), "{e}");
}

// -- 6: η, the load-bearing test -------------------------------------------

// §10.6. `P { x: p.x, y: p.y } = p` at a **neutral** `p`, by `refl`. This is
// Σ-η and `Unit`-η through the nominal tag at once: the reconstruction is
// `pair tag (pair (fst (snd p)) (pair … ⟨⟩))`, and it converts with `p` only
// because the tag component is proof-irrelevant (tier-0 §3.3) and the trailing
// `Unit` is invisible. If either η were missing this is where it shows.
#[test]
fn a_record_is_eta_equal_to_its_projections() {
    ok(r#"
        record P { x: Nat, y: Nat }
        theorem eta(p: P): (P { x: p.x, y: p.y }) = p { refl }
        "#);
}

// The same at a record with a *dependent* field, since that is the case where
// the reconstruction's Σ tail is not constant.
#[test]
fn eta_holds_with_a_dependent_field() {
    ok(&format!(
        r#"
        {MONOID}
        theorem eta<A>(m: Monoid<A>): (Monoid {{ unit: m.unit, op: m.op, unit_l: m.unit_l }}) = m {{
            refl
        }}
        "#
    ));
}

// -- 7: destructuring ------------------------------------------------------

// §10.7. `let { … }` and `match` produce convertible terms at a neutral
// receiver — which they must, since both are the same projections.
#[test]
fn destructuring_and_match_agree() {
    ok(r#"
        record P { x: Nat, y: Nat }
        fn add(a: Nat, b: Nat) -> Nat { match a { Zero => b, Succ(k) => Succ(add(k, b)) } }
        fn by_let(p: P) -> Nat { let { x, y } = p; add(x, y) }
        fn by_match(p: P) -> Nat { match p { P(x, y) => add(x, y) } }
        fn by_proj(p: P) -> Nat { add(p.x, p.y) }
        theorem all_three(p: P): by_let(p) = by_match(p) { refl }
        theorem and_proj(p: P): by_let(p) = by_proj(p) { refl }
        "#);
}

// A partial pattern binds fewer fields and is not an error (§5).
#[test]
fn a_partial_pattern_binds_fewer_fields() {
    ok("record P { x: Nat, y: Nat }
        fn f(p: P) -> Nat { let { y } = p; y }");
}

#[test]
fn a_pattern_field_that_does_not_exist_is_rejected() {
    let e = bad("record P { x: Nat }
                 fn f(p: P) -> Nat { let { z } = p; z }");
    assert!(e.contains("no field `z`"), "{e}");
}

#[test]
fn a_pattern_needs_a_record() {
    let e = bad("fn f(n: Nat) -> Nat { let { x } = n; x }");
    assert!(e.contains("needs a record"), "{e}");
}

// -- 8: open instantiation -------------------------------------------------

// §10.8, and the reason records wait on polymorphism: the record is
// instantiated at an **open** type inside a polymorphic `fn`, projected, and
// applied. Axis 2 of docs/testing-generated-terms.md — a closed instantiation
// makes the type-parameter weakening a no-op and hides a shift bug.
#[test]
fn a_record_at_an_open_instantiation_projects_and_applies() {
    ok(&format!(
        r#"
        {MONOID}{NAT_MONOID}
        fn twice<A>(m: Monoid<A>, x: A) -> A {{ m.op(m.op(x)(x))(x) }}
        theorem computes(): twice(nat_monoid(), 5) = 5 {{ refl }}
        "#
    ));
}

// The open case with a *non-function* field too, so the projection is not
// masked by the application that follows it.
#[test]
fn a_field_at_an_open_type_is_returned_directly() {
    ok(&format!(
        r#"
        {MONOID}{NAT_MONOID}
        fn unit_of<A>(m: Monoid<A>) -> A {{ m.unit }}
        theorem computes(): unit_of(nat_monoid()) = 0 {{ refl }}
        "#
    ));
}

// -- 9: checking position --------------------------------------------------

// §10.9. The literal carries no annotation and no type arguments: the
// expected type from the `fn`'s result supplies the instantiation. This is
// axis 3 — a *checking* position, not only computation.
#[test]
fn a_literal_checks_against_an_expected_type_with_no_annotation() {
    ok(r#"
        record Box<A> { val: A }
        fn boxed() -> Box<Nat> { Box { val: 3 } }
        theorem got(): boxed().val = 3 { refl }
        "#);
}

// …and the same literal as an *argument*, where the expected type comes from
// the callee's parameter rather than from a return type.
#[test]
fn a_literal_checks_in_argument_position() {
    ok(r#"
        record Box<A> { val: A }
        fn unbox<A>(b: Box<A>) -> A { b.val }
        theorem got(): unbox(Box { val: 3 }) = 3 { refl }
        "#);
}

// Explicit type arguments on the literal, for when inference cannot see the
// instantiation (§6).
#[test]
fn a_literal_may_spell_its_type_arguments() {
    ok(r#"
        record Box<A> { val: A }
        fn f() -> Nat { Box<Nat> { val: 3 }.val }
        "#);
}

// -- 10: the `.` decision --------------------------------------------------

// §10.10, the test that pins §4.2. `m.op(x, y)` must be `(m.op)(x, y)` — the
// projection applied — and **not** the old parser desugaring `op(x, y, m)`.
// Observed without reading terms: a global `op` is in scope with a different
// result, so the two readings disagree on the answer.
#[test]
fn a_field_call_applies_the_projection_not_a_global() {
    ok(r#"
        record Pair { fst: Nat -> Nat }
        // A global with the same name as the field, returning something else.
        fn fst(f: Nat -> Nat, p: Pair) -> Nat { 1 }
        fn use_field(p: Pair, n: Nat) -> Nat { p.fst(n) }
        theorem it_is_the_projection():
            use_field(Pair { fst: λ (x: Nat) => x }, 7) = 7 { refl }
        "#);
}

// -- 11: field beats global ------------------------------------------------

// §10.11. A record whose field is named `sym`, in a file where the prelude's
// polymorphic `sym` is in scope. The field wins; the global stays reachable
// under its own name at any other receiver.
#[test]
fn a_field_shadows_a_global_of_the_same_name_at_that_receiver() {
    ok(r#"
        record Weird { sym: Nat }
        fn field_wins(w: Weird) -> Nat { w.sym }
        theorem it_is_the_field(): field_wins(Weird { sym: 4 }) = 4 { refl }
        // …and the global is untouched at a receiver that is not a `Weird`.
        theorem global_still_works(a: Nat, b: Nat, p: a = b): b = a { p.sym() }
        "#);
}

// -- 12: regression, the method suite --------------------------------------

// §10.12. The whole point of §4.5: moving `.` into the elaborator must be
// invisible to every use that predates records. The dedicated suites
// (operators, goal_holes, inductive_tier0, constructor_values, container_*)
// cover these in depth and all still pass; this is the concentrated version,
// so a regression is visible in *this* file rather than only elsewhere.
#[test]
fn the_method_desugaring_still_works() {
    ok(r#"
        inductive Opt { None, Some(v: Nat) }

        // `.sym()` / `.trans()` — prelude lemmas with implicit endpoints
        // inferred from the receiver. Insertion is name-directed, so it works
        // wherever the receiver lands.
        theorem sym_method(a: Nat, b: Nat, p: a = b): b = a { p.sym() }
        // The receiver fills the subject parameter, which defaults to the
        // first: `p.trans(q)` is `trans(p, q)` and reads forward. This is the
        // inversion this file first wrote down (§11.3), fixed by
        // `issues/method-receiver-position.md`.
        theorem trans_method(a: Nat, b: Nat, c: Nat, p: a = b, q: b = c): a = c {
            p.trans(q)
        }

        // `.inj(k)` / `.absurd()` — the tier-0 derived lemmas, and `absurd`
        // is checking-only, so it exercises the fallback in checking mode.
        theorem inj_method(a: Nat, b: Nat, p: Some(a) = Some(b)): a = b { p.inj(0) }
        theorem absurd_method(a: Nat, p: Some(a) = None): 0 = 1 { p.absurd() }

        // `.cong(f)` over an arbitrary function — the deferred spelling that
        // `docs/constructor-function-values.md` closed — and `calc`, whose
        // desugaring builds an explicit `@trans` spine. `cong` is not in the
        // prelude (its function argument is not inferable from the proof), so
        // it is declared here, as the function-types suite does.
        theorem cong(f: Nat -> Nat, {a: Nat}, {b: Nat}, self p: a = b): f(a) = f(b) {
            j(p, λ y q => f(a) = f(y), refl)
        }
        theorem cong_method(a: Nat, b: Nat, p: a = b): Succ(a) = Succ(b) {
            p.cong(Succ)
        }
        theorem calc_still_chains(a: Nat, b: Nat, c: Nat, p: a = b, q: b = c): a = c {
            calc { a = b := p, = c := q }
        }
        "#);
}

// The vector eliminators arrive through the same fallback (`xs.map(f)` ⇒
// `map(xs, f)`), and they are *built-in* rather than global, so they take a
// different path out of it.
#[test]
fn the_vector_methods_still_work() {
    ok(r#"
        fn add(a: Nat, b: Nat) -> Nat { match a { Zero => b, Succ(k) => Succ(add(k, b)) } }
        fn doubled(xs: [Nat; 2]) -> [Nat; 2] { xs.map(λ (x: Nat) => add(x, x)) }
        theorem computes(): doubled([1, 2]) = [2, 4] { refl }
        "#);
}

// -- 13: no such field -----------------------------------------------------

// §10.13. A bare `p.f` is never a method call, so there is nothing to fall
// back to; the message names the receiver's actual type, since the usual
// mistake is a receiver that is not the record the writer meant.
#[test]
fn a_bare_projection_on_a_non_record_is_rejected() {
    let e = bad("fn f(n: Nat) -> Nat { n.x }");
    assert!(e.contains("not a record"), "{e}");
}

#[test]
fn a_bare_projection_at_the_wrong_record_names_it() {
    let e = bad("record P { x: Nat }
                 record Q { y: Nat }
                 fn f(q: Q) -> Nat { q.x }");
    assert!(e.contains("`Q` has no field `x`"), "{e}");
}

// -- 14: negative control, recursion ---------------------------------------

// §10.14. A `record` is tier 0 by construction; a recursive one is an
// `inductive`, and the message says so rather than silently lowering onto
// `Wf` where the field names would still project.
#[test]
fn a_recursive_record_is_rejected_and_points_at_inductive() {
    let e = bad("record R { head: Nat, tail: R }");
    assert!(e.contains("mentions itself"), "{e}");
    assert!(e.contains("inductive"), "{e}");
}

// -- 15: the nominal tag at n = 1 ------------------------------------------

// §10.15. Two structurally identical records must not share a kernel type.
// At one constructor the nominal tag is the *only* thing distinguishing them
// (tier-0 §3.3), so this is where its absence would show.
#[test]
fn structurally_identical_records_are_distinct_types() {
    let e = bad(r#"
        record Monoidish { unit: Nat }
        record Semigroupish { unit: Nat }
        fn a() -> Monoidish { Monoidish { unit: 0 } }
        fn b() -> Semigroupish { Semigroupish { unit: 0 } }
        theorem confused(): a() = b() { refl }
        "#);
    // Rejected by the kernel's structural type conversion, not by a surface
    // check — which is the point of the tag.
    assert!(!e.is_empty(), "{e}");
}

// -- 16: injectivity, inherited restrictions and all -----------------------

// §10.16. `inj` at a *non-dependent* field of a record fires, since a record
// is a one-constructor inductive and nothing about the derivation changed.
#[test]
fn injectivity_fires_at_a_non_dependent_field() {
    ok(r#"
        record P { x: Nat, y: Nat }
        theorem inj_x(a: Nat, b: Nat, c: Nat, d: Nat,
                      p: (P { x: a, y: c }) = (P { x: b, y: d })): a = b {
            p.inj(0)
        }
        "#);
}

// …and is **diagnosed** at a dependent one: the derivation is at a constant
// motive, which is exactly what a dependent field type is not
// (issues/dependent-field-injectivity.md). For a record this is the normal
// case, not the exotic one, so it will be met — hence pinned rather than
// rediscovered.
#[test]
fn injectivity_at_a_dependent_field_is_diagnosed() {
    let e = bad(r#"
        record Dep { n: Nat, p: n = n }
        theorem inj_dep(a: Nat, b: Nat, pa: a = a, pb: b = b,
                        e: (Dep { n: a, p: pa }) = (Dep { n: b, p: pb })): pa = pb {
            e.inj(1)
        }
        "#);
    assert!(e.contains("depend"), "{e}");
}

// -- 17: the level rule ----------------------------------------------------

// §10.17 / §3. The rule is `level(record) = ⊔ level(fieldᵢ)`, which the Σ
// spine already computes. Today every writable record joins to 0, because
// `TyKind` has no way to spell `Type` and parameters are monomorphized — so
// this asserts the *computation* rather than a literal, and is the test that
// fires when a `Type`-valued field arrives.
//
// A record instantiated at a record instantiated at `Nat` still lands at 0,
// and a `theorem` about it typechecks at level 0; if the join were hardcoded
// somewhere above the spine, a nested instantiation is where it would drift.
#[test]
fn a_records_level_is_the_join_of_its_fields() {
    ok(r#"
        record Inner { a: Nat }
        record Outer { i: Inner, b: Nat }
        fn nested() -> Outer { Outer { i: Inner { a: 1 }, b: 2 } }
        theorem reaches_in(): nested().i.a = 1 { refl }
        "#);
}

// -- extras: the surface's own edges ---------------------------------------

// An `inductive` is not a record: its field names are positional, not
// accessors, so neither the literal nor the projection is available.
#[test]
fn an_inductive_is_not_a_record() {
    let lit = bad("inductive I { Mk(x: Nat) }
                   fn f() -> I { I { x: 0 } }");
    assert!(lit.contains("is an `inductive`"), "{lit}");

    let proj = bad("inductive I { Mk(x: Nat) }
                    fn f(i: I) -> Nat { i.x }");
    assert!(proj.contains("not a record"), "{proj}");
}

// A record's constructor is a real constructor (§2.1), so everything an
// inductive's constructor can do it can do — including being a function value
// (docs/constructor-function-values.md).
#[test]
fn a_records_constructor_is_an_ordinary_constructor() {
    ok(r#"
        record Box<A> { val: A }
        fn ap<A, B>(f: A -> B, x: A) -> B { f(x) }
        fn positional() -> Box<Nat> { Box(3) }
        // A constructor as a function *value*, in checking position — the
        // half `docs/constructor-function-values.md` §2 landed. (A *bare*
        // unsaturated constructor in inference position is still open there,
        // which is why the result is annotated by `boxed`'s return type
        // rather than projected straight out of the call.)
        fn mk() -> Nat -> Box<Nat> { Box }
        fn boxed() -> Box<Nat> { mk()(3) }
        theorem as_a_value(): boxed().val = 3 { refl }
        theorem positional_agrees(): positional() = (Box { val: 3 }) { refl }
        "#);
}

// Chained projection, and a projection as a receiver for a method — the two
// ways `.` now composes with itself.
#[test]
fn projections_chain_and_compose_with_methods() {
    ok(r#"
        record Inner { a: Nat }
        record Outer { i: Inner }
        fn deep(o: Outer) -> Nat { o.i.a }
        theorem chains(): deep(Outer { i: Inner { a: 7 } }) = 7 { refl }
        theorem method_on_a_projection(o: Outer, p: o.i.a = 3): 3 = o.i.a { p.sym() }
        "#);
}
