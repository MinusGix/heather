//! An instance may be generic over a **value**
//! (`docs/value-generic-instances-design.md`, `issues/value-generic-instances.md`).
//!
//! `instance(n, m: Nat) Dec<Leq(n, m)>` binds two ordinary value parameters in
//! the head; resolution recovers them by unifying that head against the goal,
//! which is the same route `instance<A> Monoid<List<A>>`'s type parameters
//! already take. Before this, an instance could be generic over types or fixed
//! at an index, and the only registrable decidability instance for an order was
//! at *closed* numerals — the case elaboration-time computation already
//! answered.
//!
//! Per `docs/testing-generated-terms.md` the axes are varied deliberately: an
//! **open** (neutral) carrier and a literal one, an **open element type** in the
//! mixed test, a **checking** position at every use site (`dec_of()` against an
//! expected type), a *composed* goal reached by backchaining rather than by a
//! literal instance, and a negative control beside each positive — including
//! the control that shows the closed instance genuinely cannot serve the open
//! goal.

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

/// The order, stated by recursion into `Type` — the shape `std/nat` gives `Le`,
/// and the reason the carrier is an applied type former rather than a declared
/// type. Curried for the reason `std/nat`'s is: the inner `match` varies both
/// arguments and the guard wants the descending one to pass unchanged.
const KIT: &str = r#"
inductive Bot {}
inductive Top { tt }
fn Neg(P: Type) -> Type { P -> Bot }
inductive Sum<P, Q> { L(p: P), R(q: Q) }
class Dec<P> { d: Sum<P, Neg(P)> }

fn Leq(n: Nat) -> Nat -> Type {
    match n {
        Zero => λ (m: Nat) => Top,
        Succ(k) => λ (m: Nat) => match m { Zero => Bot, Succ(l) => Leq(k)(l) },
    }
}

fn leq_dec(n: Nat) -> (m: Nat) -> Sum<Leq(n, m), Neg(Leq(n, m))> {
    match n as λ z => (m: Nat) -> Sum<Leq(z, m), Neg(Leq(z, m))> {
        Zero => λ m => L(tt),
        Succ(k, ih) => λ m =>
            match m as λ y => Sum<Leq(Succ(k), y), Neg(Leq(Succ(k), y))> {
                Zero => R(λ (bad: Leq(Succ(k), 0)) => bad),
                Succ(m2) => ih(m2),
            },
    }
}

fn dec_of<P: Dec>() -> Sum<P, Neg(P)> { P.d }
"#;

/// The instance this whole round exists for, in the literal body form.
const LEQ_INSTANCE: &str = "instance(n, m: Nat) Dec<Leq(n, m)> { d := leq_dec(n)(m) }\n";

// -- 1: the positive cases -------------------------------------------------

#[test]
fn a_value_generic_instance_registers() {
    ok(&format!("{KIT}{LEQ_INSTANCE}"));
}

#[test]
fn it_resolves_at_an_open_carrier() {
    // The case the round is for, and the one a closed instance cannot serve:
    // `x` and `y` are binders, so the goal is neutral and no amount of
    // elaboration-time computation reaches it. Checking position throughout —
    // `dec_of()` is elaborated against the declared result type.
    ok(&format!(
        r#"{KIT}{LEQ_INSTANCE}
fn open(x, y: Nat) -> Sum<Leq(x, y), Neg(Leq(x, y))> {{ dec_of() }}
"#
    ));
}

#[test]
fn it_resolves_at_a_literal_carrier_and_still_computes() {
    // The literal-scrutinee axis, and the property the "a decider is a `fn`,
    // never a `theorem`" discipline exists to protect: resolving through the
    // class must not cost the reduction. `refl` is the whole assertion —
    // `Leq::Dec.d` unfolds to `leq_dec(1)(2)`, which computes to `L(tt)`.
    ok(&format!(
        r#"{KIT}{LEQ_INSTANCE}
theorem closed(): dec_of<Leq(1, 2)>() = L(tt) {{ refl }}
"#
    ));
}

#[test]
fn a_closed_value_index_reuses_the_parameterized_instance_without_a_mint() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
class Indexed<A>(n: Nat) { value: Nat }
instance(n: Nat) Indexed<Nat>(n) { value := n }
"#,
    )
    .expect("value-indexed instance registers");
    let derived_before = e.derived_instances().len();

    e.elab_source("fn closed_use(d: Indexed<Nat>(2) := infer) -> Nat { d.value }")
        .expect("closed value index resolves");

    assert_eq!(e.derived_instances().len(), derived_before);
}

#[test]
fn a_composed_goal_backchains_through_it() {
    // Not a rename: the connective instance is generic over a *type* and this
    // one over two *values*, and the search composes them at an open carrier.
    // Before this round every such goal died at the `Leq` leaf.
    ok(&format!(
        r#"{KIT}{LEQ_INSTANCE}
instance<P: Dec> Dec<Neg(P)> {{
    d := match P.d {{
        L(p) => R(λ (np: Neg(P)) => np(p)),
        R(np) => L(np),
    }},
}}
fn composed(x, y: Nat) -> Sum<Neg(Leq(x, y)), Neg(Neg(Leq(x, y)))> {{ dec_of() }}
"#
    ));
}

#[test]
fn the_block_body_form_carries_the_binders_too() {
    // The value binders join the telescope of every synthesized declaration,
    // members included — so a member may mention them, and the assembled value
    // still resolves.
    ok(&format!(
        r#"{KIT}
instance(n, m: Nat) Dec<Leq(n, m)> {{
    fn d() -> Sum<Leq(n, m), Neg(Leq(n, m))> {{ leq_dec(n)(m) }}
}}
fn open(x, y: Nat) -> Sum<Leq(x, y), Neg(Leq(x, y))> {{ dec_of() }}
"#
    ));
}

#[test]
fn binders_may_be_written_one_per_annotation() {
    // `(n, m: Nat)` is a run sharing one annotation and `(n: Nat, m: Nat)` is
    // two binders; the head is the same telescope either way.
    ok(&format!(
        r#"{KIT}
instance(n: Nat, m: Nat) Dec<Leq(n, m)> {{ d := leq_dec(n)(m) }}
fn open(x, y: Nat) -> Sum<Leq(x, y), Neg(Leq(x, y))> {{ dec_of() }}
"#
    ));
}

#[test]
fn a_type_parameter_and_a_value_binder_coexist() {
    // The open-element-type axis: the carrier is generic in a type `A` **and**
    // in a value `n`, so both binder lists are live at once, one unification
    // has to recover both, and the telescope's order has to hold — the
    // `requires` subgoal `Dec<A>` backchains on top of it.
    //
    // `Tag(A, n)` is `A` at every `n` and is nonetheless *stuck* at an open one,
    // because the `match` is on `n`: that is what keeps the value binder from
    // being read off by reduction, which is the whole difficulty at a relation
    // like `Leq` and would otherwise be tested away here.
    ok(&format!(
        r#"{KIT}
instance Dec<Bot> {{ d := R(λ (h: Bot) => h) }}
fn Tag(A: Type, n: Nat) -> Type {{ match n {{ Zero => A, Succ(k) => A }} }}
fn tag_val<A>(a: A, n: Nat) -> Tag(A, n) {{
    match n as λ z => Tag(A, z) {{ Zero => a, Succ(k) => a }}
}}
fn tag_neg<A>(f: Neg(A), n: Nat) -> Neg(Tag(A, n)) {{
    match n as λ z => Neg(Tag(A, z)) {{ Zero => f, Succ(k) => f }}
}}
instance<A: Dec>(n: Nat) Dec<Tag(A, n)> {{
    d := match A.d {{ L(p) => L(tag_val<A>(p, n)), R(np) => R(tag_neg<A>(np, n)) }},
}}
fn mixed(k: Nat) -> Sum<Tag(Bot, k), Neg(Tag(Bot, k))> {{ dec_of() }}
"#
    ));
}

// -- 2: the negative controls ----------------------------------------------

#[test]
fn a_closed_instance_cannot_serve_the_open_goal() {
    // The control that says the feature does the work. Exactly the same file
    // with the binders replaced by numerals: `Dec<Leq(2, 5)>` registers happily
    // — the carrier widening landed that — and answers nothing a caller with
    // variables in hand ever asks.
    let e = bad(&format!(
        r#"{KIT}
instance Dec<Leq(2, 5)> {{ d := leq_dec(2)(5) }}
fn open(x, y: Nat) -> Sum<Leq(x, y), Neg(Leq(x, y))> {{ dec_of() }}
"#
    ));
    assert!(e.contains("no instance for"), "unexpected: {e}");
}

#[test]
fn a_type_parameter_absent_from_the_head_is_refused_too() {
    // `issues/instance-binder-occurrence.md`. The rule was stated for value
    // binders and left off type parameters, which was unexamined rather than
    // decided: the two are determined the same way, and a head-absent one is a
    // registry entry no goal can use and every goal must still try.
    let e = bad(&format!(
        r#"{KIT}
instance<Q> Dec<Top> {{ d := L(tt) }}
"#
    ));
    assert!(e.contains("does not occur in the head"), "unexpected: {e}");
}

#[test]
fn a_type_parameter_in_the_index_alone_is_accepted() {
    // The case that makes the rule non-uniform, and the reason it counts the
    // index for a type parameter and not for a value binder: an index argument
    // may be a *global reference at this instance's own type parameters*, and
    // the index is part of the class type, so a goal determines `A` there. A
    // rule that counted class arguments only would refuse this.
    ok(r#"
inductive Bool2 { T, F }
class Mag<A>(op: A -> A -> A) { tag: Nat }
fn pick<A>(x: A, y: A) -> A { x }
instance<A> Mag<Bool2>(pick<A>) { tag := 0 }
"#);
}

#[test]
fn an_index_only_type_parameter_still_resolves() {
    // Accepted *and* reachable — otherwise the exception would be protecting a
    // declaration nobody can use, which is exactly what the rule exists to
    // refuse. The goal names the index, and resolution answers from it.
    ok(r#"
inductive Bool2 { T, F }
class Mag<A>(op: A -> A -> A) { tag: Nat }
fn pick<A>(x: A, y: A) -> A { x }
instance<A> Mag<Bool2>(pick<A>) { tag := 0 }
fn by_resolution(m: Mag<Bool2>(pick<Bool2>) := infer) -> Nat { m.tag }
"#);
}

#[test]
fn a_binder_absent_from_the_head_is_refused() {
    // There is exactly one route by which a value binder is determined, and a
    // binder the head does not mention is a metavariable nothing can solve.
    // Refused where the name to blame is, rather than at some later use site as
    // an uninstantiated implicit.
    let e = bad(&format!(
        r#"{KIT}
instance(k: Nat) Dec<Top> {{ d := L(tt) }}
"#
    ));
    assert!(e.contains("does not occur in the head"), "unexpected: {e}");
}

#[test]
fn a_binder_reaching_only_the_index_is_recovered_from_the_goal() {
    // A generic index has an alpha-stable registry component, while candidate
    // unification recovers the actual value from the goal.
    ok(&format!(
        r#"{KIT}
class Ind<A>(op: A -> A) {{ tag: Nat }}
instance(k: Top -> Top) Ind<Top>(k) {{ tag := 0 }}
fn keep(x: Top) -> Top {{ x }}
fn by_resolution(m: Ind<Top>(keep) := infer) -> Nat {{ m.tag }}
"#
    ));
}

#[test]
fn alpha_renaming_a_generic_index_does_not_create_a_second_slot() {
    let e = bad(&format!(
        r#"{KIT}
class Ind<A>(op: A -> A) {{ tag: Nat }}
instance(k: Top -> Top) Ind<Top>(k) {{ tag := 0 }}
instance(other: Top -> Top) Ind<Top>(other) {{ tag := 1 }}
"#,
    ));
    assert!(e.contains("already has an instance"), "unexpected: {e}");
}

#[test]
fn a_generic_index_cannot_overlap_a_concrete_index() {
    let e = bad(&format!(
        r#"{KIT}
class Ind<A>(op: A -> A) {{ tag: Nat }}
fn keep(x: Top) -> Top {{ x }}
instance(k: Top -> Top) Ind<Top>(k) {{ tag := 0 }}
instance Ind<Top>(keep) {{ tag := 1 }}
"#,
    ));
    assert!(e.contains("overlapping generic-index instance"), "unexpected: {e}");
}

#[test]
fn generic_multi_indices_may_be_disjoint_in_a_concrete_component() {
    ok(&format!(
        r#"{KIT}
class Ind2<A>(op: A -> A, n: Nat) {{ tag: Nat }}
fn keep(x: Top) -> Top {{ x }}
fn drop(x: Top) -> Top {{ tt }}
instance(n: Nat) Ind2<Top>(keep, n) {{ tag := 0 }}
instance(n: Nat) Ind2<Top>(drop, n) {{ tag := 1 }}
fn first(m: Ind2<Top>(keep, 2) := infer) -> Nat {{ m.tag }}
fn second(m: Ind2<Top>(drop, 2) := infer) -> Nat {{ m.tag }}
"#,
    ));
}

#[test]
fn a_duplicate_binder_is_refused() {
    let e = bad(&format!(
        r#"{KIT}
instance(n, n: Nat) Dec<Leq(n, n)> {{ d := leq_dec(n)(n) }}
"#
    ));
    assert!(e.contains("duplicate value binder"), "unexpected: {e}");
}

#[test]
fn a_binder_shadowing_a_type_parameter_is_refused() {
    let e = bad(&format!(
        r#"{KIT}
instance<A>(A: Nat) Dec<Leq(A, A)> {{ d := leq_dec(A)(A) }}
"#
    ));
    assert!(e.contains("already a type parameter"), "unexpected: {e}");
}

#[test]
fn patersons_variable_condition_counts_value_binders() {
    // A subgoal may not mention a value binder more often than the head does,
    // for the reason it may not do so with a type parameter: a search that used
    // this instance could feed itself forever. The size half alone would let
    // this through — `Leq(n, n)` is smaller than `Leq(n, Succ(m))`.
    let e = bad(&format!(
        r#"{KIT}
instance(n, m: Nat) Dec<Leq(n, Succ(m))> requires h: Dec<Leq(n, n)> {{
    d := leq_dec(n)(Succ(m))
}}
"#
    ));
    assert!(e.contains("more often than the head does"), "unexpected: {e}");
}
