//! An instance may be keyed at a **type former**, not only at a declared type
//! (`docs/decide-class-design.md` §2, `issues/decide-class.md`).
//!
//! The carrier a decidability class is *for* is a proposition stated by
//! recursion into `Type` — `Le(n, m)`, `Not(P)` — and such a carrier reaches
//! the elaborator as an ordinary application whose head is a `fn`. Two
//! declaration-time guards refused it: `head_name` had no case for the syntax,
//! and `names_a_type` wanted a declared inductive. Neither guard was protecting
//! resolution, which never consults the carrier head at all.
//!
//! Per `docs/testing-generated-terms.md` the axes are varied deliberately: an
//! **open** carrier (`Neg(P)` at a type parameter, not only `Neg(Bot)`), a
//! **checking** position (the use site elaborates `dec_of()` against an
//! expected type), a composed/**neutral** goal reached by backchaining rather
//! than by a literal instance, and a **negative control** beside each positive
//! — including a non-nominal endpoint type that is still refused on purpose.

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

/// Negation as a `fn` into `Type` — the shape `std/logic` gives `¬`, so that
/// `¬P` stays definitionally `P -> Bot` and needs no unwrapping. That choice is
/// exactly what made it unreachable as a carrier before the widening.
const LOGIC: &str = r#"
inductive Bot {}
fn Neg(P: Type) -> Type { P -> Bot }
inductive Sum<P, Q> { L(p: P), R(q: Q) }
class Dec<P> { d: Sum<P, Neg(P)> }

instance Dec<Bot> { d := R(λ (h: Bot) => h) }
"#;

/// The generic instance at an **open** carrier built from a type former, and
/// the one the whole widening exists for.
const NEG_INSTANCE: &str = r#"
instance<P: Dec> Dec<Neg(P)> {
    d := match P.d {
        L(p) => R(λ (np: Neg(P)) => np(p)),
        R(np) => L(np),
    },
}
"#;

// -- 1: the positive cases -------------------------------------------------

#[test]
fn an_instance_may_be_keyed_at_a_type_former() {
    // `Neg` is a `fn`, so before the widening this reported that `Neg` is not a
    // type in scope and `Neg::Dec` attaches to nothing.
    ok(&format!("{LOGIC}{NEG_INSTANCE}"));
}

#[test]
fn a_type_former_instance_is_found_by_resolution() {
    // The checking-position axis: `dec_of()` is elaborated against an expected
    // type, and the answer has to come from the registry rather than from a
    // binder in scope. `Neg(Bot)` is the *composed* goal — it resolves only by
    // backchaining through the generic instance to `Dec<Bot>`.
    ok(&format!(
        r#"{LOGIC}{NEG_INSTANCE}
fn dec_of<P: Dec>() -> Sum<P, Neg(P)> {{ P.d }}
fn use_it() -> Sum<Neg(Bot), Neg(Neg(Bot))> {{ dec_of() }}
"#
    ));
}

#[test]
fn a_type_former_carrier_backchains_through_itself() {
    // Two levels deep, so the instance is genuinely re-entered rather than
    // matched once: `Neg(Neg(Bot))` needs `Neg(Bot)` needs `Bot`.
    ok(&format!(
        r#"{LOGIC}{NEG_INSTANCE}
fn dec_of<P: Dec>() -> Sum<P, Neg(P)> {{ P.d }}
fn deep() -> Sum<Neg(Neg(Bot)), Neg(Neg(Neg(Bot)))> {{ dec_of() }}
"#
    ));
}

#[test]
fn a_type_former_owns_a_member_namespace() {
    // The owner rule was widened at the *member declaration* check rather than
    // only on the instance path, so this is the same widening observed where it
    // actually lives. An instance's canonical name is an ordinary member
    // declaration and this keeps it one.
    ok(&format!(
        r#"{LOGIC}
fn Neg::tag() -> Nat {{ 0 }}
"#
    ));
}

// -- 2: the negative controls ----------------------------------------------

#[test]
fn equality_instances_are_owned_by_the_endpoints_type() {
    // Equality has no surface head, but its endpoints do. Nat and Bit use two
    // resolved carrier keys and therefore coexist; before the equality-carrier
    // round the first declaration stopped at "no head type name".
    ok(&format!(
        r#"{LOGIC}
inductive Bit {{ Off }}
instance Dec<Nat> {{ d := L(0) }}
instance Dec<2 = 2> {{ d := L(refl) }}
instance Dec<Off = Off> {{ d := L(refl) }}
fn dec_of<P: Dec>() -> Sum<P, Neg(P)> {{ P.d }}
fn nat_value() -> Sum<Nat, Neg(Nat)> {{ dec_of() }}
fn nat_eq() -> Sum<2 = 2, Neg(2 = 2)> {{ dec_of() }}
fn bit_eq() -> Sum<Off = Off, Neg(Off = Off)> {{ dec_of() }}
"#
    ));
}

#[test]
fn equality_at_a_non_nominal_endpoint_type_is_refused() {
    // A function type has no one resolved owner to key under. A dictionary in
    // scope remains the spelling for equality at a non-nominal carrier; global
    // registration is per nominal endpoint type.
    let e = bad(&format!(
        r#"{LOGIC}
instance(f, g: Nat -> Nat) Dec<f = g> {{ d := R(λ (bad: f = g) => bad) }}
"#
    ));
    assert!(e.contains("endpoints at a type with no nominal owner"), "unexpected: {e}");
}

#[test]
fn a_head_that_is_not_a_type_former_is_refused() {
    // The widening admits type *formers*, not any global: `twice` returns `Nat`,
    // so `twice::Dec` would not be a sentence. This is what keeps the canonical
    // name meaning what it says.
    let e = bad(&format!(
        r#"{LOGIC}
fn twice(n: Nat) -> Nat {{ n }}
instance Dec<twice(2)> {{ d := R(λ (h: Bot) => h) }}
"#
    ));
    assert!(
        e.contains("not a type or a type former") || e.contains("universe"),
        "unexpected: {e}"
    );
}

#[test]
fn a_self_feeding_type_former_instance_is_refused() {
    // Paterson's condition had to learn the new syntax: `ty_size` and
    // `ty_var_count` fell through to `1`/`0` for an applied former, which made
    // every such instance refuse whatever it required. Now that they walk the
    // spine, the *decrease* has to still be enforced — a subgoal at the same
    // carrier is a search that feeds itself.
    let e = bad(&format!(
        r#"{LOGIC}
instance<P> Dec<Neg(P)> requires self: Dec<Neg(P)> {{ d := self.d }}
"#
    ));
    assert!(
        e.contains("structurally smaller") || e.contains("forever"),
        "unexpected: {e}"
    );
}

#[test]
fn a_duplicate_at_one_former_head_is_a_declaration_error() {
    // The coarsening the widening accepts, observed: two carriers sharing the
    // head `Neg` collide, and that is refused rather than silently overwritten
    // (`docs/traits-layer1-design.md` §4.1, unchanged by this round).
    let e = bad(&format!(
        r#"{LOGIC}{NEG_INSTANCE}
instance Dec<Neg(Bot)> {{ d := L(λ (h: Bot) => h) }}
"#
    ));
    assert!(e.contains("already has an instance"), "unexpected: {e}");
}

// -- 3: a former written with TYPE arguments -------------------------------
//
// `issues/type-former-carrier-with-type-arguments.md`. The widening walked the
// application spine in its *value* spelling only: `Le(n, m)` is an `App` around
// a `Var`, but `Tag<A>(n)` is an `App` around a `TyApp` around the `Var`, so the
// head fell one node out of reach and the carrier had no name. The type
// arguments are no more part of the head than the value arguments are — the
// registry has never keyed on a carrier's arguments.
//
// Found stacked under `issues/recursive-self-call-type-arguments.md`, which
// made the former fail to *declare* and so hid this behind it.

/// A former taking a type parameter **and** a value parameter, stuck at an open
/// `n` — the shape that reaches `head_name` as `App { head: TyApp { … } }`. The
/// value argument is inert on purpose: what is under test is the head, and a
/// carrier whose value argument did work would let reduction supply it.
const TAG: &str = r#"
fn Tag<A>(n: Nat) -> Type { match n { Zero => A, Succ(k) => A } }
fn tag_val<A>(a: A, n: Nat) -> Tag<A>(n) {
    match n as λ z => Tag<A>(z) { Zero => a, Succ(k) => a }
}
fn tag_neg<A>(f: Neg(A), n: Nat) -> Neg(Tag<A>(n)) {
    match n as λ z => Neg(Tag<A>(z)) { Zero => f, Succ(k) => f }
}
instance<P: Dec>(n: Nat) Dec<Tag<P>(n)> {
    d := match P.d { L(p) => L(tag_val<P>(p, n)), R(np) => R(tag_neg<P>(np, n)) },
}
"#;

#[test]
fn a_former_with_type_arguments_is_a_carrier() {
    // Registration alone: before this the head was `None` and the instance had
    // no canonical name.
    ok(&format!("{LOGIC}{TAG}"));
}

#[test]
fn it_resolves_at_an_open_type_and_an_open_value() {
    // Both axes open at once, which is the case the head-name gap made
    // unreachable: `B` is a constrained type parameter and `k` a binder, so
    // neither argument can be supplied by reduction, and the answer has to come
    // from unifying the instance head against the goal.
    ok(&format!(
        r#"{LOGIC}{TAG}
fn dec_of<P: Dec>() -> Sum<P, Neg(P)> {{ P.d }}
fn both_open<B: Dec>(k: Nat) -> Sum<Tag<B>(k), Neg(Tag<B>(k))> {{ dec_of() }}
"#
    ));
}

#[test]
fn patersons_condition_measures_a_type_argument_carrier() {
    // The lesson of the first widening, re-checked at the new syntax: a carrier
    // the measure cannot see into has size 1, which admits no strictly smaller
    // subgoal, so *every* instance at one refuses whatever it requires — a
    // failure that looks like a decrease bug rather than a measurement one.
    // `TAG` itself is the positive half (it requires `Dec<P>` and is admitted);
    // this is the negative half, so the two together pin the measure from both
    // sides rather than only proving it is not zero.
    let e = bad(&format!(
        r#"{LOGIC}
fn Tag<A>(n: Nat) -> Type {{ match n {{ Zero => A, Succ(k) => A }} }}
instance<P>(n: Nat) Dec<Tag<P>(n)> requires self: Dec<Tag<P>(n)> {{ d := self.d }}
"#
    ));
    assert!(
        e.contains("structurally smaller") || e.contains("forever"),
        "unexpected: {e}"
    );
}

#[test]
fn the_head_ignores_the_type_arguments_for_duplicates() {
    // The same coarsening as `Neg`, at the new spelling: `Tag<P>(n)` and
    // `Tag<Bot>(n)` are one key, and a second instance is a declaration error
    // naming both rather than a silent overwrite.
    let e = bad(&format!(
        r#"{LOGIC}{TAG}
instance(n: Nat) Dec<Tag<Bot>(n)> {{ d := R(λ (h: Bot) => h) }}
"#
    ));
    assert!(e.contains("already has an instance"), "unexpected: {e}");
}

#[test]
fn a_type_argument_former_that_is_not_a_type_former_is_refused() {
    // The negative control beside the positive: the owner rule is unchanged, so
    // a global returning `Nat` is still not something a proposition can be *of*,
    // and reaching its head does not make `Count::Dec` a sentence.
    let e = bad(&format!(
        r#"{LOGIC}
fn Count<A>(n: Nat) -> Nat {{ n }}
instance(n: Nat) Dec<Count<Bot>(n)> {{ d := R(λ (h: Bot) => h) }}
"#
    ));
    assert!(e.contains("not a type or a type former"), "unexpected: {e}");
}
