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
//! — including the two carriers that are still refused on purpose.

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
fn an_equation_carrier_is_still_refused() {
    // Deliberate, and the one case of this round that genuinely wants layer 2's
    // (class, carrier-syntax) key: a single reserved head for `=` would collide
    // equality at `Nat` with equality at every other type
    // (`docs/decide-class-design.md` §3.1).
    let e = bad(&format!(
        r#"{LOGIC}
instance Dec<2 = 2> {{ d := L(refl) }}
"#
    ));
    assert!(e.contains("no head type name"), "unexpected: {e}");
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
