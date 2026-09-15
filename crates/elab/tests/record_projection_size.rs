//! Projecting a field off a record **value**, at the size where the old walk
//! died: `issues/theorem-field-projection-oom.md`.
//!
//! The defect was not a wrong answer but a wrong *size*. A projection was
//! `fst(sndʲ v)` built by walking the Σ spine and substituting each field's
//! projection into the tail; every `fst`/`snd` node carries the Σ components
//! at its level as annotations, so a later field's type — which mentions the
//! earlier fields — inlined the earlier projections *with their annotations*
//! once per occurrence, and the annotations of those were the payload one
//! level down. Eleven fields with a handful of cross-references was enough to
//! exhaust memory and abort. The fix names each projection and each tail as a
//! Ψ definition (`gendefs.rs`), so a field's type mentions one node.
//!
//! What the tests here have to vary is therefore *size and shape of the
//! record*, on top of `docs/testing-generated-terms.md`'s axes: a **literal**
//! receiver (an assembled value) and a **neutral** one (a parameter), a
//! **checking** position (the projected law used as the proof of a stated
//! theorem, so a wrong type is a rejection rather than a different term), an
//! **open** field type (the record's own `R: Type` field, whose inhabitants
//! are not fixed by the declaration), and negative controls — because a fix
//! that made projection *cheap* by making it wrong would pass every timing
//! test in the file.
//!
//! These are ordinary elaborations: every term below faces the real kernel,
//! and the whole point of the regression is that it now *checks* rather than
//! merely not aborting.

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

const LIST: &str = "
inductive Tok { TPush(n: Nat), TAdd, TMul }
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
";

/// The record `datarepr` generates for `List<Tok>`, written out by hand: an
/// open carrier `R`, two functions of it, a maker per constructor, a law pair
/// per constructor, a fold and a fold law. Eleven fields, and every law
/// mentions `R`, `abs`, `inv` and a maker — which is the cross-reference
/// density the old walk raised to the eleventh power.
const REC: &str = "
fn Rp_spec_rec(B: Type, s0: B, s1: (a0: Tok) -> (a1: List<Tok>) -> (b0: B) -> B, x: List<Tok>) -> B {
    match x {
        Nil => s0,
        Cons(a0, a1) => s1(a0, a1, Rp_spec_rec(B, s0, s1, a1)),
    }
}

record Rp {
    R: Type,
    abs: (r: R) -> List<Tok>,
    inv: (r: R) -> Type,
    mk_Nil: R,
    mk_Cons: (a0: Tok) -> (a1: R) -> R,
    Nil_abs: abs(mk_Nil) = Nil,
    Nil_inv: inv(mk_Nil),
    Cons_abs: (a0: Tok) -> (a1: R) -> (h0: inv(a1)) -> abs(mk_Cons(a0, a1)) = Cons(a0, abs(a1)),
    Cons_inv: (a0: Tok) -> (a1: R) -> (h0: inv(a1)) -> inv(mk_Cons(a0, a1)),
    fold: (B: Type) -> (s0: B) -> (s1: (a0: Tok) -> (a1: R) -> (b0: B) -> B) -> (r: R) -> B,
    fold_law: (B: Type) -> (s0: B) -> (s1: (a0: Tok) -> (a1: List<Tok>) -> (b0: B) -> B) -> (r: R) -> (h: inv(r)) -> fold(B, s0, λ a0 a1 b0 => s1(a0, abs(a1), b0), r) = Rp_spec_rec(B, s0, s1, abs(r)),
}
";

/// The identity repr of `List<Tok>` at that record: every clause is the
/// obvious one, so every law is `refl` and nothing here is about the proofs.
const VAL: &str = "
fn Rp::abs() -> (r: List<Tok>) -> List<Tok> { λ r => r }
fn Rp::inv() -> (r: List<Tok>) -> Type { λ r => (Zero = Zero) }
fn Rp::mk_Nil() -> List<Tok> { Nil }
fn Rp::mk_Cons() -> (a0: Tok) -> (a1: List<Tok>) -> List<Tok> { λ a0 a1 => Cons(a0, a1) }
theorem Rp::Nil_abs(): Rp::abs(Rp::mk_Nil()) = Nil { refl }
theorem Rp::Nil_inv(): Rp::inv(Rp::mk_Nil()) { refl }
theorem Rp::Cons_abs(): (a0: Tok) -> (a1: List<Tok>) -> (h0: Rp::inv(a1)) -> Rp::abs(Rp::mk_Cons(a0, a1)) = Cons(a0, Rp::abs(a1)) { λ a0 a1 h0 => refl }
theorem Rp::Cons_inv(): (a0: Tok) -> (a1: List<Tok>) -> (h0: Rp::inv(a1)) -> Rp::inv(Rp::mk_Cons(a0, a1)) { λ a0 a1 h0 => refl }
fn Rp::fold() -> (B: Type) -> (s0: B) -> (s1: (a0: Tok) -> (a1: List<Tok>) -> (b0: B) -> B) -> (r: List<Tok>) -> B { λ B s0 s1 r => Rp_spec_rec(B, s0, s1, r) }
theorem Rp::fold_law(): (B: Type) -> (s0: B) -> (s1: (a0: Tok) -> (a1: List<Tok>) -> (b0: B) -> B) -> (r: List<Tok>) -> (h: Rp::inv(r)) -> Rp::fold(B, s0, λ a0 a1 b0 => s1(a0, Rp::abs(a1), b0), r) = Rp_spec_rec(B, s0, s1, Rp::abs(r)) { λ B s0 s1 r h => refl }

fn RpV() -> Rp { Rp { R: List<Tok>, abs: Rp::abs(), inv: Rp::inv(), mk_Nil: Rp::mk_Nil(), mk_Cons: Rp::mk_Cons(), Nil_abs: Rp::Nil_abs(), Nil_inv: Rp::Nil_inv(), Cons_abs: Rp::Cons_abs(), Cons_inv: Rp::Cons_inv(), fold: Rp::fold(), fold_law: Rp::fold_law() } }
";

// -- 1: the reported shape, by hand ----------------------------------------

// The issue's repro with `datarepr` taken out of it: a theorem-valued field,
// eight entries down a spine whose later types all mention the earlier ones,
// projected off an assembled **value** and used in a **checking** position —
// the statement is written out, so the projection's type is what decides.
#[test]
fn a_law_field_projects_off_an_assembled_value() {
    ok(&format!(
        r#"
        {LIST}{REC}{VAL}
        theorem proj_law(a0: Tok, a1: List<Tok>, h0: Rp::inv(a1)):
            Rp::abs(Rp::mk_Cons(a0, a1)) = Cons(a0, Rp::abs(a1))
        {{ RpV().Cons_abs(a0, a1, h0) }}
        "#
    ));
}

// The same projection off a **neutral** receiver. The old walk's exponent was
// in the annotations, which do not depend on the receiver at all, so this died
// exactly as the literal did — and a fix that only reduced projections of
// literal records would leave it dying.
#[test]
fn a_law_field_projects_off_a_neutral_receiver() {
    ok(&format!(
        r#"
        {LIST}{REC}
        theorem proj_law(p: Rp, a0: Tok, a1: p.R, h0: p.inv(a1)):
            p.abs(p.mk_Cons(a0, a1)) = Cons(a0, p.abs(a1))
        {{ p.Cons_abs(a0, a1, h0) }}
        "#
    ));
}

// The **last** field, whose type mentions six earlier ones and is the largest
// in the record: the deepest point of the spine, off a value.
#[test]
fn the_last_field_projects() {
    ok(&format!(
        r#"
        {LIST}{REC}{VAL}
        theorem fold_law_of(B: Type, s0: B,
                            s1: (a0: Tok) -> (a1: List<Tok>) -> (b0: B) -> B,
                            r: List<Tok>, h: Rp::inv(r)):
            Rp::fold(B, s0, λ a0 a1 b0 => s1(a0, Rp::abs(a1), b0), r)
              = Rp_spec_rec(B, s0, s1, Rp::abs(r))
        {{ RpV().fold_law(B, s0, s1, r, h) }}
        "#
    ));
}

// -- 2: the same through `datarepr`, which is where it was found ------------

// `issues/theorem-field-projection-oom.md`'s own repro, verbatim in shape: the
// generated record, the assembled value `ListTok()`, and its `Cons_abs` field
// used as the proof of the law it states. This is what aborted.
#[test]
fn a_generated_repr_records_law_projects_off_the_assembled_value() {
    ok(&format!(
        r#"
        {LIST}
        datarepr ListTok for List<Tok> := repr::naive();
        theorem proj_law(a0: Tok, a1: List<Tok>, h0: ListTok::inv(a1)):
            ListTok::abs(ListTok::mk_Cons(a0, a1)) = Cons(a0, ListTok::abs(a1))
        {{ ListTok().Cons_abs(a0, a1, h0) }}
        "#
    ));
}

// The route the elaboration itself uses — through the generated namespace —
// was the workaround and stays green: the two spellings prove the same law.
#[test]
fn the_namespace_route_still_proves_the_same_law() {
    ok(&format!(
        r#"
        {LIST}
        datarepr ListTok for List<Tok> := repr::naive();
        theorem proj_law(a0: Tok, a1: List<Tok>, h0: ListTok::inv(a1)):
            ListTok::abs(ListTok::mk_Cons(a0, a1)) = Cons(a0, ListTok::abs(a1))
        {{ ListTok::Cons_abs(a0, a1, h0) }}
        "#
    ));
}

// -- 3: what the projection has to still *mean* ----------------------------

// A projection off a literal is the field, definitionally — the property a
// named projection could quietly lose, since the name is opaque until it
// unfolds. At the deep end of the spine, not the shallow one.
#[test]
fn a_deep_projection_off_a_literal_still_computes() {
    ok(&format!(
        r#"
        {LIST}{REC}{VAL}
        theorem cons_abs_is_the_clause(): RpV().Cons_abs = Rp::Cons_abs() {{ refl }}
        theorem fold_is_the_clause(): RpV().fold = Rp::fold() {{ refl }}
        theorem carrier_is_the_carrier(a: List<Tok>): RpV().abs(a) = a {{ refl }}
        "#
    ));
}

// Every one of the eleven projections is the field it claims, checked field by
// field against the clause the value was built from. One wrong index anywhere
// in the spine — the mistake a rewrite of this walk would make — shows up here
// as a rejection, and the deep fields are exactly the ones the walk used to
// die before reaching.
//
// (The stronger statement, η at a *neutral* receiver — rebuilding the record
// from its own projections and converting it with the receiver — is out of
// fuel at this size, before this round and after it: the reconstruction is a
// pair nest eleven deep whose components each unfold a projection. That is a
// conversion cost, not a projection one, and it belongs to
// `issues/theorem-field-projection-oom.md`'s follow-on.)
#[test]
fn every_field_projects_to_its_own_clause() {
    ok(&format!(
        r#"
        {LIST}{REC}{VAL}
        theorem f0(): RpV().R = List<Tok> {{ refl }}
        theorem f1(): RpV().abs = Rp::abs() {{ refl }}
        theorem f2(): RpV().inv = Rp::inv() {{ refl }}
        theorem f3(): RpV().mk_Nil = Rp::mk_Nil() {{ refl }}
        theorem f4(): RpV().mk_Cons = Rp::mk_Cons() {{ refl }}
        theorem f5(): RpV().Nil_abs = Rp::Nil_abs() {{ refl }}
        theorem f6(): RpV().Nil_inv = Rp::Nil_inv() {{ refl }}
        theorem f7(): RpV().Cons_abs = Rp::Cons_abs() {{ refl }}
        theorem f8(): RpV().Cons_inv = Rp::Cons_inv() {{ refl }}
        theorem f9(): RpV().fold = Rp::fold() {{ refl }}
        theorem f10(): RpV().fold_law = Rp::fold_law() {{ refl }}
        "#
    ));
}

// -- 4: negative controls ---------------------------------------------------

// The projected law is the law of *this* record, not a free-floating equation:
// swapping the constructor arguments in the statement is a rejection.
#[test]
fn a_law_field_does_not_prove_a_different_equation() {
    let e = bad(&format!(
        r#"
        {LIST}{REC}{VAL}
        theorem wrong(a0: Tok, a1: List<Tok>, h0: Rp::inv(a1)):
            Rp::abs(Rp::mk_Cons(a0, a1)) = Cons(a0, Nil)
        {{ RpV().Cons_abs(a0, a1, h0) }}
        "#
    ));
    assert!(e.contains("wrong"), "{e}");
}

// A field of the *right shape* at the wrong index is still rejected: `Nil_abs`
// does not prove `Cons_abs`'s statement.
#[test]
fn a_neighbouring_field_does_not_prove_this_law() {
    let e = bad(&format!(
        r#"
        {LIST}{REC}{VAL}
        theorem swapped(): Rp::abs(Rp::mk_Nil()) = Nil {{ RpV().Nil_inv }}
        "#
    ));
    assert!(e.contains("swapped"), "{e}");
}

// The record has no field by that name, at any size.
#[test]
fn an_unknown_field_on_a_big_record_is_rejected() {
    let e = bad(&format!(
        r#"
        {LIST}{REC}{VAL}
        theorem nope(): Zero = Zero {{ let _x = RpV().Cons_absurd; refl }}
        "#
    ));
    assert!(e.contains("no field `Cons_absurd`"), "{e}");
}

// -- 5: the boundary --------------------------------------------------------

// A **parameterized** record used to have no closed lowering to name and kept
// the inline walk. Since `docs/telescoped-record-projections-design.md` (§3,
// 2026-09-15) it has one: `Monoid<A>` is telescoped and its spine is dependent
// (`unit_l` mentions `op` and `unit`), which is the device's fourth cell — the
// closed `RecFam`/`RecProj`/`RecTail` triple with `Θ` in front — so **this test
// now exercises the new route and no longer the fallback**. What it asserts is
// unchanged and is the point: the same three reads still elaborate, check and
// compute, off a **computed** receiver (`nat_monoid()`, which
// `receiver_admits_reference` declines and the dependent device is exempt
// from), off a **bare binder** (`m`, which the gate also declines), and at an
// **open** element type, with the law used in a **checking** position. The
// fallback walk itself is covered by the closed non-dependent records above,
// which are the cell that still declines.
#[test]
fn a_parameterized_records_dependent_field_still_projects() {
    ok(r#"
        record Monoid<A> {
            unit: A,
            op: A -> A -> A,
            unit_l: (x: A) -> op(unit, x) = x,
        }
        fn nat_monoid() -> Monoid<Nat> {
            Monoid { unit: 0, op: λ x y => y, unit_l: λ x => refl }
        }
        theorem law_at_a_value(x: Nat): nat_monoid().op(nat_monoid().unit, x) = x
        { nat_monoid().unit_l(x) }
        fn law_at_a_neutral<A>(m: Monoid<A>, x: A) -> m.op(m.unit, x) = x { m.unit_l(x) }
        "#);
}
