//! The `datarepr` declaration forms (`docs/datarepr-design.md` §1.4, §5.1).
//!
//! Every artifact here is a *generated term* in the sense of
//! `docs/testing-generated-terms.md` — the record type, the spec-recursor
//! specialization, every clause declaration and the assembled value are all
//! synthesized — so the four axes are varied deliberately: an **open** element
//! type (a repr of `List<Tok>`, whose element type is not the carrier), a
//! **checking** position (the assembled value checked against the generated
//! record type with no annotation, and projections checked at a field's
//! declared type), a **neutral** scrutinee (folds applied to a parameter, not
//! only to a literal), and a **negative control** beside each positive.

use heather_elab::Elaborator;

mod support;
use support::{BIN_ADD, BIN_REPR as BIN};

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

const LIST: &str = "
inductive Tok { TPush(n: Nat), TAdd, TMul }
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
";

#[test]
fn a_naive_repr_of_a_parameterized_instantiation() {
    ok(&format!("{LIST}\ndatarepr ListTok for List<Tok> := repr::naive();\n"));
}

#[test]
fn a_naive_repr_of_nat() {
    ok("datarepr NatN for Nat := repr::naive();\n");
}

// -- the v1 stretch: `Bin` as a repr of `Nat` (design §5.1 item 4) ----------
//
// Every obligation below has non-`refl` content: a genuine `abs`, a
// commutation law that is a theorem, and an anchor fold that is deliberately
// not what should run — it converts to unary and back, which is §1.1's "the
// fold need not be what runs" made visible.


#[test]
fn bin_is_a_repr_of_nat() {
    ok(BIN);
}

// -- negative controls ------------------------------------------------------
//
// The point of the round is that these obligations are *checked*. Each
// control perturbs one clause of a repr that is otherwise the passing one
// above, and each must be refused.

#[test]
fn a_wrong_abs_is_refused_by_the_kernel() {
    // `abs` reading `B0`/`B1` as if the bits were big-endian: `bin_abs` and
    // this differ at the first two-bit numeral, so `Succ`'s commutation law
    // stops holding while every type still checks.
    let src = BIN.replace(
        "        B0(b) => double(bin_abs(b)),\n        B1(b) => Succ(double(bin_abs(b))),",
        "        B0(b) => bin_abs(b),\n        B1(b) => Succ(bin_abs(b)),",
    );
    let msg = bad(&src);
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn a_fold_that_drops_the_step_is_refused_by_the_kernel() {
    // The anchor fold ignoring its step function: the shape typechecks, and
    // `fold_law` is exactly what catches it (§1.1 — the anchor is the
    // certificate anchor, so a wrong one cannot be silent).
    let src = BIN.replace(
        "    nat_rec_(B, s0, λ (m: Nat) => λ (b: B) => s1(bin_of_nat(m))(b), bin_abs(r))",
        "    s0",
    );
    let msg = bad(&src);
    assert!(msg.contains("NotConvertible"), "{msg}");
}

/// The control that lands *inside* the generated record: every hand-written
/// lemma still holds, and it is the `datarepr`'s own obligation that refuses.
#[test]
fn an_image_that_is_not_the_constructor_s_is_refused_at_the_datarepr() {
    let src = BIN
        .replace("fn binc(r: Bin)", "fn bin_dup(r: Bin) -> Bin { B0(r) }
fn binc(r: Bin)")
        .replace("mk Succ := binc,", "mk Succ := bin_dup,");
    let msg = bad(&src);
    assert!(msg.contains("datarepr BinNat"), "{msg}");
    assert!(msg.contains("Succ_abs"), "{msg}");
}

#[test]
fn an_image_at_a_constructor_that_is_not_the_spec_type_s_is_refused() {
    let msg = bad(&format!(
        "{LIST}\ndatarepr D for List<Tok> {{ R := List<Tok>, abs := f, inv := f, \
         mk Nope := f, fold := f }}\n"
    ));
    assert!(msg.contains("not a constructor of"), "{msg}");
}

#[test]
fn a_missing_clause_names_every_one_that_is_missing() {
    let msg = bad(&format!("{LIST}\ndatarepr D for List<Tok> {{ R := List<Tok> }}\n"));
    assert!(msg.contains("abs"), "{msg}");
    assert!(msg.contains("mk Nil"), "{msg}");
    assert!(msg.contains("mk Cons"), "{msg}");
    assert!(msg.contains("fold"), "{msg}");
}

#[test]
fn a_clause_that_is_not_a_field_of_the_repr_is_refused() {
    let msg = bad(&format!(
        "{LIST}\ndatarepr D for List<Tok> {{ R := List<Tok>, abs := f, inv := f, \
         mk Nil := f, mk Cons := f, fold := f, wat := f }}\n"
    ));
    assert!(msg.contains("`wat` is not a clause"), "{msg}");
}

#[test]
fn only_the_naive_generator_exists_this_round() {
    let msg = bad(&format!("{LIST}\ndatarepr D for List<Tok> := repr::clever();\n"));
    assert!(msg.contains("repr::naive()"), "{msg}");
}

#[test]
fn one_spec_type_takes_one_repr_this_round() {
    let msg = bad(&format!(
        "{LIST}\ndatarepr A for List<Tok> := repr::naive();\n\
         datarepr B for List<Tok> := repr::naive();\n"
    ));
    assert!(msg.contains("already has a repr"), "{msg}");
}

#[test]
fn a_repr_of_an_undeclared_type_is_refused() {
    let msg = bad("datarepr D for Nope := repr::naive();\n");
    assert!(msg.contains("not a declared inductive"), "{msg}");
}

// -- the assembled value in use (docs/testing-generated-terms.md) -----------

#[test]
fn the_assembled_repr_projects_and_folds_at_a_neutral_scrutinee() {
    // A **neutral** scrutinee (a parameter, not a literal) and a **checking**
    // position (each projection used where its declared type is expected),
    // over an **open** element type — `Tok` is not the carrier.
    //
    // Two fields are reached through the NAMESPACE rather than off the
    // assembled value, both for reasons recorded as as-landed notes on
    // design §1.4: `.fold` is claimed by the builtin vector receiver method
    // before the receiver's type is consulted, and projecting a
    // theorem-valued field off the assembled value exhausts memory. The
    // namespace half of the elaboration is what makes the laws usable.
    ok(&format!(
        "{LIST}
datarepr ListTok for List<Tok> := repr::naive();
fn len(l: List<Tok>) -> Nat {{
    Repr_ListTok::fold()(Nat)(Zero)(λ (t: Tok) => λ (r: List<Tok>) => λ (b: Nat) => Succ(b))(l)
}}
fn one(t: Tok) -> List<Tok> {{ ListTok().mk_Cons(t)(ListTok().mk_Nil) }}
theorem one_abs(t: Tok): ListTok().abs(one(t)) = Cons(t, Nil) {{
    Repr_ListTok::Cons_abs()(t)(Repr_ListTok::mk_Nil())(Repr_ListTok::Nil_inv())
}}
"
    ));
}

#[test]
fn the_fold_law_is_usable_as_a_rewrite_at_a_neutral_repr_value() {
    // The anchor consumed as a theorem, at a **neutral** `r` — the property
    // the transfer generator will be built on (§1.1's transfer theorem).
    ok(&format!(
        "{BIN}
theorem anchor(s0: Nat, s1: (a: Nat) -> (b: Nat) -> Nat, r: Bin):
    Repr_BinNat::fold()(Nat)(s0)(λ (a0: Bin) => λ (b0: Nat) => s1(bin_abs(a0))(b0))(r)
      = BinNat_spec_rec(Nat, s0, s1, bin_abs(r))
{{ Repr_BinNat::fold_law()(Nat)(s0)(s1)(r)(refl) }}
"
    ));
}

// -- the cost basis on `Bin` (design §1.2, §5.1 item 4) ---------------------

/// `add` at `Bin`, both routes. The **derived** implementation is what the
/// fold anchor gives — `binc` iterated `abs(rb)` times — and its certificate
/// comes straight out of `fold_law`. The **custom** one skips the anchor's
/// `bin_of_nat` round-trip at every step, and is certified *via-derived*: the
/// bodies are proved equal and the derived certificate is taken by
/// transitivity (§1.2).

const DERIVED_IMPL: &str = r#"
impl add for BinNat {
    body := bin_add_derived,
    refines := bin_add_derived_refines,
    refines_inv := bin_add_derived_inv,
}
"#;

#[test]
fn a_derived_impl_of_add_at_bin_is_registered_and_certified() {
    let e = ok(&format!("{BIN}{BIN_ADD}{DERIVED_IMPL}"));
    assert_eq!(e.impl_global("BinNat", "add"), Some("BinNat_add_impl"));
}

#[test]
fn a_via_derived_impl_takes_the_derived_certificate_by_transitivity() {
    // The custom body drops the anchor's `bin_of_nat(m)` — built and
    // discarded at every step — and is related to the derived one by an
    // equivalence, not by re-proving refinement (§1.2's via-derived route).
    let e = ok(&format!(
        "{BIN}{BIN_ADD}
fn bin_add_fast(ra: Bin, rb: Bin) -> Bin {{
    nat_rec_(Bin, ra, λ (a: Nat) => λ (b: Bin) => binc(b), bin_abs(rb))
}}

theorem bin_add_fast_is_derived(ra: Bin, rb: Bin):
    bin_add_fast(ra, rb) = bin_add_derived(ra, rb) {{ refl }}

theorem bin_add_fast_refines(ra: Bin, rb: Bin, h0: (Zero = Zero), h1: (Zero = Zero)):
    bin_abs(bin_add_fast(ra, rb)) = add(bin_abs(ra), bin_abs(rb))
{{
    trans(cong_bin_abs(bin_add_fast_is_derived(ra, rb)),
          bin_add_derived_refines(ra, rb, h0, h1))
}}

theorem bin_add_fast_inv(ra: Bin, rb: Bin, h0: (Zero = Zero), h1: (Zero = Zero)):
    bin_inv(bin_add_fast(ra, rb)) {{ refl }}

impl add for BinNat {{
    body := bin_add_fast,
    refines := bin_add_fast_refines,
    refines_inv := bin_add_fast_inv,
}}
"
    ));
    assert_eq!(e.impl_global("BinNat", "add"), Some("BinNat_add_impl"));
}

#[test]
fn an_impl_whose_body_does_not_refine_is_refused() {
    // `bin_add_derived` swapped for one that drops its second argument: the
    // types all still check, and `refines` is what catches it.
    let msg = bad(&format!(
        "{BIN}{BIN_ADD}
fn bin_add_wrong(ra: Bin, rb: Bin) -> Bin {{ ra }}
impl add for BinNat {{
    body := bin_add_wrong,
    refines := bin_add_derived_refines,
    refines_inv := bin_add_derived_inv,
}}
"
    ));
    assert!(msg.contains("impl add for BinNat"), "{msg}");
}

#[test]
fn an_impl_building_a_repr_owes_inv_of_what_it_built() {
    let msg = bad(&format!(
        "{BIN}{BIN_ADD}
impl add for BinNat {{ body := bin_add_derived, refines := bin_add_derived_refines }}
"
    ));
    assert!(msg.contains("refines_inv"), "{msg}");
}

#[test]
fn an_impl_at_an_unknown_repr_is_refused() {
    let msg = bad(&format!(
        "{BIN}{BIN_ADD}
impl add for Nope {{ body := bin_add_derived, refines := bin_add_derived_refines }}
"
    ));
    assert!(msg.contains("is not a `datarepr`"), "{msg}");
}

#[test]
fn one_operation_takes_one_impl_per_repr() {
    let msg = bad(&format!(
        "{BIN}{BIN_ADD}{DERIVED_IMPL}{DERIVED_IMPL}"
    ));
    assert!(msg.contains("already has an implementation"), "{msg}");
}

#[test]
fn an_impl_of_something_that_is_not_a_declared_function_is_refused() {
    let msg = bad(&format!(
        "{BIN}{BIN_ADD}
impl nope for BinNat {{ body := bin_add_derived, refines := bin_add_derived_refines }}
"
    ));
    assert!(msg.contains("not a declared function"), "{msg}");
}
