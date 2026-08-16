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
use support::{BIN_ADD, BIN_MIN, BIN_REPR as BIN};

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
    // `inv` and `fold` are *not* named: they default
    // (`issues/repr-fold-via-abs-default.md`), and the message says so.
    assert!(msg.contains("`inv` and `fold` default"), "{msg}");
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

// -- the clause defaults (issues/repr-fold-via-abs-default.md) --------------
//
// An omitted `inv` is `True`; an omitted `fold` is the fold *through* `abs`,
// synthesized together with the embedding `S -> R` (the spec recursor over the
// constructor images) and the two lemmas its anchor law rests on. The four
// artifacts are generated terms, so the axes are varied below: an **open**
// element type, an arm with **two** recursive children, a **neutral** carrier
// value beside a literal one, a **checking** position (the anchor law consumed
// where its statement is expected), and negative controls.

/// The milestone: a real repr of `Nat` written as `R`, `abs`, the images and
/// the one law that is not `refl`.
#[test]
fn the_minimal_repr_is_the_carrier_the_images_and_the_laws_that_are_not_refl() {
    ok(&format!(
        "{BIN_MIN}
// The defaulted fold *computes*, at the carrier: the representation of three
// folded with a counting algebra is three.
theorem counts_to_three():
    Repr_BinMin::fold()(Nat)(Zero)(\u{3bb} (a0: Bin) => \u{3bb} (b0: Nat) => Succ(b0))(B1(B1(BNil)))
      = Succ(Succ(Succ(Zero)))
{{ refl }}

// …and it anchors, at a **neutral** `r` and in a **checking** position: the
// generated `fold_law` is exactly the statement the transfer generator wants,
// and its proof is the generated induction rather than `refl`.
theorem anchor(s0: Nat, s1: (a: Nat) -> (b: Nat) -> Nat, r: Bin):
    Repr_BinMin::fold()(Nat)(s0)(\u{3bb} (a0: Bin) => \u{3bb} (b0: Nat) => s1(bin_abs(a0))(b0))(r)
      = BinMin_spec_rec(Nat, s0, s1, bin_abs(r))
{{ Repr_BinMin::fold_law()(Nat)(s0)(s1)(r)(refl) }}

// The defaulted `inv` is `True`, spelled as the naive repr spells it.
theorem inv_is_true(r: Bin): Repr_BinMin::inv()(r) {{ refl }}

// The embedding the default folds through is a real function `Nat -> Bin`, and
// its round-trip is a real theorem — neither is `bin_of_nat`, which is in scope
// and unused.
theorem embeds_four(): bin_abs(BinMin_emb(Succ(Succ(Succ(Succ(Zero)))))) = Succ(Succ(Succ(Succ(Zero))))
{{ BinMin_emb_abs(Succ(Succ(Succ(Succ(Zero))))) }}
"
    ));
}

/// The generality axes for the synthesized lemmas: an element type that is not
/// the carrier (`Tok`), and an arm with **two** recursive children — where the
/// round-trip's rewrite chain has more than one link and an off-by-one in the
/// position it abstracts would show.
#[test]
fn the_defaults_hold_at_an_open_element_type_and_at_two_recursive_children() {
    ok(&format!(
        "{LIST}
inductive Stk {{ SNil, SCons(h: Tok, t: Stk) }}
fn stk_abs(r: Stk) -> List<Tok> {{ match r {{ SNil => Nil, SCons(h, t) => Cons(h, stk_abs(t)) }} }}

datarepr StkTok for List<Tok> {{ R := Stk, abs := stk_abs, mk Nil := SNil, mk Cons := SCons }}

inductive Tree {{ Leaf(n: Nat), Node(l: Tree, r: Tree) }}
inductive TreeC {{ CLeaf(n: Nat), CNode(l: TreeC, r: TreeC) }}
fn tc_abs(x: TreeC) -> Tree {{
    match x {{ CLeaf(n) => Leaf(n), CNode(l, r) => Node(tc_abs(l), tc_abs(r)) }}
}}

datarepr TreeR for Tree {{ R := TreeC, abs := tc_abs, mk Leaf := CLeaf, mk Node := CNode }}

// A **neutral** carrier value under the defaulted fold, in a checking position.
fn stk_len(r: Stk) -> Nat {{
    Repr_StkTok::fold()(Nat)(Zero)(\u{3bb} (h: Tok) => \u{3bb} (t: Stk) => \u{3bb} (b: Nat) => Succ(b))(r)
}}
theorem stk_len_two(): stk_len(SCons(TAdd, SCons(TMul, SNil))) = Succ(Succ(Zero)) {{ refl }}

// The two-recursive-children arm, anchored at a neutral `x`.
theorem tree_anchor(s0: (n: Nat) -> Nat, s1: (l: Tree) -> (r: Tree) -> (b0: Nat) -> (b1: Nat) -> Nat,
                    x: TreeC):
    Repr_TreeR::fold()(Nat)(s0)(\u{3bb} (l: TreeC) => \u{3bb} (r: TreeC) => \u{3bb} (b0: Nat) => \u{3bb} (b1: Nat) =>
                                    s1(tc_abs(l))(tc_abs(r))(b0)(b1))(x)
      = TreeR_spec_rec(Nat, s0, s1, tc_abs(x))
{{ Repr_TreeR::fold_law()(Nat)(s0)(s1)(x)(refl) }}
"
    ));
}

/// Negative control: the defaults do not cascade. A law that is omitted is
/// `refl`, and where `refl` is wrong the repr is refused — the defaulted fold
/// changes nothing about that.
#[test]
fn a_law_that_is_not_refl_is_still_owed_by_a_minimal_repr() {
    let msg = bad(&BIN_MIN.replace("    Succ_abs := bin_succ_abs_law,\n", ""));
    assert!(msg.contains("datarepr BinMin"), "{msg}");
    assert!(msg.contains("Succ_abs"), "{msg}");
}

/// Negative control: a wrong `abs` under a defaulted fold is still refused.
/// There is no repr whose image laws hold and whose *defaulted* `fold_law`
/// fails — the round's finding is that the anchor is derivable from those laws
/// — so this is where a wrong basis surfaces.
#[test]
fn a_wrong_abs_is_refused_under_a_defaulted_fold() {
    let msg = bad(&BIN_MIN.replace(
        "        B0(b) => double(bin_abs(b)),\n        B1(b) => Succ(double(bin_abs(b))),",
        "        B0(b) => bin_abs(b),\n        B1(b) => Succ(bin_abs(b)),",
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
}

/// Negative control: a *written* fold is checked exactly as before — the
/// default is what omission means, not a fallback for a clause that fails.
#[test]
fn a_written_fold_is_still_checked_against_the_anchor() {
    // `BIN_MIN` with the anchor fold written as something that ignores its
    // step, and `fold_law` left to its `refl` default as a written fold's is.
    let msg = bad(&BIN_MIN.replace(
        "    mk Zero := BNil,",
        "    fold := \u{3bb} (B: Type) => \u{3bb} (s0: B) => \
         \u{3bb} (s1: (a0: Bin) -> (b0: B) -> B) => \u{3bb} (r: Bin) => s0,
    mk Zero := BNil,",
    ));
    assert!(msg.contains("fold_law"), "{msg}");
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
