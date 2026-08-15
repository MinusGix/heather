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

const BIN: &str = r#"
inductive Bin { BNil, B0(b: Bin), B1(b: Bin) }

fn double(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(double(k))) } }

// Little-endian bits, least significant first. `B0(BNil)` and `BNil` both
// denote zero: `abs` is not injective, and nothing requires it to be.
fn bin_abs(r: Bin) -> Nat {
    match r {
        BNil => Zero,
        B0(b) => double(bin_abs(b)),
        B1(b) => Succ(double(bin_abs(b))),
    }
}

fn bin_inv(r: Bin) -> Type { Zero = Zero }

fn binc(r: Bin) -> Bin {
    match r { BNil => B1(BNil), B0(b) => B1(b), B1(b) => B0(binc(b)) }
}

theorem cong_double({a: Nat}, {b: Nat}, p: a = b): double(a) = double(b) {
    j(p, λ y q => double(a) = double(y), refl)
}

// The commutation law for `Succ`'s image. The carry case is the only one with
// content: it is where `binc` recurses and where `double(Succ n)` has to
// unfold on the other side.
theorem bin_succ_abs(r: Bin): bin_abs(binc(r)) = Succ(bin_abs(r)) {
    match r { BNil => refl, B0(b) => refl, B1(b) => cong_double(bin_succ_abs(b)) }
}

theorem bin_succ_abs_law(a0: Bin, h0: (Zero = Zero)):
    bin_abs(binc(a0)) = Succ(bin_abs(a0)) { bin_succ_abs(a0) }

// `Nat`'s recursor, by hand: `match` is a form and not a global, so the
// anchor's statement needs a name. Definitionally the generated
// `BinNat_spec_rec`, which is what lets the hand-written law below discharge
// the generated obligation.
fn nat_rec_(B: Type, z: B, s: (a: Nat) -> (b: B) -> B, x: Nat) -> B {
    match x { Zero => z, Succ(k) => s(k)(nat_rec_(B, z, s, k)) }
}

fn bin_of_nat(n: Nat) -> Bin { match n { Zero => BNil, Succ(m) => binc(bin_of_nat(m)) } }

theorem bin_roundtrip(m: Nat): bin_abs(bin_of_nat(m)) = m {
    match m {
        Zero => refl,
        Succ(k) => trans(bin_succ_abs(bin_of_nat(k)), cong_succ(bin_roundtrip(k))),
    }
}

// The anchor. Slow on purpose (§1.1): it goes through the spec value, which
// is exactly what the cost basis exists to bypass.
fn bin_fold(B: Type, s0: B, s1: (a0: Bin) -> (b0: B) -> B, r: Bin) -> B {
    nat_rec_(B, s0, λ (m: Nat) => λ (b: B) => s1(bin_of_nat(m))(b), bin_abs(r))
}

theorem natrec_cong(B: Type, z: B, s1: (a: Nat) -> (b: B) -> B,
                    s2: (a: Nat) -> (b: B) -> B,
                    h: (a: Nat) -> (b: B) -> s1(a)(b) = s2(a)(b), n: Nat):
    nat_rec_(B, z, s1, n) = nat_rec_(B, z, s2, n)
{
    match n {
        Zero => refl,
        Succ(k) => trans(
            j(natrec_cong(B, z, s1, s2, h, k),
              λ y q => s1(k)(nat_rec_(B, z, s1, k)) = s1(k)(y), refl),
            h(k)(nat_rec_(B, z, s2, k))),
    }
}

theorem bin_fold_law(B: Type, s0: B, s1: (a0: Nat) -> (b0: B) -> B, r: Bin,
                     h: (Zero = Zero)):
    bin_fold(B, s0, λ (a0: Bin) => λ (b0: B) => s1(bin_abs(a0))(b0), r)
      = nat_rec_(B, s0, s1, bin_abs(r))
{
    natrec_cong(B, s0, λ (m: Nat) => λ (b: B) => s1(bin_abs(bin_of_nat(m)))(b), s1,
                λ (a: Nat) => λ (b: B) =>
                    j(bin_roundtrip(a),
                      λ y q => s1(bin_abs(bin_of_nat(a)))(b) = s1(y)(b), refl),
                bin_abs(r))
}

datarepr BinNat for Nat {
    R := Bin,
    abs := bin_abs,
    inv := bin_inv,
    mk Zero := BNil,
    mk Succ := binc,
    Succ_abs := bin_succ_abs_law,
    fold := bin_fold,
    fold_law := bin_fold_law,
}
"#;

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
const BIN_ADD: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }

fn bin_add_derived(ra: Bin, rb: Bin) -> Bin {
    bin_fold(Bin, ra, λ (t: Bin) => λ (acc: Bin) => binc(acc), rb)
}

// `binc` iterated `n` times commutes with `abs` into `add`. The only
// induction the cost basis needs here.
theorem bin_iter_abs(ra: Bin, n: Nat):
    bin_abs(nat_rec_(Bin, ra, λ (a: Nat) => λ (b: Bin) => binc(b), n))
      = add(bin_abs(ra), n)
{
    match n {
        Zero => refl,
        Succ(k) => trans(
            bin_succ_abs(nat_rec_(Bin, ra, λ (a: Nat) => λ (b: Bin) => binc(b), k)),
            cong_succ(bin_iter_abs(ra, k))),
    }
}

theorem bin_add_derived_refines(ra: Bin, rb: Bin, h0: (Zero = Zero), h1: (Zero = Zero)):
    bin_abs(bin_add_derived(ra, rb)) = add(bin_abs(ra), bin_abs(rb))
{ bin_iter_abs(ra, bin_abs(rb)) }

theorem bin_add_derived_inv(ra: Bin, rb: Bin, h0: (Zero = Zero), h1: (Zero = Zero)):
    bin_inv(bin_add_derived(ra, rb)) { refl }

theorem cong_bin_abs({a: Bin}, {b: Bin}, p: a = b): bin_abs(a) = bin_abs(b) {
    j(p, λ y q => bin_abs(a) = bin_abs(y), refl)
}
"#;

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
