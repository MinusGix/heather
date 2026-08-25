//! `reprgen` — derived `Impl`s for structural spec fns over repr'd types
//! (`docs/datarepr-design.md` §3, §5.1 item 5).
//!
//! The hand-run comes first (the discipline `docs/certgen-*-design.md` calls
//! hand-run-first): the artifacts below are written by hand in exactly the
//! shape the generator emits, so that what the generator has to produce is
//! known to be checkable before anything produces it.
//!
//! The broad hand-run/negative matrix is intentionally slow-lane coverage:
//! tests prefixed `slow_acceptance_` run under plain `scripts/test` and are
//! skipped by `scripts/test --fast`. The fast lane retains the two generated
//! cross-axis positives, one end-to-end transfer, and one kernel-refusal
//! control; those four exercise generation rather than repeating every
//! stable emitted shape.

use heather_elab::Elaborator;

mod support;
use support::{BIN_CANON, BIN_MIN, BIN_REPR, UNARY_CANON};

fn ok(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
    e
}

const LIST: &str = "
inductive Tok { TPush(n: Nat), TAdd, TMul }
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
datarepr ListTok for List<Tok> := repr::naive();
";

/// The hand-run for verification item (b): `length`, a structural fn over
/// `List<Tok>`, transferred to the naive repr through the fold anchor.
#[test]
fn slow_acceptance_hand_run_a_derived_impl_over_the_naive_list_repr() {
    ok(&format!(
        "{LIST}
fn length(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => Succ(length(t)) }} }}

// Phase 2: the structural match becomes the anchor fold, with the algebra
// read off the arms and the recursive occurrence at the accumulator slot.
fn length_derived(r: List<Tok>) -> Nat {{
    ListTok::fold(Nat, Zero, λ a0 a1 b0 => Succ(b0), r)
}}

// Phase 4, part one: the spec fn agrees with its own recursor unfolding.
// NOT definitional — both sides are recursive globals — so this is an
// induction the generator has to emit.
theorem length_is_rec(l: List<Tok>):
    ListTok::spec_rec(Nat, Zero, λ a0 a1 b0 => Succ(b0), l)
      = length(l)
{{ match l {{ Nil => refl, Cons(h, t) => cong_succ(length_is_rec(t)) }} }}

// Phase 4, part two: `fold_law` opens the anchor, the lemma above closes it.
theorem length_derived_refines(r: List<Tok>, h0: True):
    length_derived(r) = length(ListTok::abs(r))
{{
    trans(ListTok::fold_law(Nat, Zero, λ a0 a1 b0 => Succ(b0), r, h0),
          length_is_rec(r))
}}

impl length for ListTok {{
    body := length_derived,
    refines := length_derived_refines,
}}
"
    ));
}

/// The hand-run for verification item (c): the same schema at `Bin`, where
/// the result type IS the spec type. The fold's algebra then lives at the
/// *carrier*, so the closing lemma is an induction that pushes `abs` through
/// the algebra using the image commutation law — §3.1 phase 4's "each image
/// by its commutation law". Nothing parallel to the `List` route: one extra
/// lemma shape, chosen by whether the result is repr-typed.
#[test]
fn slow_acceptance_hand_run_a_derived_impl_at_bin_where_the_result_is_the_spec_type() {
    ok(&format!(
        "{BIN_REPR}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}

fn double_derived(r: Bin) -> Bin {{
    BinNat::fold(Bin, BNil, λ a0 b0 => binc(binc(b0)), r)
}}

// `abs` pushed through the algebra, by induction, on the image law.
theorem double_abs_alg(n: Nat):
    bin_abs(BinNat::spec_rec(Bin, BNil, λ a b => binc(binc(b)), n))
      = double_spec(n)
{{
    match n {{
        Zero => refl,
        Succ(k) => trans(
            bin_succ_abs(binc(BinNat::spec_rec(Bin, BNil, λ a b => binc(binc(b)), k))),
            cong_succ(trans(
                bin_succ_abs(BinNat::spec_rec(Bin, BNil, λ a b => binc(binc(b)), k)),
                cong_succ(double_abs_alg(k))))),
    }}
}}

theorem double_derived_refines(r: Bin, h0: (Zero = Zero)):
    bin_abs(double_derived(r)) = double_spec(bin_abs(r))
{{
    trans(cong_bin_abs(BinNat::fold_law(Bin, BNil, λ a b => binc(binc(b)), r, h0)),
          double_abs_alg(bin_abs(r)))
}}

theorem double_derived_inv(r: Bin, h0: (Zero = Zero)): bin_inv(double_derived(r)) {{ refl }}

impl double_spec for BinNat {{
    body := double_derived,
    refines := double_derived_refines,
    refines_inv := double_derived_inv,
}}
"
    ));
}

/// Hand-run (a) of the repr-typed-result stage: the same transfer as the test
/// above, written in the spelling the *generator* uses — every law reached
/// through the record's namespace rather than through the fixture's own
/// theorems, the `inv` hypotheses each law demands supplied, and the third
/// lemma (`inv`-preservation of the fold) present even though `Bin`'s `inv` is
/// `True` and it could have been elided. This is the schema; the canonical-inv
/// hand-run below is the same schema where the third lemma has content.
#[test]
fn slow_acceptance_hand_run_the_generated_shape_for_a_repr_typed_result_at_bin() {
    ok(&format!(
        "{BIN_REPR}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}

fn double_spec_derived(n: Bin) -> Bin {{
    BinNat::fold(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), n)
}}

// The third lemma: the fold's accumulator satisfies `inv`, by induction over
// the spec value, one image closure law per constructor node.
theorem double_spec_inv_pres(x: Nat):
    BinNat::inv(BinNat::spec_rec(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), x))
{{
    match x {{
        Zero => BinNat::Zero_inv(),
        Succ(a0) => BinNat::Succ_inv(BinNat::mk_Succ(BinNat::spec_rec(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), a0)), BinNat::Succ_inv(BinNat::spec_rec(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), a0), double_spec_inv_pres(a0))),
    }}
}}

// `abs` pushed through the image spine, by induction: one commutation law per
// constructor node, a `j` chain over the recursive argument positions.
theorem double_spec_abs_alg(x: Nat):
    BinNat::abs(BinNat::spec_rec(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), x))
      = double_spec(x)
{{
    match x {{
        Zero => BinNat::Zero_abs(),
        Succ(a0) => trans(
            BinNat::Succ_abs(BinNat::mk_Succ(BinNat::spec_rec(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), a0)), BinNat::Succ_inv(BinNat::spec_rec(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), a0), double_spec_inv_pres(a0))),
            j(trans(
                BinNat::Succ_abs(BinNat::spec_rec(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), a0), double_spec_inv_pres(a0)),
                j(double_spec_abs_alg(a0),
                  λ y q => Succ(BinNat::abs(BinNat::spec_rec(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), a0))) = Succ(y),
                  refl)),
              λ y q => Succ(BinNat::abs(BinNat::mk_Succ(BinNat::spec_rec(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), a0)))) = Succ(y),
              refl)),
    }}
}}

theorem double_spec_derived_refines(n: Bin, h0: BinNat::inv(n)):
    BinNat::abs(double_spec_derived(n)) = double_spec(BinNat::abs(n))
{{
    trans(j(BinNat::fold_law(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), n, h0),
            λ y q => BinNat::abs(double_spec_derived(n)) = BinNat::abs(y),
            refl),
          double_spec_abs_alg(BinNat::abs(n)))
}}

theorem double_spec_derived_inv(n: Bin, h0: BinNat::inv(n)):
    BinNat::inv(double_spec_derived(n))
{{
    j(sym(BinNat::fold_law(Bin, BinNat::mk_Zero(), λ a0 b0 => BinNat::mk_Succ(BinNat::mk_Succ(b0)), n, h0)),
      λ y q => BinNat::inv(y),
      double_spec_inv_pres(BinNat::abs(n)))
}}

impl double_spec for BinNat {{
    body := double_spec_derived,
    refines := double_spec_derived_refines,
    refines_inv := double_spec_derived_inv,
}}
"
    ));
}

/// Hand-run (b): the same schema at a repr whose `inv` is a **canonical
/// form**, where the third lemma stops being `refl`. Every `inv` obligation
/// below is discharged by the chain of image closure laws applied to the
/// induction's hypothesis — at `Bin`'s `True` invariant the same terms check
/// but say nothing, which is why the stage needed this fixture before the
/// generator was written.
///
/// `sr` is bound only to keep the repeated recursor spelling honest; the
/// text is otherwise written out as the generator emits it.
#[test]
fn slow_acceptance_hand_run_a_repr_typed_result_where_inv_preservation_has_content() {
    let alg = "BinC::mk_Zero(), λ a0 b0 => BinC::mk_Succ(BinC::mk_Succ(b0))";
    let sr = |x: &str| format!("BinC::spec_rec(Bin, {alg}, {x})");
    let (sr_a0, sr_x) = (sr("a0"), sr("x"));
    ok(&format!(
        "{BIN_CANON}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}

fn double_spec_derived(n: Bin) -> Bin {{
    BinC::fold(Bin, BinC::mk_Zero(), λ a0 b0 => BinC::mk_Succ(BinC::mk_Succ(b0)), n)
}}

theorem double_spec_inv_pres(x: Nat): BinC::inv({sr_x}) {{
    match x {{
        Zero => BinC::Zero_inv(),
        Succ(a0) => BinC::Succ_inv(BinC::mk_Succ({sr_a0}), BinC::Succ_inv({sr_a0}, double_spec_inv_pres(a0))),
    }}
}}

theorem double_spec_abs_alg(x: Nat): BinC::abs({sr_x}) = double_spec(x) {{
    match x {{
        Zero => BinC::Zero_abs(),
        Succ(a0) => trans(
            BinC::Succ_abs(BinC::mk_Succ({sr_a0}), BinC::Succ_inv({sr_a0}, double_spec_inv_pres(a0))),
            j(trans(
                BinC::Succ_abs({sr_a0}, double_spec_inv_pres(a0)),
                j(double_spec_abs_alg(a0),
                  λ y q => Succ(BinC::abs({sr_a0})) = Succ(y), refl)),
              λ y q => Succ(BinC::abs(BinC::mk_Succ({sr_a0}))) = Succ(y), refl)),
    }}
}}

theorem double_spec_derived_refines(n: Bin, h0: BinC::inv(n)):
    BinC::abs(double_spec_derived(n)) = double_spec(BinC::abs(n))
{{
    trans(j(BinC::fold_law(Bin, BinC::mk_Zero(), λ a0 b0 => BinC::mk_Succ(BinC::mk_Succ(b0)), n, h0),
            λ y q => BinC::abs(double_spec_derived(n)) = BinC::abs(y), refl),
          double_spec_abs_alg(BinC::abs(n)))
}}

theorem double_spec_derived_inv(n: Bin, h0: BinC::inv(n)):
    BinC::inv(double_spec_derived(n))
{{
    j(sym(BinC::fold_law(Bin, BinC::mk_Zero(), λ a0 b0 => BinC::mk_Succ(BinC::mk_Succ(b0)), n, h0)),
      λ y q => BinC::inv(y),
      double_spec_inv_pres(BinC::abs(n)))
}}

impl double_spec for BinC {{
    body := double_spec_derived,
    refines := double_spec_derived_refines,
    refines_inv := double_spec_derived_inv,
}}
"
    ));
}

// -- the generator ---------------------------------------------------------

/// Generate, elaborate, kernel-check. The whole trust story: what comes back
/// is source, and it goes through the ordinary gate.
fn transfer(e: &mut Elaborator, op: &str, repr: &str) -> String {
    let em = match e.reprgen(op, repr) {
        Ok(em) => em,
        Err(r) => panic!("`{op}` at `{repr}` declined: {r}"),
    };
    // Generated text, elaborated as generated text: the emission spells the
    // minted names, which are not the surface
    // (docs/repr-access-spellings-design.md §6).
    if let Err(err) = e.elab_generated_source(&em.text) {
        panic!("emission for `{op}` did not check:\n{}\n{}", em.text, err.render(&em.text));
    }
    em.text
}

fn declines(e: &Elaborator, op: &str, repr: &str) -> String {
    match e.reprgen(op, repr) {
        Err(r) => r,
        Ok(_) => panic!("`{op}` at `{repr}` must decline"),
    }
}

#[test]
fn a_generated_transfer_of_length_checks_end_to_end() {
    let mut e = ok(&format!(
        "{LIST}
fn length(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => Succ(length(t)) }} }}
"
    ));
    let text = transfer(&mut e, "length", "ListTok");
    assert!(text.contains("fn length_derived"), "{text}");
    assert!(text.contains("theorem length_is_rec"), "{text}");
    assert!(text.contains("impl length for ListTok"), "{text}");
    assert_eq!(e.impl_global("ListTok", "length"), Some("ListTok_length_impl"));
}

/// The axes a generated-term test has to vary
/// (`docs/testing-generated-terms.md`), for a transfer: a **non-naive** repr
/// (`Bin`, where `abs` is a real computation and the derived body genuinely
/// folds over the representation), an **open** payload type (`Tok` is not the
/// carrier), **two** recursive children in one arm (the certificate's rewrite
/// chain has more than one link), an extra parameter carried through the
/// fold, and a **neutral** scrutinee throughout — the emitted `refines`
/// quantifies over a parameter, never a literal.
#[test]
fn generated_transfers_across_the_axes() {
    let mut e = ok(&format!(
        "{LIST}
inductive Tree {{ Leaf(n: Nat), Node(l: Tree, r: Tree) }}
datarepr TreeN for Tree := repr::naive();

fn add(a: Nat, b: Nat) -> Nat {{ match b {{ Zero => a, Succ(k) => Succ(add(a, k)) }} }}

fn tok_val(t: Tok) -> Nat {{ match t {{ TPush(n) => n, TAdd => Zero, TMul => Zero }} }}

// A payload field consumed by a foreign call, and a foreign combiner.
fn total(l: List<Tok>) -> Nat {{
    match l {{ Nil => Zero, Cons(h, t) => add(tok_val(h), total(t)) }}
}}

// An extra parameter, carried through the fold as part of the algebra.
fn length_from(k: Nat, l: List<Tok>) -> Nat {{
    match l {{ Nil => k, Cons(h, t) => Succ(length_from(k, t)) }}
}}

// TWO recursive children in one arm.
fn tsize(x: Tree) -> Nat {{
    match x {{ Leaf(n) => n, Node(l, r) => add(tsize(l), tsize(r)) }}
}}
"
    ));
    for (op, repr) in [("total", "ListTok"), ("length_from", "ListTok"), ("tsize", "TreeN")] {
        transfer(&mut e, op, repr);
        assert_eq!(
            e.impl_global(repr, op),
            Some(format!("{repr}_{op}_impl").as_str()),
            "{op} at {repr}"
        );
    }
}

#[test]
fn slow_acceptance_a_transfer_to_a_non_naive_repr_checks_end_to_end() {
    // `Bin`: `abs` is a real binary evaluation, so the derived body folds
    // over the representation and the certificate has content beyond `refl`.
    let mut e = ok(&format!(
        "{BIN_REPR}
inductive Ct {{ CZ, CS(p: Ct) }}
fn tally(n: Nat) -> Ct {{ match n {{ Zero => CZ, Succ(k) => CS(tally(k)) }} }}
"
    ));
    let text = transfer(&mut e, "tally", "BinNat");
    assert!(text.contains("Repr_BinNat::fold("), "{text}");
    assert_eq!(e.impl_global("BinNat", "tally"), Some("BinNat_tally_impl"));
}

/// The acceptance for the repr-typed-result stage: **arithmetic at `Bin`**,
/// generated. `double_spec` returns `Nat`, which is the repr'd type, so the
/// derived body's algebra is at the carrier and the certificate is the
/// image-spine induction rather than the recursor-unfolding one.
#[test]
fn slow_acceptance_arithmetic_at_bin_transfers_when_the_result_is_repr_typed() {
    let mut e = ok(&format!(
        "{BIN_REPR}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}
"
    ));
    let text = transfer(&mut e, "double_spec", "BinNat");
    assert!(text.contains("theorem double_spec_abs_alg"), "{text}");
    assert!(text.contains("theorem double_spec_inv_pres"), "{text}");
    assert!(text.contains("refines_inv := double_spec_derived_inv"), "{text}");
    // The body is built out of the constructor *images*, not the constructors.
    assert!(text.contains("Repr_BinNat::mk_Succ("), "{text}");
    assert_eq!(e.impl_global("BinNat", "double_spec"), Some("BinNat_double_spec_impl"));
    // The literal-scrutinee axis (`docs/testing-generated-terms.md`): the
    // derived body does not merely typecheck, it *computes* at the carrier —
    // doubling the representation of two yields a representation of four.
    let computes = "theorem double_at_two(): bin_abs(double_spec_derived(B0(B1(BNil)))) \
                      = Succ(Succ(Succ(Succ(Zero)))) { refl }";
    if let Err(err) = e.elab_source(computes) {
        panic!("the derived body does not compute: {}", err.render(computes));
    }
}

/// The same transfer at the canonical-form repr, where `inv` is not `True`:
/// every commutation law in the certificate is now paid for by the
/// `inv`-preservation lemma, which no longer holds by `refl`.
#[test]
fn slow_acceptance_a_repr_typed_result_transfers_at_a_repr_with_a_real_invariant() {
    let mut e = ok(&format!(
        "{BIN_CANON}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}
fn pred_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => pred_spec(k) }} }}
"
    ));
    let text = transfer(&mut e, "double_spec", "BinC");
    assert!(text.contains("Repr_BinC::Succ_inv("), "{text}");
    // An arm that is *only* the recursion: the spine bottoms out immediately,
    // so the certificate is the inductive hypothesis with nothing around it.
    transfer(&mut e, "pred_spec", "BinC");
    assert_eq!(e.impl_global("BinC", "pred_spec"), Some("BinC_pred_spec_impl"));
}

/// The four axes (`docs/testing-generated-terms.md`) for the repr-typed
/// result: an **open** payload type carried through the spine (`Tok`), a
/// constructor node with a non-recursive field beside the recursive one, an
/// extra parameter used *inside* the spine, two recursive children in one arm,
/// and a neutral scrutinee throughout (the emitted lemmas quantify).
#[test]
fn repr_typed_results_across_the_axes() {
    let mut e = ok(&format!(
        "{LIST}
inductive Tree {{ Leaf(n: Nat), Node(l: Tree, r: Tree) }}
datarepr TreeN for Tree := repr::naive();

// A node with a payload field beside the recursion, duplicated: the spine has
// two constructor nodes and the payload is spelled on both sides.
fn dup(l: List<Tok>) -> List<Tok> {{
    match l {{ Nil => Nil, Cons(h, t) => Cons(h, Cons(h, dup(t))) }}
}}

// An extra parameter, consumed inside the spine.
fn replace_all(k: Tok, l: List<Tok>) -> List<Tok> {{
    match l {{ Nil => Nil, Cons(h, t) => Cons(k, replace_all(k, t)) }}
}}

// TWO recursive children in one arm: the `j` chain has more than one link.
fn mirror(x: Tree) -> Tree {{
    match x {{ Leaf(n) => Leaf(n), Node(l, r) => Node(mirror(r), mirror(l)) }}
}}
"
    ));
    for (op, repr) in [("dup", "ListTok"), ("replace_all", "ListTok"), ("mirror", "TreeN")] {
        transfer(&mut e, op, repr);
        assert_eq!(
            e.impl_global(repr, op),
            Some(format!("{repr}_{op}_impl").as_str()),
            "{op} at {repr}"
        );
    }
}

/// The transfer machinery on top of a **defaulted** fold
/// (`issues/repr-fold-via-abs-default.md`): the generator consumes
/// `BinMin::fold()` and `fold_law()` without knowing that neither was
/// written, and the `Impl` it registers computes at the carrier.
#[test]
fn slow_acceptance_a_transfer_at_a_repr_whose_fold_is_defaulted() {
    let mut e = ok(&format!(
        "{BIN_MIN}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}
"
    ));
    let text = transfer(&mut e, "double_spec", "BinMin");
    assert!(text.contains("Repr_BinMin::fold("), "{text}");
    assert!(text.contains("refines_inv := double_spec_derived_inv"), "{text}");
    assert_eq!(e.impl_global("BinMin", "double_spec"), Some("BinMin_double_spec_impl"));
    // …and it computes: doubling the representation of two yields four.
    let computes = "theorem double_at_two(): bin_abs(double_spec_derived(B0(B1(BNil)))) \
                      = Succ(Succ(Succ(Succ(Zero)))) { refl }";
    if let Err(err) = e.elab_source(computes) {
        panic!("the derived body does not compute: {}", err.render(computes));
    }
}

// -- the fold-not-through-`abs` control point (§3.3, as-landed note 5) ------
//
// Every repr the suite had defines `fold` as `spec_rec ∘ abs`, which makes one
// thing in the certificate unobservable. `UnC` folds on the **carrier**.

#[test]
fn slow_acceptance_a_transfer_at_a_repr_whose_fold_is_not_through_abs() {
    let mut e = ok(&format!(
        "{UNARY_CANON}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}
"
    ));
    let text = transfer(&mut e, "double_spec", "UnC");
    assert!(text.contains("Repr_UnC::Succ_inv("), "{text}");
    assert_eq!(e.impl_global("UnC", "double_spec"), Some("UnC_double_spec_impl"));
    let computes = "theorem double_at_two(): un_abs(double_spec_derived(US(US(UZ)))) \
                      = Succ(Succ(Succ(Succ(Zero)))) { refl }";
    if let Err(err) = e.elab_source(computes) {
        panic!("the derived body does not compute: {}", err.render(computes));
    }
}

/// **The control §3.3's note 5 records as missing.** `refines_inv` transports
/// the `inv`-preservation lemma back across the anchor law, and the direction
/// of that transport is what `sym` supplies. At `Bin`/`BinC` deleting it still
/// checks — `fold` is defined through `abs` there, so both sides of `fold_law`
/// are convertible for an algebra that ignores the spec child. Here they are
/// two different stuck terms, and the mutation is refused.
#[test]
fn slow_acceptance_the_refines_inv_transport_direction_is_observable_when_fold_is_not_through_abs() {
    let mut e = ok(&format!(
        "{UNARY_CANON}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}
"
    ));
    let text = e.reprgen("double_spec", "UnC").expect("green emission").text;
    let bad = text.replacen("j(sym(", "j((", 1);
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "`refines_inv` transported in the wrong direction");
}

/// The other half of the same control, stated as a fact about the *old*
/// fixture rather than left implicit: at `BinC` the identical mutation checks.
/// Recording it keeps a future reader from "fixing" the note above.
#[test]
fn slow_acceptance_the_same_mutation_is_invisible_where_fold_is_defined_through_abs() {
    let (mut e, text) = base_double();
    let bad = text.replacen("j(sym(", "j((", 1);
    assert_ne!(bad, text, "the mutation must apply");
    if let Err(err) = e.elab_generated_source(&bad) {
        panic!(
            "the transport direction is expected to be UNOBSERVABLE at `BinC`; \
             if this now fails, design §3.3 note 5 has changed: {}",
            err.render(&bad)
        );
    }
}

// -- negative controls (§3.5) ----------------------------------------------
//
// The generator is untrusted, so what matters is that a wrong emission is
// *refused*, not that the generator is careful. Each control below mutates a
// green emission at one place and requires the pipeline to reject it — the
// certgen mutation-control discipline, at reprgen's scale.

fn base_length() -> (Elaborator, String) {
    let e = ok(&format!(
        "{LIST}
fn length(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => Succ(length(t)) }} }}
"
    ));
    let text = e.reprgen("length", "ListTok").expect("green emission").text;
    (e, text)
}

/// A perturbed — or hand-forced — *emission*, which must not check. Through
/// the generated entry point, so that the refusal is the mutation's and not the
/// surface's refusal to spell a generated name
/// (docs/repr-access-spellings-design.md §6): a control that passes for the
/// wrong reason is worse than no control.
/// …and refused for the *mutation*, not for the shape of the text it was cut
/// out of. A perturbation is a string edit on generated source, so a pattern
/// that has drifted from the emission can leave the text unparseable and the
/// control green for a reason that has nothing to do with the property it
/// names. The emission's style is now the idiomatic surface
/// (`issues/idiomatic-spelling-pass.md`), which is exactly the kind of move
/// that re-cuts these patterns, so the distinction is asserted rather than
/// assumed: a `ParseError` here is a broken control.
fn refused(e: &mut Elaborator, text: &str, what: &str) {
    match e.elab_generated_source(text) {
        Ok(()) => panic!("{what} elaborated, but it must be refused:\n{text}"),
        Err(heather_elab::ElabError::Parse(p)) => panic!(
            "{what} was refused by the PARSER, so this control proves nothing \
             about the mutation: {}\n{text}",
            p.msg
        ),
        Err(_) => {}
    }
}

#[test]
fn a_perturbed_derived_body_is_refused_by_its_own_refines() {
    // The algebra's step made the identity: the body still typechecks and
    // computes something, and `refines` is what catches it.
    let (mut e, text) = base_length();
    let bad = text.replace(
        "\u{3bb} h t b0 => Succ(b0)",
        "\u{3bb} h t b0 => b0",
    );
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a derived body that drops a `Succ`");
}

#[test]
fn slow_acceptance_a_perturbed_base_case_is_refused() {
    let (mut e, text) = base_length();
    // The derived body's base value only: `::fold(` does not match the
    // `::fold_law(` citation beside it, which quantifies over the same algebra.
    let bad = text.replace("::fold(Nat, Zero,", "::fold(Nat, Succ(Zero),");
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a derived body with the wrong base value");
}

#[test]
fn slow_acceptance_a_closing_lemma_over_the_wrong_statement_is_refused() {
    // The induction that links the spec fn to its recursor unfolding, aimed
    // at a different function: the proof term is unchanged and the statement
    // is a lie.
    let (mut e, text) = base_length();
    let bad = text.replace("= length(x)", "= Succ(length(x))");
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a closing lemma over the wrong statement");
}

#[test]
fn slow_acceptance_a_forced_emission_outside_the_fragment_fails_to_check() {
    // `stunted` reaches its recursive child directly instead of through the
    // recursion, so the generator declines it. Forcing the emission's *shape*
    // by hand — the fold with an algebra read off the arms — produces
    // something that does not check, which is the property the decline is
    // protecting. At `Bin` and not at the naive repr on purpose: the naive
    // carrier IS the spec type, so a body outside the fragment can still
    // happen to check there, and the control would prove nothing.
    let mut e = ok(&format!(
        "{BIN_REPR}
inductive Ct {{ CZ, CS(p: Ct) }}
fn tally(n: Nat) -> Ct {{ match n {{ Zero => CZ, Succ(k) => CS(tally(k)) }} }}
fn stunted(n: Nat) -> Ct {{ match n {{ Zero => CZ, Succ(k) => tally(k) }} }}
"
    ));
    let msg = declines(&e, "stunted", "BinNat");
    assert!(msg.contains("outside a self-call"), "{msg}");
    let forced = "
fn stunted_derived(n: Bin) -> Ct {
    Repr_BinNat::fold(Ct, CZ, λ k b0 => tally(k), n)
}
";
    refused(&mut e, forced, "a forced emission outside the fragment");
}

// -- controls for the repr-typed result, at a repr with a real `inv` --------
//
// All four run at `BinC` and not at a naive repr, for the reason the
// forced-emission control already records: the naive carrier IS the spec type,
// so a wrong artifact can still happen to check there.

fn base_double() -> (Elaborator, String) {
    let e = ok(&format!(
        "{BIN_CANON}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}
"
    ));
    let text = e.reprgen("double_spec", "BinC").expect("green emission").text;
    (e, text)
}

#[test]
fn slow_acceptance_a_perturbed_image_spine_is_refused() {
    // One `Succ` image dropped from the algebra, consistently everywhere: the
    // derived body still computes, the two closing lemmas are still about the
    // body that is there, and `refines` is what notices that it halves.
    let (mut e, text) = base_double();
    let bad = text.replace(
        "Repr_BinC::mk_Succ(Repr_BinC::mk_Succ(b0))",
        "Repr_BinC::mk_Succ(b0)",
    );
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a derived body one image short");
}

#[test]
fn slow_acceptance_a_perturbed_commutation_step_is_refused() {
    // The `j` motive of one link in the image chain no longer abstracts the
    // position it rewrites, so its `refl` no longer proves the base case.
    let (mut e, text) = base_double();
    let bad = text.replacen("= Succ(y), refl)", "= y, refl)", 1);
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a commutation step over the wrong motive");
}

#[test]
fn slow_acceptance_a_perturbed_inv_preservation_proof_is_refused() {
    // The inner closure law is applied to the accumulator instead of to the
    // image built on top of it: `inv` of the wrong term. Invisible at
    // `inv = True`, which is why this fixture exists.
    let (mut e, text) = base_double();
    let bad = text.replacen(
        "Repr_BinC::Succ_inv(Repr_BinC::mk_Succ(",
        "Repr_BinC::Succ_inv((",
        1,
    );
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "an `inv`-preservation proof at the wrong term");
}

#[test]
fn slow_acceptance_the_third_lemma_at_the_wrong_value_is_refused() {
    // `refines_inv` carries the `inv`-preservation lemma back across the
    // anchor law; aimed at a *literal* instead of at the value being folded,
    // it proves `inv` of something else.
    //
    // Deliberately not the mutation one would reach for first — dropping the
    // `sym` in that same proof — which this fixture cannot refuse: `Bin`'s
    // `fold` is *defined* through `abs`, so at an algebra that ignores the
    // spec child both sides of `fold_law` are convertible and the transport
    // direction is unobservable. The control is honest about what it controls.
    let (mut e, text) = base_double();
    let bad = text.replace(
        "double_spec_inv_pres(Repr_BinC::abs(n))",
        "double_spec_inv_pres(Zero)",
    );
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "the `inv`-preservation lemma at the wrong value");
}

#[test]
fn slow_acceptance_a_forced_repr_typed_emission_outside_the_fragment_fails_to_check() {
    // `pred_bad` hands back its recursive child, so the generator declines it.
    // Forcing the schema shows what the decline protects: the child is at the
    // carrier on the repr side and at `S` on the spec side, so the algebra the
    // closing lemma has to quantify over does not even typecheck.
    let mut e = ok(&format!(
        "{BIN_CANON}
fn pred_bad(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => k }} }}
"
    ));
    assert!(declines(&e, "pred_bad", "BinC").contains("outside a self-call"));
    let forced = "
fn pred_bad_derived(n: Bin) -> Bin {
    Repr_BinC::fold(Bin, Repr_BinC::mk_Zero(), λ k b0 => k, n)
}

theorem pred_bad_abs_alg(x: Nat):
    Repr_BinC::abs(BinC_spec_rec(Bin, Repr_BinC::mk_Zero(), λ k b0 => k, x))
      = pred_bad(x)
{ match x { Zero => Repr_BinC::Zero_abs(), Succ(k) => pred_bad_abs_alg(k), } }
";
    refused(&mut e, forced, "a forced repr-typed emission outside the fragment");
}

// -- declines (§3.3) -------------------------------------------------------

#[test]
fn slow_acceptance_the_decline_boundary_names_its_reasons() {
    let mut e = ok(&format!(
        "{LIST}
inductive Pair {{ P(a: Nat, b: Nat) }}
fn add(a: Nat, b: Nat) -> Nat {{ match b {{ Zero => a, Succ(k) => Succ(add(a, k)) }} }}
fn length(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => Succ(length(t)) }} }}
fn appended(x: List<Tok>, y: List<Tok>) -> Nat {{ Zero }}
fn tail_of(l: List<Tok>) -> List<Tok> {{ match l {{ Nil => Nil, Cons(h, t) => t }} }}
fn uses_tail(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => length(tail_of(Nil)) }} }}
fn not_a_match(l: List<Tok>) -> Nat {{ Zero }}
fn uses_child(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => length(t) }} }}
datarepr NatN for Nat := repr::naive();
fn zeroish(n: Nat) -> Nat {{ match n {{ Zero => 0, Succ(k) => Succ(zeroish(k)) }} }}
"
    ));
    for (op, frag) in [
        // A repr-typed result no longer declines *for being one* — but
        // `tail_of` hands back its recursive child, which is at the carrier on
        // the repr side and at `S` on the spec side, so it still declines. The
        // stage widened the fragment; it did not widen this.
        ("tail_of", "outside a self-call"),
        // Two parameters at `S`.
        ("appended", "two parameters at"),
        // Not a structural match at all.
        ("not_a_match", "not a structural `match`"),
        // A callee that touches the repr'd type is resolved against the
        // registry — and `tail_of` has no `Impl` and cannot be given one,
        // so the caller inherits the callee's decline, named as such.
        ("uses_tail", "and generating one declines"),
        // A recursive child reached outside a self-call.
        ("uses_child", "outside a self-call"),
    ] {
        let msg = declines(&e, op, "ListTok");
        assert!(msg.contains(frag), "`{op}`: {msg}");
    }
    // At a repr-typed result an arm has to be an *image spine*: `S`'s
    // constructors down to the self-calls. A numeral is not one — an honest
    // syntactic predicate, so it declines rather than desugaring.
    assert!(declines(&e, "zeroish", "NatN").contains("not an image spine"));
    // Unknown repr and unknown operation.
    assert!(declines(&e, "length", "Nope").contains("not a `datarepr`"));
    assert!(declines(&e, "nope", "ListTok").contains("not a declared function"));
    // A transfer never overwrites a hand override.
    transfer(&mut e, "length", "ListTok");
    assert!(declines(&e, "length", "ListTok").contains("already has an `Impl`"));
}

/// The fragment reads `ExprKind::Match`, and the parser desugars `split` onto
/// that node (docs/match-equation-split-design.md §6) — so a transfer body
/// written as a `split` is *admitted*, and used to be described back to its
/// author as a `match` (issues/diagnostics-name-the-written-form.md, the third
/// instance of that wart and the one in a subsystem neither of its rounds
/// touched). The admission is the positive half of this test; the wording is
/// the rest.
#[test]
fn slow_acceptance_a_split_bodied_transfer_is_admitted_and_declined_in_its_own_words() {
    let mut e = ok(&format!(
        "{LIST}
fn slength(l: List<Tok>) -> Nat {{
    split l;
    on Nil := Zero;
    on Cons(h, t) := Succ(slength(t));
}}
fn s_stmts(l: List<Tok>) -> Nat {{
    let z = Zero;
    split l;
    on Nil := z;
    on Cons(h, t) := z;
}}
fn s_other(l: List<Tok>, n: Nat) -> Nat {{
    split n;
    on Zero := Zero;
    on Succ(k) := Zero;
}}
fn s_default(l: List<Tok>) -> Nat {{
    split l;
    on _ := Zero;
}}
"
    ));
    // A `split` body transfers, exactly as its `match` spelling does.
    let text = transfer(&mut e, "slength", "ListTok");
    assert!(text.contains("fn slength_derived"), "{text}");
    assert_eq!(e.impl_global("ListTok", "slength"), Some("ListTok_slength_impl"));
    // The three declines that describe the body the author wrote.
    for (op, frag) in [
        ("s_stmts", "`s_stmts`'s body is not a bare `split`"),
        ("s_other", "`s_other` does not split on its `List<Tok>` parameter"),
        ("s_default", "`s_default`'s split has 1 arms for 2 constructors"),
    ] {
        let msg = declines(&e, op, "ListTok");
        assert!(msg.contains(frag), "`{op}`: {msg}");
        assert!(!msg.contains("match"), "`{op}` still says `match`: {msg}");
    }
}

/// The control the fix needs: hardcoding `split` would pass the test above.
/// The same three shapes spelled `match` are still described as a `match`.
#[test]
fn slow_acceptance_a_match_bodied_transfers_declines_still_name_match() {
    let e = ok(&format!(
        "{LIST}
fn m_stmts(l: List<Tok>) -> Nat {{
    let z = Zero;
    match l {{ Nil => z, Cons(h, t) => z }}
}}
fn m_other(l: List<Tok>, n: Nat) -> Nat {{
    match n {{ Zero => Zero, Succ(k) => Zero }}
}}
fn m_default(l: List<Tok>) -> Nat {{ match l {{ _ => Zero }} }}
"
    ));
    for (op, frag) in [
        ("m_stmts", "`m_stmts`'s body is not a bare `match`"),
        ("m_other", "`m_other` does not match on its `List<Tok>` parameter"),
        ("m_default", "`m_default`'s match has 1 arms for 2 constructors"),
    ] {
        let msg = declines(&e, op, "ListTok");
        assert!(msg.contains(frag), "`{op}`: {msg}");
        assert!(!msg.contains("split"), "`{op}` says `split`: {msg}");
    }
    // A body that is no case analysis at all has no spelling to name, so its
    // "not a structural `match`" is the shape the fragment REQUIRES rather
    // than a claim about what was written — which is why that one message is
    // not threaded. Pinned already by `not_a_match` in
    // `the_decline_boundary_names_its_reasons`.
}


// -- hand-runs for callee-`Impl` resolution (§3.1 phase 0's other half) ------

/// Hand-run (a): a callee that touches `S`, resolved against the registry, in
/// a transfer whose result is *not* repr-typed. Two callees at once, and
/// deliberately of different provenance — `length` would be generated,
/// `single` is a **hand override** (it takes no parameter at `S`, so no
/// transfer could produce it). The caller's certificate cannot tell them
/// apart: that indifference is the open registry's whole point (§1.2).
///
/// The load-bearing shape is `length(single(h))` — a callee whose result is at
/// `S` feeding a callee that consumes `S`, so the step is closed by `single`'s
/// `refines` *and* `refines_inv` chained into `length`'s `refines`.
#[test]
fn slow_acceptance_hand_run_a_transfer_over_resolved_callees() {
    ok(&format!(
        "{LIST}
fn add(a: Nat, b: Nat) -> Nat {{ match b {{ Zero => a, Succ(k) => Succ(add(a, k)) }} }}
fn length(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => Succ(length(t)) }} }}
fn single(t: Tok) -> List<Tok> {{ Cons(t, Nil) }}

// `length`'s `Impl`, in the shape the generator emits.
fn length_derived(r: List<Tok>) -> Nat {{
    ListTok::fold(Nat, Zero, λ a0 a1 b0 => Succ(b0), r)
}}

theorem length_is_rec(l: List<Tok>):
    ListTok::spec_rec(Nat, Zero, λ a0 a1 b0 => Succ(b0), l)
      = length(l)
{{ match l {{ Nil => refl, Cons(h, t) => cong_succ(length_is_rec(t)) }} }}

theorem length_derived_refines(r: List<Tok>, h0: True):
    length_derived(r) = length(ListTok::abs(r))
{{
    trans(ListTok::fold_law(Nat, Zero, λ a0 a1 b0 => Succ(b0), r, h0),
          length_is_rec(r))
}}

impl length for ListTok {{
    body := length_derived,
    refines := length_derived_refines,
}}

// `single`'s `Impl`, hand-written: a separate global that happens to agree.
fn single_impl(t: Tok) -> List<Tok> {{ Cons(t, Nil) }}
theorem single_impl_refines(t: Tok): ListTok::abs(single_impl(t)) = single(t) {{ refl }}
theorem single_impl_inv(t: Tok): ListTok::inv(single_impl(t)) {{ trivial }}

impl single for ListTok {{
    body := single_impl,
    refines := single_impl_refines,
    refines_inv := single_impl_inv,
}}

// The caller, and the transfer of it.
fn count(l: List<Tok>) -> Nat {{
    match l {{ Nil => Zero, Cons(h, t) => add(length(single(h)), count(t)) }}
}}

fn count_derived(l: List<Tok>) -> Nat {{
    ListTok::fold(Nat, Zero, λ h t b0 =>
        add(Impl(length, ListTok)::body(Impl(single, ListTok)::body(h)), b0), l)
}}

// The closing induction, with one rewrite per *site*: the callee step first
// (closed by the callees' own `refines`), then the recursive occurrence.
theorem count_is_rec(x: List<Tok>):
    ListTok::spec_rec(Nat, Zero, λ h t b0 =>
        add(Impl(length, ListTok)::body(Impl(single, ListTok)::body(h)), b0), x)
      = count(x)
{{
    match x {{
        Nil => refl,
        Cons(h, t) => trans(
            j(trans(Impl(length, ListTok)::refines(Impl(single, ListTok)::body(h))
                        (Impl(single, ListTok)::refines_inv(h)),
                    j(Impl(single, ListTok)::refines(h),
                      λ y q => length(ListTok::abs(Impl(single, ListTok)::body(h))) = length(y),
                      refl)),
              λ y q => add(Impl(length, ListTok)::body(Impl(single, ListTok)::body(h)),
                           ListTok::spec_rec(Nat, Zero, λ h t b0 =>
                               add(Impl(length, ListTok)::body(Impl(single, ListTok)::body(h)), b0), t))
                        = add(y,
                           ListTok::spec_rec(Nat, Zero, λ h t b0 =>
                               add(Impl(length, ListTok)::body(Impl(single, ListTok)::body(h)), b0), t)),
              refl),
            j(count_is_rec(t),
              λ y q => add(length(single(h)),
                           ListTok::spec_rec(Nat, Zero, λ h t b0 =>
                               add(Impl(length, ListTok)::body(Impl(single, ListTok)::body(h)), b0), t))
                        = add(length(single(h)), y),
              refl)),
    }}
}}

theorem count_derived_refines(l: List<Tok>, h0: ListTok::inv(l)):
    count_derived(l) = count(ListTok::abs(l))
{{
    trans(ListTok::fold_law(Nat, Zero, λ h t b0 =>
              add(Impl(length, ListTok)::body(Impl(single, ListTok)::body(h)), b0), l, h0),
          count_is_rec(ListTok::abs(l)))
}}

impl count for ListTok {{
    body := count_derived,
    refines := count_derived_refines,
}}
"
    ));
}

/// Hand-run (b): the `inv`-carrying case. `quad`'s result is at `S`, so its
/// arm is an image spine — and the spine now has a **callee node**: a
/// registered `Impl` applied to a value built on the recursion's own result.
///
/// This is where the charter's `inv` question is answered. A callee's
/// `refines` demands `inv` at each repr-typed argument, and every such
/// argument here is either an image (paid by the closure law) or the fold's
/// accumulator (paid by the transfer's own `inv`-preservation lemma). No
/// *hereditarity* law — `inv` of a child from `inv` of the whole — is asked
/// for anywhere, because a recursive child never reaches the repr side at all
/// (see the decline below). Run at `BinC`, where `inv` is a canonical form and
/// every one of those obligations has content.
#[test]
fn slow_acceptance_hand_run_a_resolved_callee_at_a_repr_with_a_real_invariant() {
    let alg = "BinC::mk_Zero(), λ k b0 => Impl(double_spec, BinC)::body(BinC::mk_Succ(b0))";
    let sr = |x: &str| format!("BinC::spec_rec(Bin, {alg}, {x})");
    let (sr_k, sr_x) = (sr("k"), sr("x"));
    let mut e = ok(&format!(
        "{BIN_CANON}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}
fn quad(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => double_spec(Succ(quad(k))) }} }}
"
    ));
    transfer(&mut e, "double_spec", "BinC");
    let src = format!(
        "
fn quad_derived(n: Bin) -> Bin {{
    BinC::fold(Bin, BinC::mk_Zero(), λ k b0 =>
        Impl(double_spec, BinC)::body(BinC::mk_Succ(b0)), n)
}}

theorem quad_inv_pres(x: Nat): BinC::inv({sr_x}) {{
    match x {{
        Zero => BinC::Zero_inv(),
        Succ(k) => Impl(double_spec, BinC)::refines_inv(BinC::mk_Succ({sr_k}))
                       (BinC::Succ_inv({sr_k}, quad_inv_pres(k))),
    }}
}}

theorem quad_abs_alg(x: Nat): BinC::abs({sr_x}) = quad(x) {{
    match x {{
        Zero => BinC::Zero_abs(),
        Succ(k) => trans(
            Impl(double_spec, BinC)::refines(BinC::mk_Succ({sr_k}))
                (BinC::Succ_inv({sr_k}, quad_inv_pres(k))),
            j(trans(BinC::Succ_abs({sr_k}, quad_inv_pres(k)),
                    j(quad_abs_alg(k), λ y q => Succ(BinC::abs({sr_k})) = Succ(y), refl)),
              λ y q => double_spec(BinC::abs(BinC::mk_Succ({sr_k}))) = double_spec(y),
              refl)),
    }}
}}

theorem quad_derived_refines(n: Bin, h0: BinC::inv(n)):
    BinC::abs(quad_derived(n)) = quad(BinC::abs(n))
{{
    trans(j(BinC::fold_law(Bin, BinC::mk_Zero(), λ k b0 =>
                Impl(double_spec, BinC)::body(BinC::mk_Succ(b0)), n, h0),
            λ y q => BinC::abs(quad_derived(n)) = BinC::abs(y), refl),
          quad_abs_alg(BinC::abs(n)))
}}

theorem quad_derived_inv(n: Bin, h0: BinC::inv(n)): BinC::inv(quad_derived(n)) {{
    j(sym(BinC::fold_law(Bin, BinC::mk_Zero(), λ k b0 =>
              Impl(double_spec, BinC)::body(BinC::mk_Succ(b0)), n, h0)),
      λ y q => BinC::inv(y),
      quad_inv_pres(BinC::abs(n)))
}}

impl quad for BinC {{
    body := quad_derived,
    refines := quad_derived_refines,
    refines_inv := quad_derived_inv,
}}
"
    );
    if let Err(err) = e.elab_source(&src) {
        panic!("the hand-run did not check:\n{}", err.render(&src));
    }
}

// -- generated transfers over resolved callees (§3.1 phase 0) ---------------

const COUNT: &str = "
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
fn length(l: List<Tok>) -> Nat { match l { Nil => Zero, Cons(h, t) => Succ(length(t)) } }
fn single(t: Tok) -> List<Tok> { Cons(t, Nil) }

// `single` takes no parameter at `List<Tok>`, so no transfer could ever
// produce its `Impl`: it is a hand override, and the caller's certificate is
// not allowed to care (§1.2, the open registry).
fn single_impl(t: Tok) -> List<Tok> { Cons(t, Nil) }
theorem single_impl_refines(t: Tok): ListTok::abs(single_impl(t)) = single(t) { refl }
theorem single_impl_inv(t: Tok): ListTok::inv(single_impl(t)) { trivial }
impl single for ListTok {
    body := single_impl,
    refines := single_impl_refines,
    refines_inv := single_impl_inv,
}

fn count(l: List<Tok>) -> Nat {
    match l { Nil => Zero, Cons(h, t) => add(length(single(h)), count(t)) }
}
";

/// The stage's acceptance at the naive repr: a transfer whose arm calls two
/// callees at `S` of **different provenance** — `single` hand-written,
/// `length` generated by a transfer of its own — chained (`length(single(h))`),
/// so the step is closed by `single`'s `refines` and `refines_inv` feeding
/// `length`'s `refines`.
#[test]
fn slow_acceptance_a_transfer_resolves_callees_of_either_provenance() {
    let mut e = ok(&format!("{LIST}{COUNT}"));
    transfer(&mut e, "length", "ListTok");
    let text = transfer(&mut e, "count", "ListTok");
    // Both callees reach the repr side through their `Impl`s, and neither
    // spec function survives in the derived body.
    assert!(text.contains("Impl_ListTok_length::body("), "{text}");
    assert!(text.contains("Impl_ListTok_single::body("), "{text}");
    // The certificate closes the step with the callees' own theorems.
    assert!(text.contains("Impl_ListTok_length::refines("), "{text}");
    assert!(text.contains("Impl_ListTok_single::refines_inv("), "{text}");
    assert_eq!(e.impl_global("ListTok", "count"), Some("ListTok_count_impl"));
}

/// The other half of phase 0: "a callee with no `Impl` is recursively a
/// generation target if in-fragment". `length` is *not* transferred first
/// here, so the emission has to contain both `Impl`s, the callee's before the
/// caller's — the topological order the doc asks for.
#[test]
fn slow_acceptance_a_missing_in_fragment_callee_is_generated_first() {
    let mut e = ok(&format!("{LIST}{COUNT}"));
    let text = transfer(&mut e, "count", "ListTok");
    let callee = text.find("impl length for ListTok").expect("the callee's `Impl`");
    let caller = text.find("impl count for ListTok").expect("the caller's `Impl`");
    assert!(callee < caller, "the callee's `Impl` must come first:\n{text}");
    // Both are registered by elaborating the one emission.
    assert_eq!(e.impl_global("ListTok", "length"), Some("ListTok_length_impl"));
    assert_eq!(e.impl_global("ListTok", "count"), Some("ListTok_count_impl"));
}

/// The same transfer, byte-for-byte, whichever way the callee's `Impl` got
/// there. This is the open registry's cost basis stated as a test: the
/// caller's certificate resolves four names and never asks who wrote them.
#[test]
fn slow_acceptance_the_callers_certificate_is_indifferent_to_how_the_callee_was_implemented() {
    let mut generated = ok(&format!("{LIST}{COUNT}"));
    transfer(&mut generated, "length", "ListTok");
    let over_generated = generated.reprgen("count", "ListTok").expect("green").text;

    // The same `length` `Impl`, written by hand instead — a different body
    // (`add(Succ(Zero), …)` where the transfer folds) with its own certificate.
    let mut handwritten = ok(&format!(
        "{LIST}{COUNT}
fn length_by_hand(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => Succ(length_by_hand(t)) }} }}
theorem length_by_hand_refines(l: List<Tok>, h0: ListTok::inv(l)):
    length_by_hand(l) = length(ListTok::abs(l))
{{ match l {{ Nil => refl, Cons(h, t) => cong_succ(length_by_hand_refines(t, h0)) }} }}
impl length for ListTok {{
    body := length_by_hand,
    refines := length_by_hand_refines,
}}
"
    ));
    let over_hand = handwritten.reprgen("count", "ListTok").expect("green").text;
    assert_eq!(over_generated, over_hand, "the caller's emission must not vary with provenance");
    if let Err(err) = handwritten.elab_generated_source(&over_hand) {
        panic!("the emission over a hand `Impl` did not check:\n{}", err.render(&over_hand));
    }
}

/// The `inv`-carrying case, generated: `hexa`'s result is at `S`, so its arm
/// is an image spine whose nodes are now **two callees** — `double_spec`
/// generated, `succ2` hand-written — wrapped around a constructor image over
/// the recursion's own result. Every `inv` hypothesis those `refines` demand
/// is paid by the node below it: the image's closure law, the callee's
/// `refines_inv`, or the transfer's own `inv`-preservation lemma at the
/// accumulator. At `BinC` none of them is `refl`.
const HEXA: &str = "
fn double_spec(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) } }

fn succ2(n: Nat) -> Nat { Succ(Succ(n)) }
fn succ2_bin(r: Bin) -> Bin { binc(binc(r)) }
theorem succ2_bin_refines(r: Bin, h0: bin_canon(r)): bin_abs(succ2_bin(r)) = succ2(bin_abs(r)) {
    trans(bin_succ_abs(binc(r)), cong_succ(bin_succ_abs(r)))
}
theorem succ2_bin_inv(r: Bin, h0: bin_canon(r)): bin_canon(succ2_bin(r)) {
    bin_canon_succ(binc(r), bin_canon_succ(r, h0))
}
impl succ2 for BinC {
    body := succ2_bin,
    refines := succ2_bin_refines,
    refines_inv := succ2_bin_inv,
}

fn hexa(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => succ2(double_spec(Succ(hexa(k)))) } }

// A recursive child handed to a resolved callee — the decline this stage did
// not lift.
fn pred_via(n: Nat) -> Nat { match n { Zero => Zero, Succ(k) => double_spec(k) } }
";

#[test]
fn slow_acceptance_resolved_callees_transfer_at_a_repr_with_a_real_invariant() {
    let mut e = ok(&format!("{BIN_CANON}{HEXA}"));
    // `double_spec` has no `Impl` and is in the fragment, so the transfer of
    // `hexa` generates it on the way — at the repr where `inv` has content.
    let text = transfer(&mut e, "hexa", "BinC");
    assert!(text.contains("Impl_BinC_succ2::refines("), "{text}");
    assert!(text.contains("Impl_BinC_succ2::refines_inv("), "{text}");
    assert!(text.contains("Impl_BinC_double_spec::refines("), "{text}");
    assert!(text.contains("Repr_BinC::Succ_inv("), "{text}");
    assert_eq!(e.impl_global("BinC", "double_spec"), Some("BinC_double_spec_impl"));
    assert_eq!(e.impl_global("BinC", "hexa"), Some("BinC_hexa_impl"));
    // The literal-scrutinee axis: the derived body *computes* at the carrier.
    // `hexa(k+1) = 2·hexa(k) + 4`, so `hexa(2) = 12` — computed at the
    // carrier, out of two callees' `Impl` bodies and a constructor image.
    let computes = "theorem hexa_at_two(): bin_abs(hexa_derived(B0(B1(BNil)))) = hexa(Succ(Succ(Zero))) { refl }";
    if let Err(err) = e.elab_source(computes) {
        panic!("the derived body does not compute: {}", err.render(computes));
    }
}

// -- mutation controls for the callee steps, at `BinC` ----------------------

fn base_hexa() -> (Elaborator, String) {
    let mut e = ok(&format!("{BIN_CANON}{HEXA}"));
    transfer(&mut e, "double_spec", "BinC");
    let text = e.reprgen("hexa", "BinC").expect("green emission").text;
    (e, text)
}

#[test]
fn slow_acceptance_a_callee_step_closed_by_the_wrong_callees_refines_is_refused() {
    let (mut e, text) = base_hexa();
    let bad = text.replace("Impl_BinC_succ2::refines(", "Impl_BinC_double_spec::refines(");
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a callee step closed by another callee's `refines`");
}

#[test]
fn slow_acceptance_a_callee_step_closed_at_the_wrong_argument_is_refused() {
    // `succ2`'s `refines` aimed one node down the spine: the equation it
    // proves is about the value its argument was built from, not the value.
    let (mut e, text) = base_hexa();
    let bad = text.replacen(
        "Impl_BinC_succ2::refines(Impl_BinC_double_spec::body(",
        "Impl_BinC_succ2::refines((",
        1,
    );
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a callee step closed at the wrong argument");
}

#[test]
fn slow_acceptance_a_callees_inv_hypothesis_paid_by_the_wrong_lemma_is_refused() {
    // A callee's `refines` demands `inv` at its repr-typed argument, and the
    // node below it pays. Paying with the *equation* instead of the invariant
    // is the mistake `inv = True` would hide, which is why this runs at `BinC`.
    let (mut e, text) = base_hexa();
    let bad =
        text.replacen("Impl_BinC_double_spec::refines_inv(", "Impl_BinC_double_spec::refines(", 1);
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "an `inv` hypothesis paid by the wrong lemma");
}

#[test]
fn slow_acceptance_a_forced_callee_at_a_recursive_child_fails_to_check() {
    // The decline this stage did *not* lift: a recursive child handed to a
    // resolved callee. The arm becomes the fold's algebra, which is spelled
    // once and typed twice — at the carrier for the fold and at `S` for the
    // anchor law's spec algebra — and a child binder has no reading that is
    // well-typed under both. Forcing the emission shows exactly that: the
    // closing lemma's statement does not even typecheck.
    let mut e = ok(&format!("{BIN_CANON}{HEXA}"));
    transfer(&mut e, "double_spec", "BinC");
    let msg = declines(&e, "pred_via", "BinC");
    assert!(msg.contains("outside a self-call"), "{msg}");
    let forced = "
theorem pred_via_abs_alg(x: Nat):
    Repr_BinC::abs(BinC_spec_rec(Bin, Repr_BinC::mk_Zero(),
        λ k b0 => Impl_BinC_double_spec::body(k), x))
      = pred_via(x)
{ match x { Zero => Repr_BinC::Zero_abs(), Succ(k) => pred_via_abs_alg(k), } }
";
    refused(&mut e, forced, "a forced emission handing a recursive child to a callee");
}

/// The `S` parameter first, not last: the self-call's recursive child is read
/// at the **recursion parameter's index**, so an operation whose repr'd
/// parameter is not the last one transfers instead of being blamed for
/// non-structural recursion (`issues/reprgen-self-call-args-unchecked.md`'s
/// sibling case). The declaration-order fix landed the emission side of this;
/// this is the reader side.
#[test]
fn slow_acceptance_the_recursive_child_is_read_at_the_recursion_parameters_index() {
    let mut e = ok(&format!(
        "{LIST}
fn length_at(l: List<Tok>, k: Nat) -> Nat {{
    match l {{ Nil => k, Cons(h, t) => Succ(length_at(t, k)) }}
}}
"
    ));
    transfer(&mut e, "length_at", "ListTok");
    assert_eq!(e.impl_global("ListTok", "length_at"), Some("ListTok_length_at_impl"));
}

#[test]
fn slow_acceptance_the_callee_decline_boundary_names_its_reasons() {
    let e = ok(&format!(
        "{BIN_CANON}{HEXA}
// An arm that mentions the value being matched.
fn sees_scrutinee(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => double_spec(n) }} }}
"
    ));
    for (op, frag) in [
        ("pred_via", "outside a self-call"),
        ("sees_scrutinee", "mentions the scrutinee"),
    ] {
        let msg = declines(&e, op, "BinC");
        assert!(msg.contains(frag), "`{op}`: {msg}");
    }
}
