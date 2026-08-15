//! `reprgen` — derived `Impl`s for structural spec fns over repr'd types
//! (`docs/datarepr-design.md` §3, §5.1 item 5).
//!
//! The hand-run comes first (the discipline `docs/certgen-*-design.md` calls
//! hand-run-first): the artifacts below are written by hand in exactly the
//! shape the generator emits, so that what the generator has to produce is
//! known to be checkable before anything produces it.

use heather_elab::Elaborator;

mod support;
use support::BIN_REPR;

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
fn hand_run_a_derived_impl_over_the_naive_list_repr() {
    ok(&format!(
        "{LIST}
fn length(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => Succ(length(t)) }} }}

// Phase 2: the structural match becomes the anchor fold, with the algebra
// read off the arms and the recursive occurrence at the accumulator slot.
fn length_derived(r: List<Tok>) -> Nat {{
    Repr_ListTok::fold()(Nat)(Zero)(λ (a0: Tok) => λ (a1: List<Tok>) => λ (b0: Nat) => Succ(b0))(r)
}}

// Phase 4, part one: the spec fn agrees with its own recursor unfolding.
// NOT definitional — both sides are recursive globals — so this is an
// induction the generator has to emit.
theorem length_is_rec(l: List<Tok>):
    ListTok_spec_rec(Nat, Zero, λ (a0: Tok) => λ (a1: List<Tok>) => λ (b0: Nat) => Succ(b0), l)
      = length(l)
{{ match l {{ Nil => refl, Cons(h, t) => cong_succ(length_is_rec(t)) }} }}

// Phase 4, part two: `fold_law` opens the anchor, the lemma above closes it.
theorem length_derived_refines(r: List<Tok>, h0: (Zero = Zero)):
    length_derived(r) = length(Repr_ListTok::abs()(r))
{{
    trans(Repr_ListTok::fold_law()(Nat)(Zero)
            (λ (a0: Tok) => λ (a1: List<Tok>) => λ (b0: Nat) => Succ(b0))(r)(h0),
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
fn hand_run_a_derived_impl_at_bin_where_the_result_is_the_spec_type() {
    ok(&format!(
        "{BIN_REPR}
fn double_spec(n: Nat) -> Nat {{ match n {{ Zero => Zero, Succ(k) => Succ(Succ(double_spec(k))) }} }}

fn double_derived(r: Bin) -> Bin {{
    Repr_BinNat::fold()(Bin)(BNil)(λ (a0: Bin) => λ (b0: Bin) => binc(binc(b0)))(r)
}}

// `abs` pushed through the algebra, by induction, on the image law.
theorem double_abs_alg(n: Nat):
    bin_abs(BinNat_spec_rec(Bin, BNil, λ (a: Nat) => λ (b: Bin) => binc(binc(b)), n))
      = double_spec(n)
{{
    match n {{
        Zero => refl,
        Succ(k) => trans(
            bin_succ_abs(binc(BinNat_spec_rec(Bin, BNil, λ (a: Nat) => λ (b: Bin) => binc(binc(b)), k))),
            cong_succ(trans(
                bin_succ_abs(BinNat_spec_rec(Bin, BNil, λ (a: Nat) => λ (b: Bin) => binc(binc(b)), k)),
                cong_succ(double_abs_alg(k))))),
    }}
}}

theorem double_derived_refines(r: Bin, h0: (Zero = Zero)):
    bin_abs(double_derived(r)) = double_spec(bin_abs(r))
{{
    trans(cong_bin_abs(Repr_BinNat::fold_law()(Bin)(BNil)
             (λ (a: Nat) => λ (b: Bin) => binc(binc(b)))(r)(h0)),
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

// -- the generator ---------------------------------------------------------

/// Generate, elaborate, kernel-check. The whole trust story: what comes back
/// is source, and it goes through the ordinary gate.
fn transfer(e: &mut Elaborator, op: &str, repr: &str) -> String {
    let em = match e.reprgen(op, repr) {
        Ok(em) => em,
        Err(r) => panic!("`{op}` at `{repr}` declined: {r}"),
    };
    if let Err(err) = e.elab_source(&em.text) {
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
fn a_transfer_to_a_non_naive_repr_checks_end_to_end() {
    // `Bin`: `abs` is a real binary evaluation, so the derived body folds
    // over the representation and the certificate has content beyond `refl`.
    let mut e = ok(&format!(
        "{BIN_REPR}
inductive Ct {{ CZ, CS(p: Ct) }}
fn tally(n: Nat) -> Ct {{ match n {{ Zero => CZ, Succ(k) => CS(tally(k)) }} }}
"
    ));
    let text = transfer(&mut e, "tally", "BinNat");
    assert!(text.contains("Repr_BinNat::fold()"), "{text}");
    assert_eq!(e.impl_global("BinNat", "tally"), Some("BinNat_tally_impl"));
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

fn refused(e: &mut Elaborator, text: &str, what: &str) {
    if e.elab_source(text).is_ok() {
        panic!("{what} elaborated, but it must be refused:\n{text}");
    }
}

#[test]
fn a_perturbed_derived_body_is_refused_by_its_own_refines() {
    // The algebra's step made the identity: the body still typechecks and
    // computes something, and `refines` is what catches it.
    let (mut e, text) = base_length();
    let bad = text.replace(
        "λ (b0: Nat) => Succ(b0)",
        "λ (b0: Nat) => b0",
    );
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a derived body that drops a `Succ`");
}

#[test]
fn a_perturbed_base_case_is_refused() {
    let (mut e, text) = base_length();
    let bad = text.replace("(Zero)(", "(Succ(Zero))(");
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a derived body with the wrong base value");
}

#[test]
fn a_closing_lemma_over_the_wrong_statement_is_refused() {
    // The induction that links the spec fn to its recursor unfolding, aimed
    // at a different function: the proof term is unchanged and the statement
    // is a lie.
    let (mut e, text) = base_length();
    let bad = text.replace("= length(x)", "= Succ(length(x))");
    assert_ne!(bad, text, "the mutation must apply");
    refused(&mut e, &bad, "a closing lemma over the wrong statement");
}

#[test]
fn a_forced_emission_outside_the_fragment_fails_to_check() {
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
    Repr_BinNat::fold()(Ct)(CZ)(λ (k: Bin) => λ (b0: Ct) => tally(k))(n)
}
";
    refused(&mut e, forced, "a forced emission outside the fragment");
}

// -- declines (§3.3) -------------------------------------------------------

#[test]
fn the_decline_boundary_names_its_reasons() {
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
"
    ));
    for (op, frag) in [
        // The result at the repr'd type — the round's named deferral.
        ("tail_of", "result is repr-typed"),
        // Two parameters at `S`.
        ("appended", "two parameters at"),
        // Not a structural match at all.
        ("not_a_match", "not a structural `match`"),
        // A callee that touches the repr'd type needs its own `Impl`.
        ("uses_tail", "has to be resolved against the `Impl` registry"),
        // A recursive child reached outside a self-call.
        ("uses_child", "outside a self-call"),
    ] {
        let msg = declines(&e, op, "ListTok");
        assert!(msg.contains(frag), "`{op}`: {msg}");
    }
    // Unknown repr and unknown operation.
    assert!(declines(&e, "length", "Nope").contains("not a `datarepr`"));
    assert!(declines(&e, "nope", "ListTok").contains("not a declared function"));
    // A transfer never overwrites a hand override.
    transfer(&mut e, "length", "ListTok");
    assert!(declines(&e, "length", "ListTok").contains("already has an `Impl`"));
}
