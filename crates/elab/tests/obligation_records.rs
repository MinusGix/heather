//! The obligation-record surface: inline clause expressions, the `?` reporting
//! hole, and the two routes (`docs/obligation-records-design.md`).
//!
//! Everything here is a *generated term* in the sense of
//! `docs/testing-generated-terms.md` — the record type, the obligation
//! statements and (for the routes) the whole certificate are synthesized — so
//! the four axes are varied deliberately: an **open** element type (`List<Tok>`
//! at the naive repr, whose payload is not the carrier) beside a **non-naive**
//! one (`Bin`, where `abs` computes); a **neutral** scrutinee everywhere (every
//! obligation quantifies over a parameter, never a literal); a **checking**
//! position (an inline clause is checked against the synthesized field type and
//! nothing else); and a **negative control** beside each positive.

use heather_elab::Elaborator;

mod support;
use support::{BIN_ADD, BIN_CANON, BIN_MIN, BIN_REPR};

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
datarepr ListTok for List<Tok> := repr::naive();
fn length(l: List<Tok>) -> Nat { match l { Nil => Zero, Cons(h, t) => Succ(length(t)) } }
";

// -- step 2: inline clause expressions (§4.2) -------------------------------

/// An inline λ body and an inline proof at `refines`, at the **open** element
/// type. Before the splice both cost a top-level `fn` and a top-level
/// `theorem`; the clause is in checking position either way, which is what the
/// `refl` at `refines` relies on.
#[test]
fn an_inline_lambda_body_and_an_inline_proof() {
    ok(&format!(
        "{LIST}
impl length for ListTok {{
    body := \u{3bb} r => length(r),
    refines := \u{3bb} r h0 => refl,
}}
"
    ));
}

/// An inline `match` body — the shape `spell_expr` declined on, and the one a
/// tuned implementation actually has. Its `refines` is `refl` because the
/// clause is checked by *conversion*: the spec fn δ-unfolds to the same match.
#[test]
fn an_inline_match_body() {
    let e = ok(&format!(
        "{LIST}
fn nonempty(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => Succ(Zero) }} }}
impl nonempty for ListTok {{
    body := \u{3bb} r => match r {{ Nil => Zero, Cons(h, t) => Succ(Zero) }},
    refines := \u{3bb} r h0 => refl,
}}
"
    ));
    assert_eq!(e.impl_global("ListTok", "nonempty"), Some("ListTok_nonempty_impl"));
}

/// An inline `let`-block body, and an inline proof that is a `let`-block too.
#[test]
fn an_inline_let_block_body() {
    ok(&format!(
        "{LIST}
impl length for ListTok {{
    body := {{ let f: (l: List<Tok>) -> Nat = length; f }},
    refines := \u{3bb} r h0 => refl,
}}
"
    ));
}

/// An inline clause at the **non-naive** repr, where `abs` is a real
/// computation and the proof has content: `add` at `Bin`.
#[test]
fn an_inline_clause_at_bin() {
    ok(&format!(
        "{BIN_REPR}{BIN_ADD}
impl add for BinNat {{
    body := \u{3bb} ra rb => bin_add_derived(ra, rb),
    refines := \u{3bb} ra rb h0 h1 => bin_iter_abs(ra, bin_abs(rb)),
    refines_inv := \u{3bb} ra rb h0 h1 => refl,
}}
"
    ));
}

/// The negative control for the whole splice: a wrong inline proof is refused
/// by the **kernel**, not by the printer — the failure is a conversion failure
/// against the synthesized statement, which is the only thing that makes the
/// widening safe.
#[test]
fn a_wrong_inline_proof_is_refused_by_the_kernel() {
    let msg = bad(&format!(
        "{LIST}
impl length for ListTok {{
    body := \u{3bb} r => Succ(length(r)),
    refines := \u{3bb} r h0 => refl,
}}
"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
}

/// …and it is reported at the **clause**, not at the block: the span the round
/// moved the diagnostic to (§2.3).
#[test]
fn an_inline_failure_is_located_at_the_clause() {
    let msg = bad(&format!(
        "{LIST}
impl length for ListTok {{
    body := \u{3bb} r => Succ(length(r)),
    refines := \u{3bb} r h0 => refl,
}}
"
    ));
    assert!(msg.contains("clause `refines`"), "{msg}");
    // The obligation is still quoted: the field's statement is exactly what is
    // not obvious about a failure here.
    assert!(msg.contains("in the generated declaration"), "{msg}");
}

/// An inline clause in a `datarepr`, the second customer (§5): the closure law
/// `BinC` proves by hand, written where it is owed.
#[test]
fn an_inline_datarepr_clause_law() {
    let src = BIN_CANON.replace(
        "    Succ_inv := bin_canon_succ,",
        "    Succ_inv := \u{3bb} a0 h0 => bin_canon_succ(a0, h0),",
    );
    assert!(src.contains("\u{3bb} a0 h0 =>"), "the fixture moved");
    ok(&src);
}

/// The carrier is the one clause that is still *spelled*: it stands in type
/// position throughout the generated source, so it cannot be an arbitrary
/// expression, and the decline says so.
#[test]
fn the_carrier_clause_is_still_spelled() {
    let msg = bad(&BIN_REPR.replace("    R := Bin,", "    R := \u{3bb} x => Bin,"));
    assert!(msg.contains("carrier and stands in"), "{msg}");
}

// -- step 3: `?`, the reporting hole (§1.2) ---------------------------------

#[test]
fn a_hole_at_refines_reports_the_obligation_and_fails() {
    let msg = bad(&format!(
        "{BIN_REPR}{BIN_ADD}
impl add for BinNat {{
    body := bin_add_derived,
    refines := ?,
    refines_inv := bin_add_derived_inv,
}}
"
    ));
    // The owner, the `::` path (print-only, §3), and the statement — spelled in
    // the generated vocabulary the kernel will compare against.
    assert!(msg.contains("`refines` of `impl add for BinNat` is not proved"), "{msg}");
    assert!(msg.contains("Impl(add, BinNat)::refines"), "{msg}");
    assert!(msg.contains("(a: Bin) -> (b: Bin) -> (h0: BinNat::inv(a))"), "{msg}");
    assert!(msg.contains("= add(BinNat::abs(a), BinNat::abs(b))"), "{msg}");
}

#[test]
fn a_labelled_hole_names_its_label() {
    let msg = bad(&format!(
        "{BIN_REPR}{BIN_ADD}
impl add for BinNat {{
    body := bin_add_derived,
    refines := ?later,
    refines_inv := bin_add_derived_inv,
}}
"
    ));
    assert!(msg.contains("labelled `later`"), "{msg}");
}

/// The second customer's hole: a law of a `datarepr`, at `BinC`, where the
/// statement genuinely consumes its `inv` hypothesis.
#[test]
fn a_hole_at_a_datarepr_law_reports_the_law() {
    let msg = bad(&BIN_CANON.replace("    Succ_inv := bin_canon_succ,", "    Succ_inv := ?,"));
    assert!(msg.contains("`Succ_inv` of `datarepr BinC` is not proved"), "{msg}");
    assert!(msg.contains("BinC::Succ_inv"), "{msg}");
    assert!(msg.contains("(a0: Bin) -> (h0: BinC::inv(a0))"), "{msg}");
    assert!(msg.contains("BinC::inv(BinC::mk_Succ(a0))"), "{msg}");
}

/// Omission keeps meaning *take the default* — the rule the defaults round
/// inherits (§1.2, FINDING C dissolved). `BIN_REPR` omits `Zero_abs`,
/// `Zero_inv` and `Succ_inv`, and checks.
#[test]
fn omission_still_defaults() {
    ok(BIN_REPR);
}

/// A `?` and an omission never blur, now that `fold` has a default
/// (`issues/repr-fold-via-abs-default.md`): omitting `fold` takes the via-abs
/// default, and writing `fold := ?` still reports — as the data-field error,
/// because a fold is not an obligation whose statement could be printed.
#[test]
fn a_hole_at_fold_reports_rather_than_taking_the_default() {
    let msg = bad(&BIN_MIN.replace("    mk Zero := BNil,", "    fold := ?,\n    mk Zero := BNil,"));
    assert!(msg.contains("is not an obligation"), "{msg}");
    assert!(msg.contains("fold"), "{msg}");
}

/// …and a `?` at the *law* of a defaulted fold prints the statement that fold
/// anchors, naming the generated `BinMin::fold()` — which is how an author
/// discovers what the default committed them to.
#[test]
fn a_hole_at_the_law_of_a_defaulted_fold_prints_the_anchor() {
    let msg =
        bad(&BIN_MIN.replace("    mk Zero := BNil,", "    fold_law := ?,\n    mk Zero := BNil,"));
    assert!(msg.contains("`fold_law` of `datarepr BinMin` is not proved"), "{msg}");
    assert!(msg.contains("BinMin::fold("), "{msg}");
    assert!(msg.contains("BinMin::spec_rec"), "{msg}");
}

/// A `?` at a data field is an error that says why: the statements are computed
/// *from* the data (§1.1).
#[test]
fn a_hole_at_a_data_field_says_it_is_not_an_obligation() {
    let msg = bad(&format!(
        "{LIST}
impl length for ListTok {{ body := ?, refines := length_refines }}
"
    ));
    assert!(msg.contains("is not an obligation"), "{msg}");
}

// -- step 4: the routes (§4.3) ----------------------------------------------

/// **The first transfer ever requested from surface source.** The declaration
/// runs the generator, the emission goes through the ordinary gate, and the
/// registry entry it installs is the transfer's own.
#[test]
fn derive_requests_a_transfer_from_surface_source() {
    let e = ok(&format!("{LIST}\nimpl length for ListTok := derive();\n"));
    assert_eq!(e.impl_global("ListTok", "length"), Some("ListTok_length_impl"));
    assert_eq!(
        e.impl_provenance_of("ListTok", "length").map(|p| p.as_str()),
        Some("derived")
    );
}

/// …and the certificate it installs is consumable: a later transfer resolves
/// `length` as a **callee** through the registry, exactly as it would a
/// hand-written `Impl` (design §9's last bullet — the registry has one entry
/// per key whatever produced it).
#[test]
fn a_surface_derived_impl_is_consumable_as_a_callee() {
    let mut e = ok(&format!(
        "{LIST}
fn add(a: Nat, b: Nat) -> Nat {{ match b {{ Zero => a, Succ(k) => Succ(add(a, k)) }} }}
fn single(t: Tok) -> List<Tok> {{ Cons(t, Nil) }}
theorem single_refines(t: Tok): ListTok::abs(single(t)) = single(t) {{ refl }}
theorem single_inv(t: Tok): ListTok::inv(single(t)) {{ trivial }}
impl single for ListTok {{
    body := single, refines := single_refines, refines_inv := single_inv,
}}

fn count(l: List<Tok>) -> Nat {{
    match l {{ Nil => Zero, Cons(h, t) => add(length(single(h)), count(t)) }}
}}

impl length for ListTok := derive();
"
    ));
    let em = match e.reprgen("count", "ListTok") {
        Ok(em) => em,
        Err(why) => panic!("the callee's surface-derived `Impl` did not resolve: {why}"),
    };
    // Resolved through the registry, not regenerated: the caller's certificate
    // asks for four names and never asks who wrote them.
    assert!(em.text.contains("Impl_ListTok_length::refines("), "{}", em.text);
    assert!(!em.text.contains("impl length for ListTok"), "{}", em.text);
    if let Err(err) = e.elab_generated_source(&em.text) {
        panic!("{}", err.render(&em.text));
    }
}

/// A declined `derive()` reports the generator's reason **verbatim**, which is
/// what lets a tool tell "the fragment does not cover this" from "you have not
/// proved it yet" (§6).
#[test]
fn a_declined_derive_reports_the_generators_reason() {
    let msg = bad(&format!(
        "{LIST}
fn constant(l: List<Tok>) -> Nat {{ Zero }}
impl constant for ListTok := derive();
"
    ));
    assert!(msg.contains("declines:"), "{msg}");
    assert!(msg.contains("is not a bare `match`") || msg.contains("structural `match`"), "{msg}");
}

/// `via_derived(p)` at a result that is **not** the spec type: the obligation is
/// the equation between this body and the derived one, and the certificate is
/// composed by `trans`.
#[test]
fn via_derived_composes_at_a_plain_result() {
    let e = ok(&format!(
        "{LIST}
impl length for ListTok {{
    body := \u{3bb} r => length(r),
    refines := via_derived(\u{3bb} r h0 =>
        sym(length_derived_refines(r, h0))),
}}
"
    ));
    assert_eq!(
        e.impl_provenance_of("ListTok", "length").map(|p| p.as_str()),
        Some("via")
    );
}

/// The same route at a **repr-typed** result, at `Bin`: `double` implemented by
/// a left shift, certified against the derived fold. This is probe 6's shape,
/// generated rather than hand-written.
#[test]
fn via_derived_composes_at_bin_with_a_repr_typed_result() {
    ok(&format!(
        "{BIN_REPR}
impl double for BinNat {{
    body := \u{3bb} r => B0(r),
    refines := via_derived(\u{3bb} r h0 =>
        sym(double_derived_refines(r, h0))),
    refines_inv := \u{3bb} r h0 => refl,
}}
"
    ));
}

/// …and if `refines_inv` is left out there, the error **says why** the route
/// cannot fill it: an abs-image equation says nothing about `inv` of what was
/// built, which is what a non-injective `abs` costs (§4.3).
#[test]
fn via_derived_does_not_fill_refines_inv_and_says_why() {
    let msg = bad(&format!(
        "{BIN_REPR}
impl double for BinNat {{
    body := \u{3bb} r => B0(r),
    refines := via_derived(\u{3bb} r h0 =>
        sym(double_derived_refines(r, h0))),
}}
"
    ));
    assert!(msg.contains("`via_derived` cannot fill it"), "{msg}");
    assert!(msg.contains("non-injective `abs`"), "{msg}");
}

/// The negative control for `via_derived`: a wrong equivalence proof is refused
/// by the kernel against the *synthesized* obligation, not accepted because the
/// route composed it.
#[test]
fn a_wrong_via_derived_proof_is_refused() {
    let msg = bad(&format!(
        "{LIST}
impl length for ListTok {{
    body := \u{3bb} r => Succ(length(r)),
    refines := via_derived(\u{3bb} r h0 =>
        sym(length_derived_refines(r, h0))),
}}
"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
}

/// A route that is not a route is not silently a name: the `:=` body form takes
/// `derive()` and nothing else in v1.
#[test]
fn an_unknown_route_is_refused() {
    let msg = bad(&format!("{LIST}\nimpl length for ListTok := magic();\n"));
    assert!(msg.contains("is not a route this round knows"), "{msg}");
}

// -- step 5: the obligations listing (§6) -----------------------------------

#[test]
fn the_listing_records_state_provenance_and_statement() {
    let e = ok(&format!(
        "{LIST}
impl length for ListTok {{
    body := \u{3bb} r => length(r),
    refines := \u{3bb} r h0 => refl,
}}
"
    ));
    let rows = e.obligations();
    // The `datarepr`'s own laws come first, then the `impl`'s.
    let repr_law = rows
        .iter()
        .find(|o| o.owner == "datarepr ListTok" && o.field == "Cons_abs")
        .expect("the repr's commutation law is an obligation");
    assert_eq!(repr_law.state, "defaulted");
    assert_eq!(repr_law.provenance, None);
    assert_eq!(repr_law.path, "ListTok::Cons_abs");

    let refines = rows
        .iter()
        .find(|o| o.owner == "impl length for ListTok" && o.field == "refines")
        .expect("the impl's `refines` is an obligation");
    assert_eq!(refines.state, "supplied");
    assert_eq!(refines.provenance.map(|p| p.as_str()), Some("inline"));
    assert_eq!(refines.path, "Impl(length, ListTok)::refines");
    assert!(refines.statement.contains("= length(ListTok::abs(l))"), "{}", refines.statement);
}

/// The two data clauses that have a default are listed too, so the listing
/// answers the question the defaults created: did this repr write its `fold`
/// and its `inv`, or take them (`issues/repr-fold-via-abs-default.md`)?
#[test]
fn the_listing_says_which_defaultable_data_clauses_were_taken() {
    let min = ok(BIN_MIN);
    let at = |e: &Elaborator, owner: &str, field: &str| {
        let o = e
            .obligations()
            .iter()
            .find(|o| o.owner == owner && o.field == field)
            .unwrap_or_else(|| panic!("no row for {owner} / {field}"))
            .clone();
        (o.state, o.provenance.map(|p| p.as_str()), o.statement)
    };
    let (state, prov, stmt) = at(&min, "datarepr BinMin", "fold");
    assert_eq!((state, prov), ("defaulted", None));
    // The statement of a data clause is the type it is checked against.
    assert!(stmt.starts_with("(B: Type) -> "), "{stmt}");
    assert_eq!(at(&min, "datarepr BinMin", "inv").0, "defaulted");
    // …and a repr that writes both says so.
    let written = ok(BIN_REPR);
    let (state, prov, _) = at(&written, "datarepr BinNat", "fold");
    assert_eq!((state, prov), ("supplied", Some("named")));
    let (state, prov, _) = at(&written, "datarepr BinNat", "inv");
    assert_eq!((state, prov), ("supplied", Some("named")));
}

/// Also the **ascription interim** (§2.2, FINDING F): the surface has no
/// expression ascription, so an author who wants the statement visible states
/// it as a named theorem in their *own* vocabulary — `my_len(r) = length(r)`,
/// not the generated `Impl_ListTok_length::body(r) =
/// length(ListTok::abs(r))` — and the field type accepts it by
/// conversion. That it works is probe 4's δ row, here as a test.
#[test]
fn the_listing_distinguishes_named_from_inline_and_derived() {
    let e = ok(&format!(
        "{LIST}
fn my_len(r: List<Tok>) -> Nat {{ length(r) }}
theorem my_len_refines(r: List<Tok>, h0: True): my_len(r) = length(r) {{ refl }}
impl length for ListTok {{ body := my_len, refines := my_len_refines }}
"
    ));
    let refines = e
        .obligations()
        .iter()
        .find(|o| o.field == "refines")
        .expect("`refines`");
    assert_eq!(refines.provenance.map(|p| p.as_str()), Some("named"));
    assert_eq!(e.impl_provenance_of("ListTok", "length").map(|p| p.as_str()), Some("named"));
}
