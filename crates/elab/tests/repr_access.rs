//! The designed access spellings of a repr and its `Impl`s
//! (`docs/repr-access-spellings-design.md`).
//!
//! What is under test is a *resolution* device over generated terms, so the
//! axes of `docs/testing-generated-terms.md` apply and are varied here: a
//! **literal** carrier value (the derived body computing to a numeral) and a
//! **neutral** one (a parameter), an **open** element type (`Tok`, which is
//! not the carrier), **checking** positions throughout (every designed path is
//! used where its declared type is expected, and the laws are used as proofs
//! of statements written out by hand), and negative controls for each half of
//! the rule: the minted spelling refuses and names the designed one, an
//! unknown member prints the member list, and an access path with no
//! declaration behind it says which declaration is missing.

use heather_elab::Elaborator;

mod support;
use support::{BIN_MIN, BIN_REPR};

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

/// The naive repr of a parameterized instantiation, plus a derived `Impl` —
/// the fixture every path below is spelled against.
const DERIVED: &str = "
fn length(l: List<Tok>) -> Nat { match l { Nil => Zero, Cons(h, t) => Succ(length(t)) } }
datarepr ListTok for List<Tok> := repr::naive();
impl length for ListTok := derive();
";

// -- the designed spellings check -------------------------------------------

#[test]
fn every_designed_repr_member_checks_in_a_checking_position() {
    // Each member used where its declared type is expected, at an **open**
    // element type, over a **neutral** carrier value.
    ok(&format!(
        "{LIST}
datarepr ListTok for List<Tok> := repr::naive();

fn carrier_of(r: ListTok().R) -> List<Tok> {{ ListTok::abs(r) }}
fn invariant_of(r: List<Tok>) -> Type {{ ListTok::inv(r) }}
fn one(t: Tok) -> List<Tok> {{ ListTok::mk_Cons(t, ListTok::mk_Nil()) }}
fn len(l: List<Tok>) -> Nat {{
    ListTok::fold(Nat, Zero, λ t r b => Succ(b), l)
}}
fn spec_len(l: List<Tok>) -> Nat {{
    ListTok::spec_rec(Nat, Zero, λ t r b => Succ(b), l)
}}
theorem image_law(t: Tok): ListTok::abs(one(t)) = Cons(t, Nil) {{
    ListTok::Cons_abs(t, ListTok::mk_Nil(), ListTok::Nil_inv())
}}
theorem closure_law(t: Tok): ListTok::inv(one(t)) {{
    ListTok::Cons_inv(t, ListTok::mk_Nil(), ListTok::Nil_inv())
}}
theorem anchor(B: Type, s0: B, s1: (a0: Tok) -> (a1: List<Tok>) -> (b0: B) -> B,
               r: List<Tok>, h: ListTok::inv(r)):
    ListTok::fold(B, s0, λ a0 a1 b0 =>
        s1(a0, ListTok::abs(a1), b0), r)
      = ListTok::spec_rec(B, s0, s1, ListTok::abs(r))
{{ ListTok::fold_law(B, s0, s1, r, h) }}
"
    ));
}

#[test]
fn the_designed_fold_computes_at_a_literal() {
    // The **literal** axis: the same member, applied to a closed carrier
    // value, reduces to the numeral it should.
    ok(&format!(
        "{LIST}
datarepr ListTok for List<Tok> := repr::naive();
theorem two(): ListTok::fold(Nat, Zero, λ t r b => Succ(b),
                            Cons(TAdd, Cons(TMul, Nil)))
      = Succ(Succ(Zero))
{{ refl }}
"
    ));
}

#[test]
fn an_impl_is_cited_through_its_applied_owner_path() {
    // The new grammar (design §4), at a **neutral** argument and in a
    // **checking** position: the certificate discharges an equation written
    // out by hand in the designed vocabulary.
    ok(&format!(
        "{LIST}{DERIVED}
fn by_impl(r: List<Tok>) -> Nat {{ Impl(length, ListTok)::body(r) }}
theorem by_impl_refines(r: List<Tok>, h0: ListTok::inv(r)):
    Impl(length, ListTok)::body(r) = length(ListTok::abs(r))
{{ Impl(length, ListTok)::refines(r, h0) }}
theorem by_impl_at_two():
    Impl(length, ListTok)::body(Cons(TAdd, Cons(TMul, Nil))) = Succ(Succ(Zero))
{{ refl }}
"
    ));
}

/// The round's tightest claim: what `heather obligations` prints is what an
/// author can write. The statement is taken out of the listing programmatically
/// and used, verbatim, as a theorem's type.
#[test]
fn a_printed_statement_is_writable_verbatim() {
    let e = ok(BIN_REPR);
    let row = e
        .obligations()
        .iter()
        .find(|o| o.field == "Succ_abs")
        .expect("the `Succ_abs` row");
    assert_eq!(row.path, "BinNat::Succ_abs");
    assert!(!row.statement.contains("Repr_BinNat"), "{}", row.statement);
    assert!(row.statement.contains("BinNat::abs("), "{}", row.statement);
    let restated = format!("theorem restated(): {} {{ bin_succ_abs_law }}", row.statement);
    let src = format!("{BIN_REPR}\n{restated}\n");
    ok(&src);
}

#[test]
fn a_printed_anchor_statement_names_the_designed_spec_recursor() {
    let e = ok(BIN_REPR);
    let row = e.obligations().iter().find(|o| o.field == "fold_law").expect("the anchor row");
    assert!(row.statement.contains("BinNat::spec_rec("), "{}", row.statement);
    assert!(!row.statement.contains("BinNat_spec_rec"), "{}", row.statement);
}

/// The via-abs default's four artifacts are members **only** where the default
/// was taken (design §3.1). `BIN_MIN` omits `fold`; `BIN_REPR` writes one.
#[test]
fn the_via_abs_members_exist_exactly_where_the_default_was_taken() {
    ok(&format!(
        "{BIN_MIN}
theorem embeds_two(): bin_abs(BinMin::emb(Succ(Succ(Zero)))) = Succ(Succ(Zero))
{{ BinMin::emb_abs(Succ(Succ(Zero))) }}
"
    ));
    let msg = bad(&format!("{BIN_REPR}\nfn p(n: Nat) -> Bin {{ BinNat::emb(n) }}\n"));
    assert!(msg.contains("`BinNat` has no member `emb`"), "{msg}");
    assert!(msg.contains("`fold_law`"), "{msg}");
}

// -- `.` is projection, and still is (design §3.2) ---------------------------

#[test]
fn projection_off_the_assembled_value_agrees_with_the_designed_path() {
    // Not a second spelling: an ordinary record projection, definitionally the
    // member. Both scrutinee axes — a neutral `r` for the equation, a literal
    // for the computation.
    ok(&format!(
        "{LIST}
datarepr ListTok for List<Tok> := repr::naive();
theorem same(r: List<Tok>):
    ListTok().fold(Nat, Zero, λ t l b => Succ(b), r)
      = ListTok::fold(Nat, Zero, λ t l b => Succ(b), r)
{{ refl }}
theorem same_at_a_literal(t: Tok): ListTok().abs(ListTok::mk_Cons(t, ListTok::mk_Nil()))
      = Cons(t, Nil)
{{ refl }}
"
    ));
}

// -- negative controls -------------------------------------------------------

#[test]
fn the_minted_repr_member_is_refused_and_names_the_designed_form() {
    let msg = bad(&format!("{BIN_REPR}\nfn p() -> (r: Bin) -> Nat {{ Repr_BinNat::abs() }}\n"));
    assert!(msg.contains("is a generated name and is not part of the surface"), "{msg}");
    assert!(msg.contains("write `BinNat::abs`"), "{msg}");
}

#[test]
fn the_minted_spec_recursor_is_refused_and_names_the_designed_form() {
    let msg = bad(&format!(
        "{BIN_REPR}
fn p() -> Nat {{ BinNat_spec_rec(Nat, Zero, λ a b => Succ(b), Zero) }}
"
    ));
    assert!(msg.contains("write `BinNat::spec_rec`"), "{msg}");
}

#[test]
fn the_minted_impl_member_is_refused_and_names_the_designed_form() {
    let msg = bad(&format!(
        "{LIST}{DERIVED}
fn p(r: List<Tok>) -> Nat {{ Impl_ListTok_length::body(r) }}
"
    ));
    assert!(msg.contains("write `Impl(length, ListTok)::body`"), "{msg}");
}

/// The `via_derived` route's intermediate stays an internal: it is a step in
/// how one clause was proved, not something another proof may rely on
/// (design §3.3).
#[test]
fn a_route_intermediate_has_no_surface_spelling() {
    let msg = bad(&format!(
        "{LIST}{DERIVED}
fn p(r: List<Tok>) -> Nat {{ ListTok_length_impl() }}
"
    ));
    assert!(msg.contains("has no surface spelling"), "{msg}");
    assert!(msg.contains("`impl length for ListTok`"), "{msg}");
}

#[test]
fn an_unknown_member_of_a_repr_prints_the_member_list() {
    let msg = bad(&format!("{BIN_REPR}\nfn p() -> Nat {{ BinNat::nope() }}\n"));
    assert!(msg.contains("`BinNat` has no member `nope`"), "{msg}");
    assert!(msg.contains("`abs`"), "{msg}");
    assert!(msg.contains("`spec_rec`"), "{msg}");
}

#[test]
fn an_access_path_with_no_impl_behind_it_names_the_missing_declaration() {
    let msg = bad(&format!(
        "{LIST}
fn length(l: List<Tok>) -> Nat {{ match l {{ Nil => Zero, Cons(h, t) => Succ(length(t)) }} }}
datarepr ListTok for List<Tok> := repr::naive();
fn p(r: List<Tok>) -> Nat {{ Impl(length, ListTok)::body(r) }}
"
    ));
    assert!(msg.contains("no `impl length for ListTok` is declared"), "{msg}");
}

#[test]
fn a_path_whose_owner_is_not_an_applied_name_is_a_parse_error() {
    let msg = bad("fn p() -> Nat { (λ x => x)(Zero)::refines }");
    assert!(msg.contains("needs an owner of the form"), "{msg}");
    assert!(msg.contains("Impl(<op>, <repr>)::refines"), "{msg}");
}

/// The mode boundary (design §6), as a pair: the *same* text is refused
/// through the user entry point and accepted through the generated one. This
/// is what keeps the perturbed-emission mutation controls honest — without it
/// they would pass on the refusal of a name rather than on the mutation.
#[test]
fn generated_text_is_refused_as_user_source_and_accepted_as_generated() {
    let cite = format!("{BIN_REPR}\nfn p() -> (r: Bin) -> Nat {{ Repr_BinNat::abs() }}\n");
    let mut refused = Elaborator::with_prelude().expect("prelude");
    assert!(refused.elab_source(&cite).is_err(), "the user entry point must refuse it");
    let mut accepted = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = accepted.elab_generated_source(&cite) {
        panic!("the generated entry point must accept it: {}", err.render(&cite));
    }
}

/// …and the exemption is exactly one elaboration deep: a file that *contains* a
/// `datarepr` is user source again as soon as its emission is done.
#[test]
fn the_generated_exemption_does_not_leak_past_the_emission() {
    let msg = bad(&format!("{BIN_REPR}\nfn p() -> (r: Bin) -> Nat {{ Repr_BinNat::abs() }}\n"));
    assert!(msg.contains("write `BinNat::abs`"), "{msg}");
}

/// The alias never *re*-interprets: a member of a genuine type's namespace
/// keeps resolving to that member, at a name shaped exactly like a designed
/// path (design §5, the fallback ordering).
#[test]
fn a_real_type_member_is_not_shadowed_by_the_alias() {
    ok(&format!(
        "{LIST}
datarepr ListTok for List<Tok> := repr::naive();
record Holder {{ n: Nat }}
fn Holder::abs(h: Holder) -> Nat {{ h.n }}
fn use_it(h: Holder) -> Nat {{ Holder::abs(h) }}
fn still_the_repr(r: List<Tok>) -> List<Tok> {{ ListTok::abs(r) }}
"
    ));
}
