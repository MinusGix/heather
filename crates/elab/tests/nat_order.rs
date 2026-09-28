//! `lib/std/nat.hthr`'s **propositional** order and the `Cmp` class that now
//! takes it (`issues/nat-order-kit.md`, `docs/nat-order-design.md`).
//!
//! The module checking is not the interesting assertion — every `.hthr` file
//! under `lib/` is checked somewhere already. What is asserted here is the
//! four things the design claims and a Bool-valued order could not have given:
//!
//! - §1 the definition **reduces**, so closed comparisons are `trivial` and
//!   deciding is `refl`;
//! - §2 inversion and the successor step are **definitional**, asserted by
//!   handing a proof of one type to a slot expecting the other;
//! - §3 the kit is usable at **open** arguments, which is the axis
//!   `docs/testing-generated-terms.md` calls the one closed types hide;
//! - §4 `<` parses where a hypothesis goes, the grammar half of the round.
//!
//! Every positive here has a **negative control** beside it, because most of
//! this file's positives would pass against a definition that was simply
//! `λ n m => True`. The controls are what rule that out.

use heather_elab::{ElabError, Elaborator};

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = support::library(&[
        ("logic", LOGIC), ("bool", BOOL), ("nat", NAT),
        ("option", OPTION), ("pair", PAIR), ("list", LIST),
        ("algebra", ALGEBRA),
    ]);
    if !extra.is_empty() {
        let src = format!(
            "import logic;\nimport bool;\nimport nat;\nimport option;\n\
             import list;\nimport algebra;\n{extra}"
        );
        if let Err(err) = e.elab_module_source("probe", &src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
    }
    Ok(e)
}

fn ok(extra: &str) {
    run(extra).unwrap_or_else(|e| panic!("expected this to check, got: {e}"));
}

fn bad(extra: &str) -> String {
    match run(extra) {
        Err(e) => e,
        Ok(_) => panic!("expected a refusal, but it checked"),
    }
}

// ---------------------------------------------------------------------------
// 1. The definition reduces. This is the property the whole design rests on —
//    the thing the retired `leb(n)(m) = True` spelling existed to buy — and it
//    is asserted at a *closed* comparison, where reduction is the only way the
//    proof can be `trivial`.

#[test]
fn a_closed_comparison_is_trivial() {
    ok("theorem t(): 3 <= 10 { trivial }
theorem u(): 3 < 10 { trivial }
theorem v(): 7 <= 7 { trivial }");
}

/// The control without which the test above is worthless: a **false**
/// comparison must not be `trivial`. If `Le` were `λ n m => True` the previous
/// test would pass and this one would too, so this is what separates a
/// relation from a tautology.
#[test]
fn a_false_closed_comparison_is_refused() {
    bad("theorem t(): 10 <= 3 { trivial }");
    bad("theorem t(): 7 < 7 { trivial }");
}

/// A refuted comparison is `False`, and *by computation* — no lemma is cited.
/// The second line is the same fact reached through `¬`, which is how the kit
/// states it.
#[test]
fn a_refuted_comparison_is_already_falsity() {
    ok("theorem t(h: 10 <= 3): False { h }
theorem u(): ¬ (10 <= 3) { λ (h: 10 <= 3) => h }
theorem v(n: Nat, h: Succ(n) <= 0): False { h }");
}

// ---------------------------------------------------------------------------
// 2. Definitional inversion: `Le(Succ n, Succ m)` and `Le(n, m)` are ONE type.
//    Asserted by passing a proof of each where the other is expected, with no
//    lemma between them — a lemma would prove only that a lemma exists.

#[test]
fn the_successor_step_is_the_identity_in_both_directions() {
    ok("theorem down(n, m: Nat, h: Succ(n) <= Succ(m)): n <= m { h }
theorem up(n, m: Nat, h: n <= m): Succ(n) <= Succ(m) { h }");
}

/// `Lt(n, Succ m)` and `Le(n, m)` are likewise one type, which is why
/// `lt_succ_iff_le` is a pair of identity functions.
#[test]
fn lt_at_a_successor_is_le() {
    ok("theorem t(n, m: Nat, h: n < Succ(m)): n <= m { h }
theorem u(n, m: Nat, h: n <= m): n < Succ(m) { h }");
}

/// The control: identity does **not** relate the two sides at a *shifted*
/// pair. Without this, `Le` being constant would satisfy everything above.
#[test]
fn identity_does_not_relate_unequal_shifts() {
    bad("theorem t(n, m: Nat, h: Succ(n) <= m): n <= m { h }");
}

// ---------------------------------------------------------------------------
// 3. The kit at OPEN arguments — the axis a closed type hides
//    (docs/testing-generated-terms.md). Every lemma below is applied to
//    variables, so nothing here can be discharged by reduction.

#[test]
fn the_order_kit_composes_at_open_arguments() {
    ok("theorem t(a, b, c: Nat, h1: a <= b, h2: b <= c): a <= c {
    a.le_trans(b, c, h1, h2)
}
theorem u(a, b: Nat, h1: a <= b, h2: b <= a): a = b { a.le_antisym(b, h1, h2) }
theorem v(a: Nat): 0 <= a { a.nonneg() }
theorem w(a, b: Nat): Or<nat::Nat::Le(a, b), nat::Nat::Le(b, a)> { a.le_total(b) }");
}

#[test]
fn the_strict_kit_composes_at_open_arguments() {
    ok("theorem t(a, b, c: Nat, h1: a < b, h2: b < c): a < c { a.lt_trans(b, c, h1, h2) }
theorem u(a: Nat, h: a < a): False { a.lt_irrefl()(h) }
theorem v(a, b: Nat, h: a < b): a <= b { a.le_of_lt(b, h) }
theorem w(a: Nat): a < Succ(a) { a.lt_succ_self() }
theorem x(a, b: Nat, h: a <= b, ne: ¬ (a = b)): a < b { a.lt_of_le_of_ne(b, h, ne) }
theorem y(a, b: Nat): Or<a.Lt(b), Or<(a = b), b.Lt(a)>> { a.lt_trichotomy(b) }");
}

/// The bridge to addition, both ways, at open arguments. `le_iff_exists_add`
/// is what keeps route (c) of the design available as a *view* — and it is
/// written with the `Exists(…)` call spelling because the `∃` notation does
/// not reach a type-argument slot ([[quantifier-notation-in-type-arguments]]).
#[test]
fn the_addition_bridge_goes_both_ways() {
    ok("theorem fwd(a, b: Nat, h: a <= b): Exists(λ (k: Nat) => a.add(k) = b) {
    a.le_iff_exists_add(b).mp(h)
}
theorem bwd(a, b: Nat, h: Exists(λ (k: Nat) => a.add(k) = b)): a <= b {
    a.le_iff_exists_add(b).mpr(h)
}
theorem round_trip(a, k: Nat): a <= a.add(k) {
    a.le_iff_exists_add(a.add(k)).mpr(Exists(k, refl))
}");
}

/// The decider is total and reduces, so a *closed* use of it is `refl`-usable
/// while an *open* one is still a legitimate `Or` to match on. Both matter:
/// the first is what makes `max_of` compute, the second what makes it a
/// decision rather than a lookup.
#[test]
fn the_decider_works_closed_and_open() {
    ok("theorem closed(): nat::Nat::Le(2, 5) { or_resolve(nat::Nat::le_dec(2)(5), λ (k: ¬ nat::Nat::Le(2, 5)) => k(trivial)) }
fn branch(a, b: Nat) -> Nat { or_pick(nat::Nat::le_dec(a)(b), a, b) }
theorem at_open(a, b: Nat, h: a <= b): branch(a, b) = b { or_pick_dec(nat::Nat::le_dec(a)(b), a, b, h) }
theorem at_closed(): branch(2, 5) = 5 { refl }
theorem the_other_way(): branch(5, 2) = 5 { refl }");
}

// ---------------------------------------------------------------------------
// 4. `Cmp` went propositional (design §3), and the two facts that had to
//    survive the conversion are that it still COMPUTES and that its law is now
//    the relation rather than an equation with `True`.

#[test]
fn max_of_still_computes_at_both_carriers() {
    ok("theorem picks_the_larger(): max_of(2, 5) = 5 { refl }
theorem picks_the_larger_the_other_way(): max_of(5, 2) = 5 { refl }
theorem on_bools(): max_of(bool::False, bool::True) = bool::True { refl }
theorem idempotent(n: Nat): max_of(n, n) = n { max_of_self(n) }");
}

/// Why `on_bools` above is qualified, pinned so the qualification is a
/// *recorded* boundary rather than someone's stray habit. The
/// `False`-coexistence rules (`issues/false-collides-with-bools-constructor.md`)
/// are two shrinks: a **type** position never considers a constructor, and an
/// expected type that is a known inductive never considers a type name.
/// `max_of(False, False)` is neither — the expected type is `A`, the class's
/// carrier, and nothing in the call solves it — so both readings survive and
/// the elaborator says so by name instead of guessing. Correct, and it only
/// bites where `logic` and `bool` are imported into one file.
///
/// `max_of(False, True)` is *not* this case, in either order: a bare `False`
/// waits for the arguments after it
/// (issues/nullary-ctor-argument-not-deferred.md), `True` names only `bool`'s
/// constructor in a term position and pins `A := Bool`, and `False` is then
/// checked at a known inductive — the second shrink.
#[test]
fn a_bare_false_at_an_unsolved_carrier_is_ambiguous() {
    let e = bad("fn t() -> Nat { let x = max_of(False, False); 0 }");
    assert!(e.contains("ambiguous") && e.contains("logic") && e.contains("bool"), "{e}");
    ok("theorem t(): max_of(False, True) = True { refl }
theorem u(): max_of(True, False) = True { refl }");
}

/// The rename that is the content of §3: the hypothesis is the RELATION, not
/// a fact about having run a decision procedure. The negative control is that
/// the retired spelling is gone rather than merely unused — a `= True`
/// hypothesis no longer typechecks against the field, because the field is not
/// `Bool`-valued.
#[test]
fn the_cmp_law_is_the_relation_itself() {
    ok("theorem t(a, b: Nat, h: a <= b): max_of(a, b) = b { max_of_le(a, b, h) }");
    let e = bad("theorem t(a, b: Nat, h: nat::Nat::leb(a)(b) = True): max_of(a, b) = b { max_of_le(a, b, h) }");
    assert!(!e.is_empty(), "expected a type error, got an empty message");
}

/// Generic over the class, at a binder rather than a carrier: the conversion
/// did not cost `Cmp` its abstraction. `A.le_dec` is projected from the type
/// exactly as `A.le_refl` was.
#[test]
fn the_class_still_abstracts() {
    ok("fn biggest<A: Cmp>(x, y: A) -> A { max_of(x, y) }
theorem t<A: Cmp>(x: A): biggest(x, x) = x { max_of_self(x) }
fn decide_it<A: Cmp>(x, y: A) -> Or<A.le(x, y), Not(A.le(x, y))> { A.le_dec(x, y) }");
}

// ---------------------------------------------------------------------------
// 5. The grammar half (design §4): `<` parses where a hypothesis goes. Before
//    this round every one of these was a parse error, because `Parser::ty`
//    read `ident <` as the start of type arguments unconditionally.

#[test]
fn lt_parses_in_every_type_position() {
    ok("fn a(n, m: Nat, h: n < m) -> Nat { 0 }
theorem b(n: Nat): n < Succ(n) { n.lt_succ_self() }
theorem c(n, m: Nat, h: Or<n < m, m <= n>): Nat { 0 }
fn len_of(xs: List<Nat>) -> Nat { 0 }
fn nth_lt(xs: List<Nat>, i: Nat, h: i < len_of(xs)) -> Nat { 0 }");
}

/// The control the speculative parse must not break: a genuine type
/// application still parses as one, including nested and multi-argument.
#[test]
fn type_application_still_parses_as_type_application() {
    ok("theorem d<P, Q>(h: And<P, Q>): And<Q, P> { and_swap(h) }
fn e(xs: List<Option<Nat>>) -> List<Option<Nat>> { xs }
fn f(h: Iff<And<Nat, Nat>, Nat>) -> Nat { 0 }");
}

/// This was the round's residue, pinned as a *refusal* with the note "if this
/// test starts failing, that issue has been fixed and this becomes a
/// positive". It did, so it is — `issues/comparison-inside-type-arguments.md`
/// closed the same day under the one-directional whitespace rule
/// (`docs/type-argument-disambiguation.md`), and an unparenthesized comparison
/// inside type arguments now parses.
///
/// The parenthesized spelling is asserted beside it, because parens did not
/// stop being correct — they stopped being *mandatory*.
#[test]
fn a_bare_comparison_inside_type_arguments_now_parses() {
    ok("theorem c(n, m: Nat, h: Or<n < m, m <= n>): Nat { 0 }
theorem d(n, m: Nat, h: Or<(n < m), (m <= n)>): Nat { 0 }");
}

/// Literal size must not unroll the delayed induction hypotheses when the
/// two sides differ only by one successor reduction (le-lt-conversion-linear-in-literal).
#[test]
fn large_literal_successor_conversion() {
    for k in [16, 1024, 0xD800, 0x10FFFF] {
        ok(&format!("theorem down(n: Nat, h: {k} < Succ(n)): {k} <= n {{ h }}
            theorem up(n: Nat, h: {k} <= n): {k} < Succ(n) {{ h }}
            theorem le_down(n: Nat, h: Succ({k}) <= Succ(n)): {k} <= n {{ h }}
            theorem mid(n: Nat, h: ¬(Succ(n) <= {k})): {k} <= n {{
                Nat::lt_of_not_le({k}, Succ(n), h)
            }}"));
    }
}

#[test]
fn large_literal_successor_conversion_preserves_the_arguments() {
    bad("theorem shifted(n: Nat, h: 0xD800 < Succ(n)): 0xD801 <= n { h }");
    bad("theorem other(n, m: Nat, h: 0xD800 < Succ(n)): 0xD800 <= m { h }");
}
