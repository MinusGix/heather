//! Acceptance for issues/mutual-recursion-declarations.md
//! (docs/mutual-recursion-design.md): N adjacent `decreases` declarations that
//! call one another are one recursion — a product motive `f#grp`, a shared
//! `f#grp_rec`, and each member a projection of it — with the group inferred
//! from adjacency and no keyword written anywhere (§1).
//!
//! What the positives vary (docs/testing-generated-terms.md): a **literal**
//! argument (closed `refl` through the tuple projections and the eliminator)
//! and a **neutral** one (a member applied to an open list inside another
//! recursion, in a checking position); an **open element type** (the
//! polymorphic group, whose helpers hoist the type parameters); heterogeneous
//! telescopes and result types; and the customer's own shape, a call at an
//! *unchanged* measure that pays with §4's member rank.
//!
//! The negative controls are the substance: a pure rank cycle, a run broken by
//! a plain `fn`, disagreeing type-parameter lists, a measure naming a member,
//! a site whose obligation cannot be lifted, and a citation of a member's
//! `f_unfold` (§6, deferred with the reason recorded).

use std::cell::OnceCell;
use std::sync::Mutex;

use heather_elab::{ElabError, Elaborator, SemanticImage};

mod support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/omega.hthr");

/// The same prefix, in the same order, as `semantic_omega_warmup.rs`, so the
/// on-disk image keys this file reads are the ones the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("int", INT),
    ("omega", OMEGA),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn load_image() -> SemanticImage {
    // Two libtest workers otherwise miss the cold image store together and
    // each spends the process's CPU rail checking the same arithmetic
    // prefix. The first worker fills it; the second waits and replays it.
    let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    support::semantic_test_base(MODULES).semantic_image()
}

/// A fresh elaborator over the checked library prefix. The semantic image is
/// the committed-state boundary: every call forks its own attempt, report and
/// gate state, so a test's module never leaks into the next one's base.
fn base() -> Elaborator {
    BASE.with(|base| base.get_or_init(load_image).elaborator())
}

/// §3: a module holding a group imports `pair`, whose `Pair` the motive is.
const IMPORTS: &str =
    "import logic;\nimport nat;\nimport list;\nimport int;\nimport omega;\nimport pair;\n";

fn ok(src: &str) {
    let mut e = base();
    e.elab_module_source("m", &format!("{IMPORTS}{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err}"));
}

fn elab_err(src: &str) -> String {
    let mut e = base();
    match e.elab_module_source("m", &format!("{IMPORTS}{src}")) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

fn any_err(src: &str) -> String {
    let mut e = base();
    match e.elab_module_source("m", &format!("{IMPORTS}{src}")) {
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected this to be refused"),
    }
}

/// The customer (docs/showcase/idealized.hthr 55–105): three adjacent members,
/// each `decreases list_len(ts)`, each calling the next forward — including
/// `parse_expr`'s call to `parse_factor` on the **same** `ts`, which decreases
/// nothing and is paid for by §4's declaration-order rank. Every obligation
/// here is `omega`'s: the list-tail sites needed a lemma by hand until
/// docs/omega-measure-reduction-design.md §6 took it out.
const PARSER: &str = r#"
fn parse_expr(ts: List<Nat>) -> Nat decreases ts.len() {
    match ts {
        Nil => 0,
        Cons(t, rest) => Succ(nat::Nat::add(parse_factor(ts), parse_expr(rest))),
    }
}
fn parse_factor(ts: List<Nat>) -> Nat decreases ts.len() {
    match ts { Nil => 0, Cons(t, rest) => parse_atom(ts) }
}
fn parse_atom(ts: List<Nat>) -> Nat decreases ts.len() {
    match ts { Nil => 1, Cons(t, rest) => parse_expr(rest) }
}
"#;

// -- positives ----------------------------------------------------------------

/// Two members, one `Nat` measure, ranks inert (both calls strictly decrease):
/// the generator still scales the measure uniformly (§11 item 5), and closed
/// arguments still compute through the projections and the eliminator.
#[test]
fn two_members_under_one_measure_compute_at_literals() {
    ok(r#"
fn ev(n: Nat) -> Nat decreases n { match n { Zero => 1, Succ(k) => od(k) } }
fn od(n: Nat) -> Nat decreases n { match n { Zero => 0, Succ(k) => ev(k) } }

theorem ev4(): ev(4) = 1 { refl }
theorem od4(): od(4) = 0 { refl }
theorem ev7(): ev(7) = 0 { refl }
"#);
}

/// The customer's three members, at **literal** arguments. `parse_expr` calls
/// `parse_factor` on the same token list; the rank makes that legal and the
/// writer pays nothing for it — there is no `on` for that site.
#[test]
fn the_parser_group_checks_and_computes() {
    ok(&format!(
        "{PARSER}
theorem pe_nil():  parse_expr([]) = 0 {{ refl }}
theorem pe_one():  parse_expr([7]) = 1 {{ refl }}
theorem pe_two():  parse_expr([7, 8]) = 3 {{ refl }}
theorem pf_one():  parse_factor([7]) = 0 {{ refl }}
theorem pa_two():  parse_atom([7, 8]) = 1 {{ refl }}
"
    ));
}

/// The companion assertion for the hand discharges
/// docs/omega-measure-reduction-design.md §6 removed above: what closes the
/// group's list-tail sites is `omega`, so without the closer's modules they
/// are ordinary unsolved goals again.
#[test]
fn the_parser_groups_tail_sites_are_closed_by_the_closer() {
    let mut e = base();
    let err = e
        .elab_module_source(
            "m",
            &format!("import logic;\nimport nat;\nimport list;\nimport pair;\n{PARSER}"),
        )
        .expect_err("without `omega` the tail sites are ordinary goals");
    let msg = format!("{err}");
    assert!(msg.contains("unsolved goals in `parse_expr#obl_"), "{msg}");
}

/// §4's arithmetic from the clean statement to the scaled one is
/// `Nat::scaled_lt`/`Nat::scaled_le`, not `omega`: a group whose strict sites
/// the writer discharges checks with neither `omega` nor `int` imported. The
/// rank-lowering calls at an unchanged argument — one at a literal-refined
/// `0`, one at an **open** `Succ(k)` — owe `x <= x`, which the lowering closes
/// with `Nat::le_refl` unasked; and at literals the members still compute.
#[test]
fn a_group_with_written_discharges_needs_no_omega() {
    let mut e = base();
    e.elab_module_source(
        "m",
        r#"import logic;
import nat;
import pair;
fn hi(n: Nat) -> Nat decreases n {
    match n { Zero => lo(n), Succ(k) => nat::Nat::add(lo(n), hi(k) decreasing down) }
    on decreasing down := k.lt_succ_self();
}
fn lo(n: Nat) -> Nat decreases n {
    match n { Zero => 0, Succ(k) => Succ(hi(k) decreasing up) }
    on decreasing up := k.lt_succ_self();
}
theorem hi3(): hi(3) = 7 { refl }
theorem lo2(): lo(2) = 2 { refl }
"#,
    )
    .unwrap_or_else(|err| panic!("expected this to check, got: {err}"));
}

/// A member at a **neutral** argument, in a **checking** position: an ordinary
/// singleton `decreases` declaration whose body applies `parse_expr` to its own
/// open scrutinee. The group's members are ordinary globals once registered,
/// which is the claim.
#[test]
fn a_member_applies_to_a_neutral_argument_in_a_checking_position() {
    ok(&format!(
        "{PARSER}
fn total(ts: List<Nat>) -> Nat decreases ts.len() {{
    match ts {{ Nil => 0, Cons(t, rest) => nat::Nat::add(parse_expr(ts), total(rest)) }}
}}
theorem total_two(): total([7, 8]) = 4 {{ refl }}
// an open *element* under a closed spine: nothing about `t` is scrutinized,
// so the group still computes to a numeral.
theorem pf_open(t: Nat): parse_factor([t]) = 0 {{ refl }}
"
    ));
}

/// §3: the type parameters are hoisted to `f#grp`, `f#grp_rec` and each
/// `g#body`, with every reference pinned. Probed at an **open element type**,
/// which is the axis docs/testing-generated-terms.md requires.
#[test]
fn a_polymorphic_group_hoists_its_type_parameters() {
    ok(r#"
fn evens<A>(xs: List<A>) -> List<A> decreases xs.len() {
    match xs { Nil => Nil, Cons(h, t) => Cons(h, odds<A>(t)) }
}
fn odds<A>(xs: List<A>) -> List<A> decreases xs.len() {
    match xs { Nil => Nil, Cons(h, t) => evens<A>(t) }
}

theorem ev_demo(): evens<Nat>([1, 2, 3, 4, 5]) = [1, 3, 5] { refl }
theorem od_demo(): odds<Nat>([1, 2, 3, 4, 5]) = [2, 4] { refl }
theorem ev_nil<A>(): evens<A>(Nil) = Nil { refl }
theorem ev_one<A>(a: A): evens<A>([a]) = [a] { refl }
"#);
}

/// §3: no common telescope and no common result type is required — each
/// component of the product carries its member's own. This is §8's answer to
/// "a member with a different result type": there is nothing to diagnose.
#[test]
fn members_may_differ_in_telescope_and_result_type() {
    ok(r#"
fn f(n: Nat) -> Nat decreases n {
    match n { Zero => 0, Succ(k) => g(Cons(k, Nil), k).len() }
}
fn g(xs: List<Nat>, b: Nat) -> List<Nat> decreases b {
    match b { Zero => xs, Succ(m) => Cons(f(m), g(xs, m)) }
}
theorem f0(): f(0) = 0 { refl }
theorem f2(): f(2) = 2 { refl }
"#);
}

/// §10 / §11 item 6: a run is scoped to one container, and the only container
/// a declaration lives in is the top level of a file — a qualified name is an
/// ordinary top-level declaration that recurses under its **base** name, as
/// `List::nth2` does for a singleton.
#[test]
fn a_group_of_qualified_declarations_recurses_under_base_names() {
    ok(r#"
fn List::ev2<A>(xs: List<A>) -> Nat decreases xs.len() {
    match xs { Nil => 0, Cons(h, t) => od2<A>(t) }
    on ?dec1 := nat::Nat::le_succ_r(t.len(), t.len())(nat::Nat::le_refl(t.len()));
}
fn List::od2<A>(xs: List<A>) -> Nat decreases xs.len() {
    match xs { Nil => 1, Cons(h, t) => ev2<A>(t) }
    on ?dec1 := nat::Nat::lt_succ_self(t.len());
}
theorem q(): List::ev2<Nat>([1, 2, 3]) = 1 { refl }
"#);
}

// -- negative controls --------------------------------------------------------

/// §4: a cycle with no measure drop. `a` calls `b` forward, which the rank
/// makes free; `b` calls `a` back, which must climb, and there is nothing to
/// pay with. The message names the obligation *and* the rank rule.
#[test]
fn a_pure_rank_cycle_is_refused_with_the_rank_rule() {
    let msg = any_err(r#"
fn a(n: Nat) -> Nat decreases n { b(n) }
fn b(n: Nat) -> Nat decreases n { a(n) }
"#);
    assert!(
        msg.contains("this recursive call must decrease the measure"),
        "{msg}"
    );
    assert!(
        msg.contains("`a` is declared above `b`, so a call at an unchanged measure may only \
                      go forward in the group"),
        "{msg}"
    );
    // The writer is told the statement *they* wrote the measure for, not the
    // flattening `omega` closes on top of it (§4).
    assert!(msg.contains("`n < n`"), "{msg}");
}

/// §8: a plain `fn` between two members breaks the run, so the forward
/// reference is an unbound name — with the sentence that says why.
#[test]
fn a_run_broken_by_a_plain_fn_reports_why_the_group_did_not_form() {
    let msg = elab_err(r#"
fn p(n: Nat) -> Nat decreases n { match n { Zero => 0, Succ(k) => q(k) } }
fn between(n: Nat) -> Nat { n }
fn q(n: Nat) -> Nat decreases n { match n { Zero => 1, Succ(k) => p(k) } }
"#);
    assert!(msg.contains("unbound name `q`"), "{msg}");
    assert!(msg.contains("`q` is declared below"), "{msg}");
    assert!(
        msg.contains("nothing else stands between them")
            && msg.contains("docs/mutual-recursion-design.md §1"),
        "{msg}"
    );
}

/// §3: the group's helpers are shared, and a surface function type cannot
/// quantify a type parameter, so every member declares the same list.
#[test]
fn members_disagreeing_on_type_parameters_are_refused() {
    let msg = elab_err(r#"
fn u<A>(xs: List<A>) -> Nat decreases xs.len() {
    match xs { Nil => 0, Cons(h, t) => v(t) }
}
fn v<B>(xs: List<B>) -> Nat decreases xs.len() {
    match xs { Nil => 0, Cons(h, t) => u<B>(t) }
}
"#);
    assert!(
        msg.contains("they declare the same type parameters")
            && msg.contains("`u` has <A>")
            && msg.contains("`v` has <B>"),
        "{msg}"
    );
}

/// §2: the motive quantifies over every member's measure, so a measure defined
/// by the recursion would be circular. Reported as that, before the measure is
/// elaborated — "unbound name" is the wrong thing to say about it.
#[test]
fn a_measure_naming_a_member_is_refused() {
    let msg = elab_err(r#"
fn m1(n: Nat) -> Nat decreases m2(n) { match n { Zero => 0, Succ(k) => m2(k) } }
fn m2(n: Nat) -> Nat decreases n { match n { Zero => 0, Succ(k) => m1(k) } }
"#);
    assert!(
        msg.contains("a `decreases` measure may not call `m2`")
            && msg.contains("docs/mutual-recursion-design.md §2"),
        "{msg}"
    );
}

/// §4: unlike Part A, a group cannot fall back to stating an obligation at the
/// call — `omega` there has the group's ih in context and renders it back as
/// source. A site whose arm binder the generator cannot type is reported.
#[test]
fn a_site_whose_obligation_cannot_be_lifted_is_reported() {
    let msg = elab_err(r#"
fn a1(xs: List<Nat>) -> Nat decreases xs.len() {
    match list_tail(xs) { Nil => 0, Cons(y, ys) => b1(ys) }
}
fn b1(xs: List<Nat>) -> Nat decreases xs.len() {
    match xs { Nil => 0, Cons(h, t) => a1(t) }
}
"#);
    assert!(
        msg.contains("a mutual group cannot fall back to stating it at the call")
            && msg.contains("docs/mutual-recursion-design.md §4"),
        "{msg}"
    );
}

/// §6: the unfolding companions do not extend to a group this round, and the
/// refusal is recorded on each member's `f_unfold` — so a citation reports the
/// reason and the section, not an unknown name.
#[test]
fn citing_a_members_unfolding_equation_reports_the_deferral() {
    let msg = elab_err(r#"
fn ev(n: Nat) -> Nat decreases n { match n { Zero => 1, Succ(k) => od(k) } }
fn od(n: Nat) -> Nat decreases n { match n { Zero => 0, Succ(k) => ev(k) } }
theorem cite(k: Nat): ev(Succ(k)) = od(k) { ev_unfold(Succ(k)) }
"#);
    assert!(
        msg.contains("no unfolding equation for `ev`")
            && msg.contains("member of a mutual `decreases` group")
            && msg.contains("docs/mutual-recursion-design.md §6"),
        "{msg}"
    );
    assert!(
        !msg.contains("unbound") && !msg.contains("unknown"),
        "{msg}"
    );
}
