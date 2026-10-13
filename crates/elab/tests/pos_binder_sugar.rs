//! `Pos<A>` binder sugar (`issues/pos-binder-sugar.md`,
//! `docs/positivity-evidence-design.md` §6 B and §11): a parameter, a
//! function result or a record field written `Pos<A>` is the carrier `A`
//! beside a fact `0 < x`, found by `:= infer`'s proposition search.
//!
//! The sugar is a desugaring, but what fills its facts is a generated term,
//! so the axes of `docs/testing-generated-terms.md` are varied: a literal and
//! a **neutral** operand (`5`, `Succ(k)`, a product of parameters), a second
//! carrier (`Int`, which no rule mentions), a **checking** position (a fact
//! used where a `let` states the goal), and a **negative control** beside
//! each position.

use std::cell::OnceCell;
use std::sync::Mutex;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra.hthr")),
    ("int", include_str!("../../../lib/std/int.hthr")),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn base() -> Elaborator {
    BASE.with(|base| {
        base.get_or_init(|| {
            let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            support::semantic_test_base(MODULES).semantic_image()
        })
        .elaborator()
    })
}

const HEAD: &str = "import logic; import nat; import algebra; import int;
theorem uses(n: Pos<Nat>): 0 < n { n_pos }
";

fn ok(src: &str) {
    let src = format!("{HEAD}{src}");
    if let Err(err) = base().elab_module_source("client", &src) {
        panic!("expected success, got: {}", err.render(&src));
    }
}

fn bad(src: &str) -> String {
    let src = format!("{HEAD}{src}");
    match base().elab_module_source("client", &src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(&src),
    }
}

// -- parameters -------------------------------------------------------------

#[test]
fn a_parameter_is_its_carrier_and_its_fact_is_searched() {
    // Computation (a literal, a neutral `Succ`), a local, and a rule over
    // two locals; the caller passes a plain `Nat` every time.
    ok("theorem lit(): 0 < 5 { uses(5) }
theorem succ(k: Nat): 0 < Succ(k) { uses(Succ(k)) }
theorem local(k: Nat, h: 0 < k): 0 < k { uses(k) }
theorem product(a, b: Nat, pa: 0 < a, pb: 0 < b): 0 < a * b { uses(a * b) }
");
}

#[test]
fn the_fact_is_a_local_of_the_body_and_flows_to_callees() {
    // `n_pos` is in scope by name, and the search finds it for a callee's
    // own `Pos<Nat>` parameter, under a rule and in a checking position.
    ok("theorem square(n: Pos<Nat>): 0 < n * n { uses(n * n) }
theorem stated(n: Pos<Nat>): 0 < n * 2 { let h: (0 < n * 2) = uses(n * 2); h }
fn halve(n: Pos<Nat>) -> Nat { n.div(2) }
fn caller(k: Pos<Nat>) -> Nat { halve(k) + halve(k * k) }
");
}

#[test]
fn a_parameter_without_evidence_is_refused_at_the_call() {
    let e = bad("theorem zero(): 0 < 0 { uses(0) }\n");
    assert!(e.contains("no instance for `Lt(0, 0)`"), "{e}");
    let e = bad("theorem open(k: Nat): 0 < k { uses(k) }\n");
    assert!(e.contains("no instance for `Lt(0, k)`"), "{e}");
}

#[test]
fn the_fact_is_named_by_hand_and_takes_no_positional_slot() {
    // `n_pos := …` overrides the search; `1 <= k` is convertible to `0 < k`.
    // A run of `Pos` names adds one fact after each, and the positional
    // arity is the values' alone: `two(x, y, 7)`. `@` passes every slot.
    ok("theorem named(k: Nat, h: 1 <= k): 0 < k { uses(k, n_pos := h) }
theorem two(a, b: Pos<Nat>, c: Nat): 0 < a * b { Nat::mul_pos() }
theorem call(x, y: Nat, px: 0 < x, py: 0 < y): 0 < x * y { two(x, y, 7) }
theorem by_hand(k: Nat, h: 0 < k): 0 < k { @uses(k, h) }
theorem order(x, y: Nat, px: 0 < x, py: 0 < y): 0 < x * y { @two(x, px, y, py, 7) }
");
}

#[test]
fn a_second_carrier_uses_its_own_designations() {
    // `Int` has `<` and a numeral, and no rule: locals and the named
    // override reach it, and a zero is refused.
    ok("theorem usesi(x: Pos<Int>): 0 < x { x_pos }
theorem local(x: Int, h: 0 < x): 0 < x { usesi(x) }
theorem named(x: Int, h: OfNat(1) <= x): 0 < x { usesi(x, x_pos := h) }
");
    let e = bad("theorem usesi(x: Pos<Int>): 0 < x { x_pos }
theorem open(x: Int): 0 < x { usesi(x) }
");
    assert!(e.contains("no instance"), "{e}");
}

#[test]
fn pos_is_not_a_type_outside_a_binder() {
    let e = bad("fn apply(f: Pos<Nat> -> Nat) -> Nat { f(1) }\n");
    assert!(e.contains("`Pos<A>` is binder sugar, not a type"), "{e}");
    let e = bad("fn dflt(n: Pos<Nat> := 3) -> Nat { n }\n");
    assert!(e.contains("a `Pos<A>` parameter takes no default"), "{e}");
}

// -- results ----------------------------------------------------------------

#[test]
fn a_result_declares_its_fact_as_an_evidence_rule() {
    // `sq::pos` exists by name and is found by the search: at a literal, at
    // a neutral argument whose own positivity is a local, and nested under
    // a rule. A body with `let`s is restated whole.
    ok("fn sq(n: Pos<Nat>) -> Pos<Nat> { n * n }
fn seven() -> Pos<Nat> { 7 }
fn grow(n: Nat) -> Pos<Nat> { let m = n + 1; m * 2 }
theorem named(k: Nat, h: 0 < k): 0 < sq(k) { sq::pos(n := k) }
theorem lit(): 0 < sq(3) { uses(sq(3)) }
theorem neutral(k: Nat, h: 0 < k): 0 < sq(k) { uses(sq(k)) }
theorem nested(i: Nat): 0 < grow(i) * seven() { uses(grow(i) * seven()) }
theorem stated(i: Nat): 0 < grow(i) { let h: (0 < grow(i)) = uses(grow(i)); h }
");
}

#[test]
fn a_result_fact_rests_on_the_arguments_evidence() {
    // `sq::pos`'s premise is `sq`'s own `n_pos`, which the call `sq(k)`
    // already needs: with no evidence for `k`, the call is what is refused.
    let e = bad("fn sq(n: Pos<Nat>) -> Pos<Nat> { n * n }
theorem open(k: Nat): 0 < sq(k) { uses(sq(k)) }
");
    assert!(e.contains("no instance for `Lt(0, k)`"), "{e}");
}

#[test]
fn a_recursive_result_is_proved_by_hand() {
    // `on ?pos := …` proves `0 < fact(n)` itself, so it can recurse on
    // `fact::pos`; the caller's search uses it all the same.
    ok("fn fact(n: Nat) -> Pos<Nat> {
    match n { Zero => 1, Succ(k) => Succ(k) * fact(k) }
    on ?pos := match n { Zero => trivial, Succ(k) => @Nat::mul_pos(Succ(k), fact(k), trivial, @fact::pos(k)) };
}
theorem used(i: Nat): 0 < fact(i) * 2 { uses(fact(i) * 2) }
");
}

#[test]
fn a_result_the_search_cannot_prove_is_refused_with_the_way_out() {
    let e = bad("fn ident(n: Nat) -> Pos<Nat> { n }\n");
    assert!(e.contains("`positivity` could not prove `Lt(0, n)`"), "{e}");
    assert!(e.contains("`on ?pos := …;`"), "{e}");
    // A recursion restated is a case split the search cannot read.
    let e = bad("fn up(n: Nat) -> Pos<Nat> { match n { Zero => 1, Succ(k) => up(k) + 1 } }\n");
    assert!(e.contains("`on ?pos := …;`"), "{e}");
    // A proof by hand is checked like any other proof, at the statement,
    // and the search does not run.
    let e = bad("fn ident(n: Nat) -> Pos<Nat> { n
    on ?pos := trivial;
}\n");
    assert!(!e.contains("`positivity` could not prove"), "{e}");
}

#[test]
fn a_result_is_a_functions_alone() {
    let e = bad("theorem t(n: Nat): Pos<Nat> { n }\n");
    assert!(e.contains("`Pos<A>` as a result is a function's"), "{e}");
    let e = bad("fn Nat::twice(n: Nat) -> Pos<Nat> { n + n + 1 }\n");
    assert!(e.contains("a member owns no members yet"), "{e}");
}

#[test]
fn a_result_fact_reaches_an_importer() {
    // The rule is an ordinary `evidence theorem`, so it travels as a module
    // event: the importer's search finds `sq::pos` with no name written.
    let mut e = base();
    let a = format!("{HEAD}fn sq(n: Pos<Nat>) -> Pos<Nat> {{ n * n }}\n");
    if let Err(err) = e.elab_module_source("a", &a) {
        panic!("module a: {}", err.render(&a));
    }
    let b = "import nat; import a;
theorem uses(n: Pos<Nat>): 0 < n { n_pos }
theorem used(k: Nat, h: 0 < k): 0 < sq(k) * sq(k) { uses(sq(k) * sq(k)) }
";
    if let Err(err) = e.elab_module_source("b", b) {
        panic!("module b: {}", err.render(b));
    }
}

// -- record fields ----------------------------------------------------------

const FRAC: &str = "record Frac { num: Nat, den: Pos<Nat> }\n";

#[test]
fn a_field_is_its_carrier_and_its_fact_is_searched_at_construction() {
    ok(&format!("{FRAC}fn lit() -> Frac {{ Frac(1, 2) }}
fn neutral(k: Nat) -> Frac {{ Frac(1, Succ(k)) }}
fn local(k: Nat, h: 0 < k) -> Frac {{ Frac(1, k) }}
fn product(f, g: Frac) -> Frac {{ Frac(f.num * g.num, f.den * g.den) }}
fn named(k: Nat, h: 1 <= k) -> Frac {{ Frac(1, k, den_pos := h) }}
fn written(k: Nat, h: 0 < k) -> Frac {{ Frac(1, k, h) }}
"));
}

#[test]
fn a_field_declares_a_rule_about_its_projection() {
    // `0 < f.den` is not a local, and `Frac::den_positive` is what reads it,
    // alone, under a rule and in a checking position.
    ok(&format!("{FRAC}theorem den(f: Frac): 0 < f.den {{ uses(f.den) }}
theorem product(f, g: Frac): 0 < f.den * g.den {{ uses(f.den * g.den) }}
theorem stated(f: Frac): 0 < f.den {{ let h: (0 < f.den) = Frac::den_positive(); h }}
"));
}

#[test]
fn a_field_without_evidence_is_refused_at_the_construction() {
    let e = bad(&format!("{FRAC}fn zero() -> Frac {{ Frac(1, 0) }}\n"));
    assert!(e.contains("no evidence for `Lt(0, 0)`"), "{e}");
    let e = bad(&format!("{FRAC}fn open(k: Nat) -> Frac {{ Frac(1, k) }}\n"));
    assert!(e.contains("no evidence for"), "{e}");
}

#[test]
fn a_field_on_a_parameterised_record_is_refused() {
    let e = bad("record Box<A> { a: A, n: Pos<Nat> }\n");
    assert!(e.contains("record without parameters only"), "{e}");
    let e = bad("record Frac { den: Pos<Nat> := 1 }\n");
    assert!(e.contains("a `Pos<A>` field takes no default"), "{e}");
}
