//! Acceptance for issues/termination-measures.md
//! (docs/termination-measures-design.md): `decreases e`, recursion justified
//! by a `Nat` measure. The lowering is strong induction on a bound for the
//! measure, spelled at the surface and checked like any other term, so the
//! analysis is untrusted and the negative controls are the substance: a call
//! that does not decrease is refused with its obligation named.
//!
//! What the positives vary (docs/testing-generated-terms.md): closed
//! computation (`refl` at literals) and open proofs, the automatic closer
//! (`omega`) and the by-hand discharge (`on ?decN`), a lemma-fed decrease
//! (the parser shape), and a `theorem` recursing by measure. A measure at a
//! **constructor pattern** has a file of its own,
//! `omega_measure_reduction.rs` (docs/omega-measure-reduction-design.md).

use std::sync::OnceLock;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/num/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/tactic/omega.hthr");

/// The same prefix, in the same order, as `semantic_omega_warmup.rs`, so the
/// on-disk image keys this file reads are the ones the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", ALGEBRA),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", INT),
    ("omega", OMEGA),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn load_image() -> SemanticImage {
    // Built once per process (`BASE` is a process-wide `OnceLock`; the other
    // tests wait for it): see `support`'s note on per-test threads.
    support::semantic_test_base(MODULES).semantic_image()
}

/// A fresh elaborator over the checked library prefix. The semantic image is
/// the committed-state boundary: every call forks its own attempt, report and
/// gate state, so a test's module never leaks into the next one's base.
fn base() -> Elaborator {
    BASE.get_or_init(load_image).elaborator()
}

const IMPORTS: &str = "import logic;\nimport nat;\nimport list;\nimport int;\nimport omega;\n";

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

// -- programs -----------------------------------------------------------------

/// Euclid. The obligation `nat::Nat::mod(a, Succ(k)) < Succ(k)` is stated at the
/// *pattern* — the `match b` was convoyed — so `mod_lt` proves it directly.
/// The `on` stays: nothing here is at a constructor *measure*
/// (docs/omega-measure-reduction-design.md §6).
const GCD: &str = r#"
fn gcd(a, b: Nat) -> Nat decreases b {
    match b {
        Zero => a,
        Succ(k) => gcd(Succ(k), nat::Nat::mod(a, Succ(k))),
    }
    on ?dec1 := nat::Nat::mod_lt(a, Succ(k));
}
"#;

#[test]
fn gcd_by_hand_obligation_computes_and_steps() {
    ok(&format!(
        "{GCD}\n\
         theorem gcd_12_8(): gcd(12, 8) = 4 {{ refl }}\n\
         theorem gcd_zero(a: Nat): gcd(a, 0) = a {{ refl }}"
    ));
}

/// Two calls, two obligations, both at a **two-argument** measure, and each
/// site has a constructor in one argument and a variable in the other. Both
/// `on`s and the `succ_add_le` lemma they needed came out with
/// docs/omega-measure-reduction-design.md §6: reduced, the obligations are
/// `a + b < Succ(a) + Succ(b)` over the atoms `xt.len()` and `yt.len()`.
const MERGE: &str = r#"
fn merge(xs, ys: List<Nat>) -> List<Nat> decreases xs.len() + ys.len() {
    match xs {
        Nil => ys,
        Cons(x, xt) => match ys {
            Nil => Cons(x, xt),
            Cons(y, yt) => match nat::Nat::le_dec(x, y) {
                Inl(_) => Cons(x, merge(xt, Cons(y, yt))),
                Inr(_) => Cons(y, merge(Cons(x, xt), yt)),
            },
        },
    }
}
"#;

#[test]
fn merge_with_two_obligations_at_a_sum_measure() {
    ok(&format!(
        "{MERGE}\ntheorem merge_demo(): merge([1, 4], [2, 3]) = [1, 2, 3, 4] {{ refl }}"
    ));
}

#[test]
fn merges_hand_discharges_were_replaced_by_the_closer_not_by_nothing() {
    // §6's companion assertion: `merge` above carries no `on`, and what
    // discharges its two sites is `omega`. Without the closer's modules the
    // same declaration is an ordinary unsolved goal again, so a regression
    // shows up as a refusal rather than as dead scaffolding.
    let mut e = base();
    let err = e
        .elab_module_source(
            "m",
            &format!("import logic;\nimport nat;\nimport list;\n{MERGE}"),
        )
        .expect_err("without `omega` the sites are ordinary goals");
    let msg = format!("{err}");
    assert!(msg.contains("dec1"), "{msg}");
}

#[test]
fn a_callee_postcondition_feeds_the_decrease() {
    // The parser shape (issue layer 2, the separate-lemma route): the
    // recursive call is on a suffix a callee returned, and the decrease is
    // that callee's lemma. `drop_eq(t, rest).len() <= rest.len()` is exactly
    // the obligation after `Succ`/`Succ` reduction. The `on` stays: the
    // measure head is opaque under any reduction
    // (docs/omega-measure-reduction-design.md §6).
    ok(r#"
        fn drop_eq(t: Nat, ts: List<Nat>) -> List<Nat> {
            match ts {
                Nil => Nil,
                Cons(h, rest) => match nat::Nat::eq_dec(t, h) { Inl(_) => drop_eq(t, rest), Inr(_) => Cons(h, rest) },
            }
        }

        theorem drop_eq_le(t: Nat, ts: List<Nat>): drop_eq(t, ts).len() <= ts.len() {
            match ts {
                Nil => trivial,
                Cons(h, rest) => match nat::Nat::eq_dec(t, h) {
                    Inl(_) => nat::Nat::le_succ_r(drop_eq(t, rest).len(), rest.len(), drop_eq_le(t, rest)),
                    Inr(_) => nat::Nat::le_refl(Succ(rest.len())),
                },
            }
        }

        fn runs(ts: List<Nat>) -> Nat decreases ts.len() {
            match ts {
                Nil => 0,
                Cons(t, rest) => Succ(runs(drop_eq(t, rest))),
            }
            on ?dec1 := drop_eq_le(t, rest);
        }

        theorem runs_demo(): runs([1, 1, 2, 3, 3, 3]) = 3 { refl }
    "#);
}

#[test]
fn omega_closes_arithmetic_obligations_through_the_refinement() {
    // Two nested matches on the measure's variable: the obligation is stated
    // at `Succ(Succ(l))`, which `omega` reads as `l + 2` now that an open
    // successor reflects as a sum. No `on` anywhere.
    ok(r#"
        theorem even_or_odd_wf(n: Nat): Nat::Even(n) ∨ Nat::Odd(n) decreases n {
            match n {
                Zero => Inl(trivial),
                Succ(k) => match k {
                    Zero => Inr(trivial),
                    Succ(l) => even_or_odd_wf(l),
                },
            }
        }

        fn halve_steps(n: Nat) -> Nat decreases n {
            match n {
                Zero => 0,
                Succ(k) => Succ(halve_steps(k)),
            }
        }

        theorem halve_three(): halve_steps(3) = 3 { refl }
    "#);
}

// -- negative controls --------------------------------------------------------

#[test]
fn a_call_that_grows_the_measure_is_refused_with_its_obligation() {
    let msg = elab_err(
        r#"
        fn bad(n: Nat) -> Nat decreases n {
            match n { Zero => 0, Succ(k) => bad(Succ(Succ(k))) }
        }
        "#,
    );
    assert!(msg.contains("must decrease the measure"), "{msg}");
    assert!(msg.contains("Succ(Succ(k)) < Succ(k)"), "{msg}");
    assert!(msg.contains("on ?dec1"), "{msg}");
}

#[test]
fn a_wrong_by_hand_discharge_is_refused_at_the_refined_statement() {
    let msg = elab_err(
        r#"
        fn f(n: Nat) -> Nat decreases n {
            match n { Zero => 0, Succ(k) => f(k) }
            on ?dec1 := trivial;
        }
        "#,
    );
    assert!(msg.contains("k < Succ(k)"), "{msg}");
}

#[test]
fn the_measure_must_be_a_nat() {
    let msg = any_err("import bool;\nfn f(n: Nat, b: Bool) -> Nat decreases b { 0 }");
    assert!(msg.contains("`Nat` is expected"), "{msg}");
}

#[test]
fn a_recursive_call_under_decreases_is_saturated() {
    let msg = elab_err(
        r#"
        fn f(n: Nat, m: Nat) -> Nat -> Nat decreases n {
            match n { Zero => λ (x: Nat) => x, Succ(k) => f(k) }
        }
        "#,
    );
    assert!(msg.contains("saturated"), "{msg}");
}

#[test]
fn without_omega_an_obligation_is_an_ordinary_unsolved_goal() {
    let mut e = base();
    let err = e
        .elab_module_source(
            "m",
            "import logic;\nimport nat;\n\
             fn f(n: Nat) -> Nat decreases n { match n { Zero => 0, Succ(k) => f(k) } }",
        )
        .expect_err("an undischarged obligation is refused");
    let msg = format!("{err}");
    assert!(msg.contains("dec1"), "{msg}");
}

#[test]
fn a_wrong_step_is_refused_by_the_kernel_not_the_measure() {
    // The measure argument is fine; the body is wrong. Generalizing over a
    // bound hands the arm nothing it did not have.
    let msg = any_err(&format!(
        "{GCD}\ntheorem wrong(): gcd(12, 8) = 5 {{ refl }}"
    ));
    assert!(!msg.is_empty());
}
