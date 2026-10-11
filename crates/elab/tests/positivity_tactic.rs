//! The `positivity` tactic: `:= infer`'s proposition search (locals,
//! computation, `evidence theorem` rules) run at an expected goal, with
//! `omega` as the fallback at every subgoal the rules cannot close
//! (`issues/positivity-tactic.md`, `docs/positivity-evidence-design.md` §10).
//!
//! What the tactic produces is a generated term, so the axes of
//! `docs/testing-generated-terms.md` are varied: a literal and a **neutral**
//! operand, a second carrier (`Int`, which has no rules and is omega's
//! alone), a **checking** position (an argument whose expected type a call
//! instantiated, and a `let`), and a **negative control** beside each route.
//! Cheapness is asserted, not hoped for: the audit reports count the omega
//! calls a proof kept.

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
    ("omega", include_str!("../../../lib/std/omega.hthr")),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn base() -> Elaborator {
    BASE.with(|base| {
        base.get_or_init(|| {
            let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            let elab = support::semantic_test_base(MODULES);
            elab.take_omega_reports();
            elab.semantic_image()
        })
        .elaborator()
    })
}

const HEAD: &str = "import logic; import nat; import int; import omega;
theorem needs(n: Nat, h: 0 < n): 0 < n { h }
";

/// Elaborate `src` after `head` and return how many `omega` calls the
/// accepted module kept, counted in units of one written `omega` (a
/// declaration reports each of its certificates more than once).
fn ok_with(head: &str, src: &str) -> usize {
    let reports = |head: &str, src: &str| {
        let src = format!("{head}{src}");
        let mut elab = base();
        if let Err(err) = elab.elab_module_source("client", &src) {
            panic!("expected success, got: {}", err.render(&src));
        }
        elab.take_omega_reports().len()
    };
    let n = reports(head, src);
    if n == 0 {
        return 0;
    }
    let one = reports(HEAD, "theorem one(n: Nat, h: 3 <= n): 1 < n { omega }\n");
    assert!(one > 0 && n % one == 0, "{n} reports is not a whole number of omega calls of {one} each");
    n / one
}

fn ok(src: &str) -> usize {
    ok_with(HEAD, src)
}

fn bad_with(head: &str, src: &str) -> String {
    let src = format!("{head}{src}");
    match base().elab_module_source("client", &src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(&src),
    }
}

fn bad(src: &str) -> String {
    bad_with(HEAD, src)
}

// -- the cheap routes run no omega ------------------------------------------

#[test]
fn a_local_computation_or_rule_needs_no_omega() {
    // A literal, a neutral operand under `Succ`, a local up to conversion,
    // and a product whose factors are a local and a computation.
    let omegas = ok("theorem lit(): 0 < 5 { positivity }
theorem succ(k: Nat): 0 < Succ(k) { positivity }
theorem local(n: Nat, p: 1 <= n): 0 < n { positivity }
theorem product(x, k: Nat, px: 0 < x): 0 < x * (k + 1) { positivity }
");
    assert_eq!(omegas, 0, "the cheap routes closed every goal");
}

// -- omega at the leaves ----------------------------------------------------

#[test]
fn omega_closes_a_linear_goal_no_rule_reaches() {
    // `3 <= n` is not `0 < n` by conversion; omega reads it.
    let omegas = ok("theorem lower(n: Nat, h: 3 <= n): 0 < n { positivity }\n");
    assert_eq!(omegas, 1);
}

#[test]
fn rules_split_a_nonlinear_goal_and_omega_closes_its_factors() {
    // Omega alone treats `a * b` as an opaque atom and cannot prove this;
    // `Nat::mul_pos` splits it, and each factor is a linear leftover.
    let omegas = ok("theorem product(a, b: Nat, ha: 2 <= a, hb: 5 <= b): 0 < a * b { positivity }\n");
    assert_eq!(omegas, 2, "one omega per factor, none at the product");
    // The negative control: omega on its own is stuck on the same goal.
    let e = bad("theorem product(a, b: Nat, ha: 2 <= a, hb: 5 <= b): 0 < a * b { omega }\n");
    assert!(e.contains("`omega` got stuck"), "{e}");
}

#[test]
fn only_the_leaf_a_rule_cannot_close_reaches_omega() {
    // `0 < x` is a local and `0 < y` is omega's: one call, at `y`.
    let omegas = ok("theorem mixed(x, y, z: Nat, px: 0 < x, hy: y = z + 2): 0 < x * (y * Succ(z)) {
    positivity
}
");
    assert_eq!(omegas, 1);
}

#[test]
fn a_carrier_without_rules_is_omega_alone() {
    let omegas = ok("theorem int_lower(x: Int, h: OfNat(2) <= x): OfNat(0) < x { positivity }\n");
    assert_eq!(omegas, 1);
}

// -- checking positions -----------------------------------------------------

#[test]
fn the_tactic_proves_an_argument_a_call_instantiated() {
    ok("theorem arg(a, b: Nat, ha: 2 <= a, hb: 0 < b): 0 < a * b { needs(a * b, positivity) }
theorem in_let(a, b: Nat, ha: 2 <= a, hb: 0 < b): 0 < a * b {
    let p: (0 < a * b) = positivity;
    p
}
");
}

// -- failures ---------------------------------------------------------------

#[test]
fn an_unprovable_goal_reports_the_whole_search() {
    let e = bad("theorem product(a, b: Nat, ha: 2 <= a): 0 < a * b { positivity }\n");
    assert!(e.contains("`positivity` could not prove"), "{e}");
    assert!(e.contains("candidate: nat::Nat::mul_pos"), "{e}");
    // The factor `b` is omega's, and omega is stuck on it; so, then, is the
    // product. Each stuck call is one line, not omega's whole report.
    assert!(e.contains("omega: `omega` got stuck"), "{e}");
    assert!(!e.contains("residual"), "{e}");
}

#[test]
fn a_goal_omega_was_stuck_on_is_not_retried() {
    // Both summand rules ask for `0 < a * b`'s factors; the failing one is
    // tried by omega once, then remembered.
    let e = bad("theorem twice(a, b: Nat): 0 < a * b + a * b { positivity }\n");
    assert!(e.contains("omega: already stuck on this goal"), "{e}");
}

#[test]
fn a_false_goal_is_refused() {
    let e = bad("theorem zero(): 0 < 0 { positivity }\n");
    assert!(e.contains("`positivity` could not prove"), "{e}");
}

#[test]
fn without_omega_the_cheap_routes_still_run() {
    let head = "import logic; import nat;\n";
    let omegas = ok_with(head, "theorem product(x, y: Nat, px: 0 < x, py: 0 < y): 0 < x * y { positivity }\n");
    assert_eq!(omegas, 0);
    let e = bad_with(head, "theorem lower(n: Nat, h: 3 <= n): 0 < n { positivity }\n");
    assert!(e.contains("omega: not imported"), "{e}");
}

#[test]
fn a_local_named_positivity_is_an_ordinary_name() {
    ok("theorem shadow(n: Nat, positivity: 0 < n): 0 < n { positivity }\n");
}

