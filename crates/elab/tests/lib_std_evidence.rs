//! `:= infer` at a proposition goal: computation, then `evidence theorem`
//! rules, with `lib/std/num/nat.hthr`'s positivity rules as the customer
//! (`issues/infer-proposition-evidence.md`,
//! `docs/positivity-evidence-design.md` §6 A).
//!
//! What resolution produces is a generated term, so the axes of
//! `docs/testing-generated-terms.md` are varied: a literal and a **neutral**
//! operand (`0 < 5` and `0 < Succ(k)`, `0 < x * y` over parameters), a
//! **checking** position (the proof is used where the statement is the
//! expected type, and inside a `let`), rules that **nest** and mix with
//! computation, and a **negative control** beside each.
//!
//! The prefix is a semantic image, so `nat`'s rules reach these modules the
//! way they reach any importer: replayed from the image's events.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const HEAD: &str = "import logic; import nat;
theorem uses(n: Nat, h: 0 < n := infer): 0 < n { h }
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

// -- computation ------------------------------------------------------------

#[test]
fn a_goal_that_computes_to_true_is_discharged() {
    // A literal and a neutral operand under a `Succ`: both reduce to `True`.
    ok("theorem lit(): 0 < 5 { uses(5) }
theorem succ(k: Nat): 0 < Succ(k) { uses(Succ(k)) }
theorem plus_one(k: Nat): 0 < k + 1 { uses(k + 1) }
");
}

#[test]
fn a_goal_that_computes_to_false_is_not() {
    let e = bad("theorem zero(): 0 < 0 { uses(0) }\n");
    // The goal is shown as this call instantiated it, not as the callee's
    // written `0 < n`, and not decoded to `False`.
    assert!(e.contains("no instance for `Lt(0, 0)`"), "{e}");
    assert!(e.contains("no-rule"), "{e}");
}

// -- scope still comes first ------------------------------------------------

#[test]
fn a_local_proof_is_found_up_to_conversion() {
    ok("theorem exact(n: Nat, p: 0 < n): 0 < n { uses(n) }
theorem spelled(n: Nat, p: 1 <= n): 0 < n { uses(n) }
");
}

// -- rules ------------------------------------------------------------------

#[test]
fn library_rules_backchain_through_locals() {
    ok("theorem product(x, y: Nat, px: 0 < x, py: 0 < y): 0 < x * y { uses(x * y) }
theorem nested(x, y, z: Nat, px: 0 < x, py: 0 < y, pz: 0 < z): 0 < x * (y * z) {
    uses(x * (y * z))
}
theorem right_summand(a, b: Nat, pb: 0 < b): 0 < a + b { uses(a + b) }
");
}

#[test]
fn a_rule_premise_may_be_discharged_by_computation() {
    // `0 < Succ(k)` and `0 < y + 1` are premises no local states.
    ok("theorem mixed(x, k: Nat, px: 0 < x): 0 < x * Succ(k) { uses(x * Succ(k)) }
theorem in_let(x, y: Nat, px: 0 < x): 0 < x * (y + 1) {
    let p = uses(x * (y + 1));
    p
}
");
}

#[test]
fn a_rule_is_an_ordinary_theorem_too() {
    // Callable with every premise searched, or with one given by name.
    ok("theorem direct(x, y: Nat, px: 0 < x, py: 0 < y): 0 < x * y { Nat::mul_pos() }
theorem named(x, y: Nat, q: 1 <= y, px: 0 < x): 0 < x * y { Nat::mul_pos(pb := q) }
");
}

#[test]
fn a_rule_whose_premise_fails_is_not_taken() {
    let e = bad("theorem half(a, b: Nat, pa: 0 < a): 0 < a * b { uses(a * b) }\n");
    assert!(e.contains("no instance for `Lt(0, mul(a, b))`"), "{e}");
    assert!(e.contains("candidate: nat::Nat::mul_pos"), "{e}");
}

#[test]
fn a_rule_declared_here_is_used_here() {
    // A user rule beside the library's: two rules about `Nat::Lt` coexist,
    // which the class registry's (class, carrier head) key would refuse.
    ok("fn twice(n: Nat) -> Nat { n + n }
evidence theorem twice_pos({n: Nat}, p: 0 < n := infer): 0 < twice(n) {
    uses(n + n)
}
theorem t(n, m: Nat, p: 0 < n, q: 0 < m): 0 < twice(n) * m { uses(twice(n) * m) }
");
}

// -- what a rule may be -----------------------------------------------------

#[test]
fn an_explicit_parameter_is_refused() {
    let e = bad("evidence theorem r(n: Nat, p: 0 < n := infer): 0 < n + 0 { p }\n");
    assert!(e.contains("`n` is an explicit parameter"), "{e}");
}

#[test]
fn a_premise_no_smaller_than_the_conclusion_is_refused() {
    // Provable, and a search through it would grow the goal forever.
    let e = bad(
        "evidence theorem grows({n: Nat}, p: 0 < Succ(Succ(n)) := infer): 0 < Succ(n) { trivial }\n",
    );
    assert!(e.contains("not smaller than its conclusion"), "{e}");
}

#[test]
fn a_conclusion_that_is_not_a_relation_is_refused() {
    let e = bad("evidence theorem r({n: Nat}): n = n { refl }\n");
    assert!(e.contains("not a relation applied to arguments"), "{e}");
}

#[test]
fn evidence_marks_only_a_theorem() {
    let e = bad("evidence fn f(n: Nat) -> Nat { n }\n");
    assert!(e.contains("`evidence` marks a `theorem`"), "{e}");
    // The word stays an ordinary name everywhere else.
    ok("record W { evidence: Nat }
fn read(w: W) -> Nat { w.evidence }
");
}
