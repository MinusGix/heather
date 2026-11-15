//! `subst(h, e)`: eliminating a local variable along an equation, reverting
//! the locals whose types depend on it (`issues/subst-local-equation.md`,
//! `docs/tactics/equation-rewrite-design.md` §8).
//!
//! The tactic writes a `J` whose motive generalises the goal over the
//! variable and a telescope of reverted locals, so the axes of
//! `docs/testing-generated-terms.md` are varied: a **literal** right side and
//! a **neutral** one, an **open** element type, **checking** positions that
//! are not a theorem body, and a **negative control** beside the route that
//! `rewrite` refuses. Every accepted module has passed the kernel gate.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const HEAD: &str = "import logic; import nat; import list;\n";

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

// -- the route ---------------------------------------------------------------

#[test]
fn a_variable_on_the_right_is_replaced_by_the_left() {
    // `h : n = m` eliminates `m`, Lean's order: the goal is about `n` after.
    ok("theorem t(n, m: Nat, h: n = m, k: n <= 5): m <= 5 { subst(h, k) }");
}

#[test]
fn a_variable_on_the_left_is_replaced_by_a_literal() {
    ok("theorem t(n: Nat, h: n = 3): n + n = 6 { subst(h, refl) }");
}

#[test]
fn a_neutral_right_side() {
    ok("theorem t(n, m: Nat, h: n = Succ(m), k: Succ(m) <= 9): n <= 9 { subst(h, k) }");
}

#[test]
fn the_term_may_mention_a_local_declared_after_the_variable() {
    // No local moves: `x` stays in Γ, so `y` (bound after it) is in scope
    // for the motive's `t` with no reordering.
    ok("theorem t(x, y: Nat, h: x = y + 1, k: y + 1 <= 5): x <= 5 { subst(h, k) }");
}

#[test]
fn an_open_element_type() {
    ok("theorem t<A>(xs, ys: List<A>, h: xs = ys, k: xs.len() = 0): ys.len() = 0 { subst(h, k) }");
}

#[test]
fn the_variable_means_the_term_in_the_case() {
    // After `subst`, `n` is `3`: an annotation that says `n` says `3`.
    ok("theorem t(n: Nat, h: n = 3): n = 3 {
            subst(h, { let r: (n = 3) = refl; r })
        }");
}

#[test]
fn a_let_that_mentions_the_variable_follows_it() {
    // `k` was `n + 1`; in the case it is `3 + 1`, which `refl` closes.
    ok("theorem t(n: Nat, h: n = 3): n + 1 = 4 {
            let k = n + 1;
            subst(h, { let r: (k = 4) = refl; r })
        }");
}

// -- the dependent telescope ---------------------------------------------------

#[test]
fn a_dependent_local_is_reverted() {
    // `rewrite` refuses this goal: abstracting `n` leaves `v = v` at `v :
    // P(y)`, not a type. `subst` reverts `v` and binds it again at `P(0)`.
    ok("theorem t(P: Nat → Type, n: Nat, v: P(n), h: n = 0, k: (w: P(0)) → w = w): v = v {
            subst(h, k(v))
        }");
}

#[test]
fn rewrite_refuses_what_subst_reverts() {
    // The negative control for the test above.
    let e = bad("theorem t(P: Nat → Type, n: Nat, v: P(n), h: n = 0, k: (w: P(0)) → w = w): v = v {
            rewrite(h, k(v))
        }");
    assert!(e.contains("does not leave a type"), "{e}");
}

#[test]
fn reverting_follows_dependencies_transitively() {
    // `w` does not mention `n`, but its type mentions `v`, which does.
    ok("theorem t(P: Nat → Type, Q: (n: Nat) → P(n) → Type, n: Nat, v: P(n), w: Q(n, v), h: n = 0,
               k: (v: P(0)) → Q(0, v) → Nat): Nat {
            subst(h, k(v, w))
        }");
}

#[test]
fn the_equation_itself_is_eliminated() {
    // `h : a = b` eliminates `b` and `h` together: the goal `P(b, h)` is
    // `P(a, refl)` in the case — `J` itself, with the goal as its motive.
    ok("theorem t<A>(a, b: A, h: a = b, P: (y: A) → a = y → Type, w: P(a, refl)): P(b, h) {
            subst(h, w)
        }");
}

#[test]
fn a_mentioned_equation_with_the_variable_on_the_left_is_reverted() {
    // `h : n = Succ(m)` eliminates `n`; the goal mentions `h`, so `h` is bound
    // again at `Succ(m) = Succ(m)`.
    ok("theorem t(n, m: Nat, h: n = Succ(m), P: (y: Nat) → y = Succ(m) → Type,
               w: (q: Succ(m) = Succ(m)) → P(Succ(m), q)): P(n, h) {
            subst(h, w(h))
        }");
}

#[test]
fn a_later_independent_local_is_left_alone() {
    // `c` comes after `h` and mentions nothing eliminated.
    ok("theorem t(a, b: Nat, h: a = b, c: Nat, k: a + c <= 4): b + c <= 4 { subst(h, k) }");
}

#[test]
fn a_reverted_local_shadowed_by_a_let_stays_shadowed() {
    // `v` names the `let`, not the reverted binder: bound again, the binder
    // must not take the name back.
    ok("theorem t(P: Nat → Type, n: Nat, v: P(n), h: n = 0): Nat {
            let v = 5;
            subst(h, v)
        }");
}

// -- checking positions --------------------------------------------------------

#[test]
fn under_a_binder() {
    ok("theorem t(a, b: Nat, h: a = b): (k: Nat) → a + k = b + k { λ k => subst(h, refl) }");
}

#[test]
fn an_annotated_let_and_an_argument() {
    ok("theorem t(a, b: Nat, h: a = b, k: a <= 3): b <= 3 {
            let s: (b <= 3) = subst(h, k);
            s
        }");
    ok("theorem t2(a, b, c: Nat, h: a = b, k: a <= c, l: c <= 3): b <= 3 {
            b.le_trans(c, 3, subst(h, k), l)
        }");
}

// -- refusals ----------------------------------------------------------------

#[test]
fn neither_side_a_local_is_refused() {
    let e = bad("theorem t(a, b: Nat, h: a + 1 = b + 1, k: a <= 3): b <= 3 { subst(h, k) }");
    assert!(e.contains("neither side") && e.contains("rewrite(h, e)"), "{e}");
}

// A side that only reduces to a local is that local: `a + 0` is `a`
// (issues/pattern-variables-not-rewritable.md, where a pattern variable
// re-bound by a split is the case that needs it).
#[test]
fn a_side_reducing_to_a_local_is_eliminated() {
    ok("theorem t(a, b: Nat, h: a + 0 = b + 0, k: a <= 3): b <= 3 { subst(h, k) }");
}

#[test]
fn a_variable_occurring_on_the_other_side_is_refused() {
    let e = bad("theorem t(n: Nat, h: n = Succ(n)): False { subst(h, h) }");
    assert!(e.contains("neither side"), "{e}");
}

#[test]
fn a_right_side_mentioning_a_dependent_local_is_refused() {
    let e = bad("theorem t(P: Nat → Type, n: Nat, v: P(n), f: P(n) → Nat, h: n = f(v)): n = n {
            subst(h, refl)
        }");
    assert!(e.contains("depends on `n`"), "{e}");
}

#[test]
fn a_non_equation_is_refused() {
    let e = bad("theorem t(a, b: Nat, h: a <= b, k: a <= 3): b <= 3 { subst(h, k) }");
    assert!(e.contains("along an equation"), "{e}");
}

#[test]
fn inference_position_and_arity() {
    let e = bad("theorem t(a, b: Nat, h: a = b, k: a <= 3): b <= 3 { let s = subst(h, k); s }");
    assert!(e.contains("`subst(h, e)` needs an expected type"), "{e}");
    let e = bad("theorem t(a, b: Nat, h: a = b, k: a <= 3): b <= 3 { subst(h) }");
    assert!(e.contains("takes one equation"), "{e}");
}

#[test]
fn a_local_named_subst_is_an_ordinary_name() {
    ok("theorem t(subst: Nat → Nat, a: Nat): subst(a) = subst(a) { refl }");
}
