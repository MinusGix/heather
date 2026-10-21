//! `rewrite(h₁, …, hₙ, e)`: rewriting a goal along equations without
//! writing `j`'s motive (`issues/equation-rewrite-in-goal.md`,
//! `docs/equation-rewrite-design.md`).
//!
//! The tactic writes a term — a `J` along `sym(h)` whose motive is the goal
//! with the left side abstracted — so the axes of
//! `docs/testing-generated-terms.md` are varied: a **literal** left side and a
//! **neutral** one, an **open** element type, a **checking** position that is
//! not a theorem body (an argument a call instantiated, an annotated `let`,
//! under a binder), and a **negative control** beside each route. Every
//! accepted module has passed the kernel gate, so a wrong motive is a
//! rejection here, not a silent pass.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
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
fn equations_rewrite_left_to_right_in_turn() {
    ok("theorem t(k, n, m: Nat, h: n <= m): k + n <= k + m {
            rewrite(k.add_comm(n), k.add_comm(m), k.add_le_mono_r(n, m, h))
        }");
}

#[test]
fn a_later_equation_sees_what_an_earlier_one_left() {
    // The second equation's left side exists only after the first rewrite.
    ok("theorem t(a, b, c: Nat, p: a = b, q: b = c, r: c <= 5): a <= 5 {
            rewrite(p, q, r)
        }");
}

#[test]
fn a_rewrite_that_closes_the_goal_ends_in_refl() {
    ok("theorem t(f: Nat → Nat, {a, b: Nat}, p: a = b): f(a) = f(b) { rewrite(p, refl) }");
}

#[test]
fn sym_rewrites_right_to_left() {
    ok("theorem t(f: Nat → Nat, {a, b: Nat}, p: a = b, q: f(a) = 0): f(b) = 0 {
            rewrite(sym(p), q)
        }");
}

#[test]
fn a_literal_left_side_is_rewritten_where_it_is_written() {
    // Literal on the left: `0 + n = n` rewrites the `0 + n`, and a bare `n`
    // elsewhere in the goal is a different term and stays.
    ok("theorem t(n: Nat, h: n <= n): 0 + n <= n { rewrite(n.add_left_zero(), h) }");
    // A literal *right* side: the goal mentions `n`, the case is about `3`.
    ok("theorem t2(n: Nat, h: n = 3): n + n = 6 { rewrite(h, refl) }");
}

#[test]
fn an_open_element_type_rewrites_list_terms() {
    ok("theorem t<A>(xs, ys, zs: List<A>, h: xs = ys):
            (xs ++ zs).len() = ys.len() + zs.len()
        {
            rewrite(h, ys.len_append(zs))
        }");
}

#[test]
fn a_function_variable_is_a_left_side_like_any_other() {
    ok("theorem t<A, B>(f, g: A → B, x: A, h: f = g, q: g(x) = g(x)): f(x) = g(x) {
            rewrite(h, q)
        }");
}

#[test]
fn occurrences_under_a_binder_are_rewritten() {
    ok("theorem t(n, m: Nat, h: n = m, k: (x: Nat) → x + m = m + x): (x: Nat) → x + n = n + x {
            rewrite(h, k)
        }");
}

#[test]
fn an_argument_position_is_a_checking_position() {
    // The expected type is the callee's parameter type, instantiated by the
    // call's other arguments.
    ok("theorem t(k, n, m: Nat, h: n <= m): n + k <= m + k + 0 {
            (n + k).le_trans(m + k, m + k + 0,
                rewrite(n.add_comm(k), m.add_comm(k), k.add_le_mono_l(n, m, h)),
                (m + k).le_refl())
        }");
}

#[test]
fn an_annotated_let_is_a_checking_position() {
    ok("theorem t(a, b: Nat, p: a = b, h: b <= 3): a <= 3 {
            let s: (a <= 3) = rewrite(p, h);
            s
        }");
}

#[test]
fn a_family_index_is_rewritten_in_a_dependent_goal() {
    ok("theorem t(P: Nat → Type, n, m: Nat, h: n = m, v: P(m)): P(n) { rewrite(h, v) }");
}

// -- occurrences -------------------------------------------------------------

#[test]
fn at_selects_occurrences_counted_left_to_right() {
    // `n` occurs twice; the motive keeps the first.
    ok("theorem t(n, m: Nat, h: n = m, k: n <= m): n <= n { rewrite(h, k, at := 2) }");
    ok("theorem t2(n, m: Nat, h: n = m, k: m <= n): n <= n { rewrite(h, k, at := [1]) }");
    ok("theorem t3(n, m: Nat, h: n = m, k: m <= m): n <= n { rewrite(h, k, at := [1, 2]) }");
}

#[test]
fn every_occurrence_is_rewritten_without_at() {
    // The control for the test above: the same goal and the same `k` fails
    // when every occurrence moves.
    let e = bad("theorem t(n, m: Nat, h: n = m, k: n <= m): n <= n { rewrite(h, k) }");
    assert!(e.contains("m <= m") || e.contains("Le(m, m)"), "{e}");
}

#[test]
fn an_occurrence_past_the_end_is_refused_with_the_count() {
    let e = bad("theorem t(n, m: Nat, h: n = m, k: n <= m): n <= n { rewrite(h, k, at := 3) }");
    assert!(e.contains("`at := 3`") && e.contains("2 occurrence"), "{e}");
}

#[test]
fn at_with_several_equations_is_refused() {
    let e = bad("theorem t(a, b, c: Nat, p: a = b, q: b = c, r: c <= 5): a <= 5 {
            rewrite(p, q, r, at := 1)
        }");
    assert!(e.contains("nest the one it is for"), "{e}");
}

#[test]
fn at_takes_positive_numerals() {
    let e = bad("theorem t(n, m: Nat, h: n = m, k: n <= m): n <= n { rewrite(h, k, at := 0) }");
    assert!(e.contains("counted from 1"), "{e}");
}

// -- refusals ----------------------------------------------------------------

#[test]
fn a_goal_that_mentions_only_the_right_side_hints_sym() {
    let e = bad("theorem t(f: Nat → Nat, {a, b: Nat}, p: a = b, q: f(a) = 0): f(b) = 0 {
            rewrite(p, q)
        }");
    assert!(e.contains("does not mention the equation's left side `a`"), "{e}");
    assert!(e.contains("mentions its right side `b`") && e.contains("sym("), "{e}");
}

#[test]
fn a_goal_that_mentions_neither_side_gives_no_hint() {
    let e = bad("theorem t(f: Nat → Nat, {a, b, c: Nat}, p: a = b, q: f(c) = 0): f(c) = 0 {
            rewrite(p, q)
        }");
    assert!(e.contains("does not mention the equation's left side `a`"), "{e}");
    assert!(!e.contains("hint"), "{e}");
}

#[test]
fn a_proof_of_a_non_equation_is_refused() {
    let e = bad("theorem t(a, b: Nat, p: a <= b, q: b <= 3): a <= 3 { rewrite(p, q) }");
    assert!(e.contains("rewrites along an equation"), "{e}");
}

#[test]
fn a_motive_that_is_not_a_type_is_refused_before_the_kernel() {
    // `v : P(n)` stays put while its index would move, so the abstraction
    // leaves `Id(P(y), v, v)`, which is not a type.
    let e = bad("theorem t(P: Nat → Type, n, m: Nat, h: n = m, v: P(n)): v = v { rewrite(h, refl) }");
    assert!(e.contains("does not leave a type"), "{e}");
}

#[test]
fn a_wrong_body_is_refused() {
    bad("theorem t(f: Nat → Nat, {a, b: Nat}, p: a = b, q: f(a) = 0): f(b) = 0 {
            rewrite(sym(p), refl)
        }");
}

#[test]
fn inference_position_needs_an_expected_type() {
    let e = bad("theorem t(f: Nat → Nat, {a, b: Nat}, p: a = b): f(a) = f(b) {
            let x = rewrite(p, refl);
            x
        }");
    assert!(e.contains("needs an expected type"), "{e}");
}

#[test]
fn rewrite_needs_a_body_after_its_equations() {
    let e = bad("theorem t(f: Nat → Nat, {a, b: Nat}, p: a = b): f(a) = f(b) { rewrite(p) }");
    assert!(e.contains("one or more equations and then the proof"), "{e}");
}

#[test]
fn a_local_named_rewrite_is_an_ordinary_name() {
    ok("theorem t(rewrite: Nat → Nat → Nat, a: Nat): rewrite(a, a) = rewrite(a, a) {
            let r: (rewrite(a, a) = rewrite(a, a)) = refl;
            r
        }");
    ok("fn rewrite(a, b: Nat) → Nat { a + b }
        theorem t(a: Nat): rewrite(a, 0) = a { refl }");
}

// -- unapplied lemmas: arguments found by matching ----------------------------

#[test]
fn an_unapplied_lemma_takes_its_arguments_from_the_goal() {
    ok("theorem t(n: Nat, h: n <= 5): 0 + n <= 5 { rewrite(Nat::add_left_zero, h) }");
}

#[test]
fn a_partly_applied_lemma_matches_the_rest() {
    // `Nat::add_comm(k)` still takes `b`: the first `k + _` fixes it, so the
    // second call reaches the other side.
    ok("theorem t(k, n, m: Nat, h: n <= m): k + n <= k + m {
            rewrite(Nat::add_comm(k), Nat::add_comm(k), k.add_le_mono_r(n, m, h))
        }");
}

#[test]
fn a_generic_lemma_matches_at_an_open_element_type() {
    ok("theorem t<A>(xs: List<A>, h: xs.len() = 3): (xs ++ Nil).len() = 3 {
            rewrite(List::append_nil, h)
        }");
}

#[test]
fn the_first_instance_is_rewritten_everywhere_and_only_it() {
    // `0 + a` fixes the instance; `0 + b` is another instance and stays.
    ok("theorem t(a, b: Nat, h: a + (0 + b) <= a + (0 + b)): (0 + a) + (0 + b) <= (0 + a) + (0 + b) {
            rewrite(Nat::add_left_zero, h)
        }");
    let e = bad("theorem t(a, b: Nat, h: a + b <= a + b): (0 + a) + (0 + b) <= (0 + a) + (0 + b) {
            rewrite(Nat::add_left_zero, h)
        }");
    assert!(e.contains("is expected here") || e.contains("kernel rejected"), "{e}");
}

#[test]
fn a_hypothesis_with_a_telescope_is_a_lemma_too() {
    ok("theorem t(f: Nat → Nat, w: (x: Nat) → f(x) = x, n: Nat, h: n <= 2): f(n) <= 2 {
            rewrite(w, h)
        }");
}

#[test]
fn a_left_side_that_is_an_argument_is_refused() {
    let e = bad("theorem t(w: (x: Nat) → x = x + 0, n: Nat, h: n + 0 <= 2): n <= 2 { rewrite(w, h) }");
    assert!(e.contains("one of its own arguments"), "{e}");
}

#[test]
fn an_argument_only_the_right_side_mentions_is_asked_for() {
    let e = bad("theorem t(w: (x, y: Nat) → x + 0 = x + y * 0, n: Nat, h: n <= 2): n + 0 <= 2 {
            rewrite(w, h)
        }");
    assert!(e.contains("argument 2") && e.contains("give it explicitly"), "{e}");
    ok("theorem t(w: (x, y: Nat) → x + 0 = x + y * 0, n: Nat, h: n + 7 * 0 <= 2): n + 0 <= 2 {
            rewrite(w(n, 7), h)
        }");
}

#[test]
fn no_instance_is_an_error_naming_the_goal() {
    let e = bad("theorem t(n: Nat, h: n <= 5): n + 0 <= 5 { rewrite(Nat::add_left_zero, h) }");
    assert!(e.contains("no subterm of the goal") && e.contains("is an instance"), "{e}");
}

// -- occurrences up to conversion -------------------------------------------

#[test]
fn an_occurrence_spelled_differently_is_found_by_conversion() {
    // `double(a + 0)` has the left side's head and converts to `double(a)`.
    ok("fn double(n: Nat) → Nat { n + n }
        theorem t(a: Nat, h: double(a) = 4, k: 4 <= 4): double(a + 0) <= 4 { rewrite(h, k) }");
}

#[test]
fn a_same_headed_term_that_does_not_convert_stays() {
    // The control: `double(b)` shares the head and is left alone, so the goal
    // after the rewrite still mentions it. Neutral arguments, so nothing
    // decides `<=` by computing.
    ok("fn double(n: Nat) → Nat { n + n }
        theorem t(a, b: Nat, h: double(a) = 4, k: 4 <= double(b)): double(a + 0) <= double(b) {
            rewrite(h, k)
        }");
    bad("fn double(n: Nat) → Nat { n + n }
         theorem t(a, b: Nat, h: double(a) = 4, k: 4 <= 4): double(a + 0) <= double(b) { rewrite(h, k) }");
}

#[test]
fn every_spelling_is_rewritten_together() {
    ok("fn double(n: Nat) → Nat { n + n }
        theorem t(a: Nat, h: double(a) = 4, k: 4 <= 4): double(a + 0) <= double(a) { rewrite(h, k) }");
}

// -- in a hypothesis: `rewrite(h, …, in := hyp)` -------------------------------

#[test]
fn a_hypothesis_is_rewritten_left_to_right() {
    // Inference position: the result's type is what the rewrite left.
    ok("theorem t(a, b: Nat, p: a = b, h: a <= 3): b <= 3 {
            let moved = rewrite(p, in := h);
            moved
        }");
    // Checking position, through the inference fallback.
    ok("theorem t2(a, b: Nat, p: a = b, h: a <= 3): b <= 3 { rewrite(p, in := h) }");
}

#[test]
fn a_rewritten_hypothesis_is_an_argument() {
    ok("theorem t(a, b, c: Nat, p: a = b, h: a <= c, k: c <= 3): b <= 3 {
            b.le_trans(c, 3, rewrite(p, in := h), k)
        }");
}

#[test]
fn hypothesis_equations_apply_in_turn() {
    ok("theorem t(a, b, c: Nat, p: a = b, q: b = c, h: a <= 5): c <= 5 {
            let moved = rewrite(p, q, in := h);
            moved
        }");
}

#[test]
fn a_hypothesis_rewrite_instantiates_an_unapplied_lemma() {
    ok("theorem t(n, k: Nat, h: n + k <= 3): k + n <= 3 {
            let moved = rewrite(Nat::add_comm, in := h);
            moved
        }");
}

#[test]
fn a_hypothesis_over_an_open_element_type() {
    ok("theorem t<A>(xs, ys, zs: List<A>, p: xs = ys, h: (xs ++ zs).len() = 0): (ys ++ zs).len() = 0 {
            let moved = rewrite(p, in := h);
            moved
        }");
}

#[test]
fn a_dependent_hypothesis_is_transported() {
    // `v : P(n)` itself is the hypothesis, a family index rewritten.
    ok("theorem t(P: Nat → Type, n, m: Nat, h: n = m, v: P(n)): P(m) {
            let moved = rewrite(h, in := v);
            moved
        }");
}

#[test]
fn at_selects_occurrences_in_a_hypothesis() {
    ok("theorem t(n, m: Nat, h: n = m, k: n <= n): n <= m {
            let moved = rewrite(h, in := k, at := 2);
            moved
        }");
    // The control: every occurrence moves without `at`.
    let e = bad("theorem t(n, m: Nat, h: n = m, k: n <= n): n <= m {
            let moved = rewrite(h, in := k);
            moved
        }");
    assert!(e.contains("m <= m") || e.contains("Le(m, m)"), "{e}");
}

#[test]
fn a_hypothesis_without_the_left_side_hints_sym() {
    let e = bad("theorem t(a, b: Nat, p: a = b, h: b <= 3): a <= 3 { rewrite(p, in := h) }");
    assert!(e.contains("the hypothesis's type") && e.contains("does not mention the equation's left side `a`"), "{e}");
    assert!(e.contains("sym("), "{e}");
    // With `sym` it is accepted: the direction is never guessed.
    ok("theorem t(a, b: Nat, p: a = b, h: b <= 3): a <= 3 { rewrite(sym(p), in := h) }");
}

#[test]
fn hypothesis_rewrite_refusals() {
    let e = bad("theorem t(a, b, c: Nat, p: a = b, q: b = c, h: a <= 5): c <= 5 {
            rewrite(p, q, in := h, at := 1)
        }");
    assert!(e.contains("rewrite one at a time"), "{e}");
    let e = bad("theorem t(a: Nat, h: a <= 5): a <= 5 { rewrite(in := h) }");
    assert!(e.contains("one or more equations"), "{e}");
    let e = bad("theorem t(a, b: Nat, p: a = b, h: a <= 5): b <= 5 { rewrite(p, in := h, by := 2) }");
    assert!(e.contains("not this `by :=`"), "{e}");
}

#[test]
fn a_bare_rewrite_in_inference_position_points_at_in() {
    let e = bad("theorem t(a, b: Nat, p: a = b, h: a <= 3): b <= 3 { let m = rewrite(p, h); m }");
    assert!(e.contains("needs an expected type") && e.contains("in := hyp"), "{e}");
}
