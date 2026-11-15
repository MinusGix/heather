//! `lib/std/num/nat.hthr`'s parity section — `half`, `Even`, `Odd` and their kit
//! (`issues/nat-parity-and-half.md`).
//!
//! These are the library's first declarations whose recursion reads two past
//! values (`docs/language/recursion/course-of-values-recursion-design.md`), so what is asserted
//! here is not only that the lemmas hold but that the *lowering* kept the two
//! properties the whole section was written for:
//!
//! - it is still one `elim_Nat`, so closed arguments **compute** — §1;
//! - the propositions **reduce**, so `Even(4)` is `trivial` and `¬ Even(7)` is
//!   the hypothesis itself — §2;
//! - the kit holds at **open** arguments, where nothing computes and the
//!   proofs are the only thing carrying the weight — §3;
//! - the hypotheses that look decorative are load-bearing — §4.
//!
//! Every positive has a negative control beside it, per
//! `docs/testing-generated-terms.md`. The controls matter more than usual
//! here: a tupled recursion that slid its window the wrong way still checks,
//! still computes, and answers `half(7) = 4`.

use crate::support;
use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = support::library(&[("logic", LOGIC), ("bool", BOOL), ("nat", NAT)]);
    if !extra.is_empty() {
        let src = format!("import logic;\nimport bool;\nimport nat;\n{extra}");
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
        Ok(_) => panic!("expected this to be refused:\n{extra}"),
        Err(e) => e,
    }
}

// ---------------------------------------------------------------------------
// 1. `half` computes. The property the tupling exists to preserve: the emitted
//    term is one `elim_Nat`, so a closed argument reduces and `refl` proves it.

#[test]
fn half_computes() {
    ok("theorem a(): Nat::half(0) = 0 { refl }
theorem b(): Nat::half(1) = 0 { refl }
theorem c(): Nat::half(2) = 1 { refl }
theorem d(): Nat::half(7) = 3 { refl }
theorem e(): Nat::half(8) = 4 { refl }");
}

/// A course-of-values `half` at a large closed argument was the first
/// reproducer of issues/kernel-native-depth-budget.md — one native re-entry
/// of the evaluator per level, and an abort long before the fuel was spent.
/// It is a *success* control rather than a refusal one: the run-program
/// arithmetic (issues/nat-run-algebra-primitives.md) classifies this fold and
/// iterates it over the run instead of descending it, so the depth this used
/// to cost is no longer spent at all (docs/kernel/native-depth-budget-design.md §2).
#[test]
fn half_computes_at_a_large_closed_argument() {
    ok("theorem t(): Nat::half(1048576) = 524288 { refl }");
}

/// The control that says the window slides the right way. A tuple assembled
/// one component off computes something at every argument — it is only *which*
/// value that gives it away, and `half(7)` is where an off-by-one shows.
#[test]
fn half_computes_the_right_values() {
    bad("theorem t(): Nat::half(7) = 4 { refl }");
    bad("theorem t(): Nat::half(8) = 3 { refl }");
    bad("theorem t(): Nat::half(2) = 2 { refl }");
}

// ---------------------------------------------------------------------------
// 2. `Even`/`Odd` reduce, which is why they are recursions into `Type` and not
//    `∃k, add(k, k) = n`. Both directions: the true one is `trivial` and the
//    false one is `False`, so its refutation is the hypothesis.

#[test]
fn parity_reduces_at_closed_arguments() {
    ok("theorem a(): Nat::Even(0) { trivial }
theorem b(): Nat::Even(4) { trivial }
theorem c(): Nat::Odd(1) { trivial }
theorem d(): Nat::Odd(7) { trivial }
theorem e(): ¬ Nat::Even(7) { λ (h: Nat::Even(7)) => h }
theorem f(): ¬ Nat::Odd(4) { λ (h: Nat::Odd(4)) => h }");
}

#[test]
fn parity_reduces_to_the_right_side() {
    bad("theorem t(): Nat::Even(7) { trivial }");
    bad("theorem t(): Nat::Odd(4) { trivial }");
    bad("theorem t(): Nat::Even(0) -> False { λ (h: Nat::Even(0)) => h }");
}

// ---------------------------------------------------------------------------
// 3. The kit at OPEN arguments, where nothing reduces. Each positive is
//    followed by the same statement attempted by `refl`/`trivial`, which is
//    what makes the positive non-vacuous.

#[test]
fn the_kit_holds_at_open_arguments() {
    ok("theorem bound(n: Nat): n.half() <= n { n.half_le() }
theorem inverts(n: Nat): n.add(n).half() = n { n.half_double() }
theorem doubles(n: Nat): Nat::Even(n.add(n)) { n.even_double() }
theorem total(n: Nat): Or<Nat::Even(n), Nat::Odd(n)> { n.even_or_odd() }
theorem exclusive(n: Nat): ¬ And<Nat::Even(n), Nat::Odd(n)> { n.not_even_and_odd() }
theorem back(n: Nat, h: Nat::Even(n)): n.half().add(n.half()) = n { n.half_add_half(h) }");
}

#[test]
fn the_kit_is_not_definitional_at_open_arguments() {
    bad("theorem t(n: Nat): n.half() <= n { trivial }");
    bad("theorem t(n: Nat): n.add(n).half() = n { refl }");
    bad("theorem t(n: Nat): Nat::Even(n.add(n)) { trivial }");
    bad("theorem t(n: Nat, h: Nat::Even(n)): n.half().add(n.half()) = n { refl }");
}

/// One step of the recursion at an open argument: `Even(Succ(Succ(n)))` and
/// `Even(n)` are the SAME type, which is the definitional inversion the
/// two-step shape is chosen for and what makes every step arm above a bare
/// self-call. Its neighbour one `Succ` along is *not* definitional, and the
/// control is what records that this is the real boundary.
#[test]
fn two_steps_are_definitional_and_one_is_not() {
    ok("theorem up(n: Nat, h: Nat::Even(n)): Nat::Even(Succ(Succ(n))) { h }
theorem down(n: Nat, h: Nat::Even(Succ(Succ(n)))): Nat::Even(n) { h }
theorem odd_up(n: Nat, h: Nat::Odd(n)): Nat::Odd(Succ(Succ(n))) { h }");
    bad("theorem t(n: Nat, h: Nat::Even(n)): Nat::Odd(Succ(n)) { h }");
}

// ---------------------------------------------------------------------------
// 4. The decision, and the hypotheses.

/// `even_dec` is a `fn` and not a `theorem`, so it unfolds in conversion and
/// the decision at a closed argument *computes* — the property `le_dec` has
/// and the reason neither is a `theorem`. The instance is value-generic, so a
/// use site at an open `n` writes no arguments at all.
#[test]
fn parity_decides_and_resolves() {
    ok("theorem open(n: Nat): Or<Nat::Even(n), ¬ Nat::Even(n)> { decide<Nat::Even(n)>() }
theorem named(n: Nat): Or<Nat::Even(n), ¬ Nat::Even(n)> { n.even_dec() }
theorem closed(): Or<Nat::Even(4), ¬ Nat::Even(4)> { Inl(trivial) }
theorem resolved(n: Nat, no: ¬ Nat::Odd(n)): Nat::Even(n) { or_resolve(n.even_or_odd(), no) }");
}

/// `half_add_half` needs its hypothesis, and the odd argument is why: `half`
/// throws the remainder away, so the unconditional reading is false. The open
/// attempt has nothing to supply, and the closed counterexample beside it is
/// what makes the first more than a typing accident.
#[test]
fn halving_inverts_only_on_an_even_argument() {
    bad("theorem t(n: Nat): n.half().add(n.half()) = n { n.half_add_half(trivial) }");
    bad("theorem t(): Nat::half(3).add(Nat::half(3)) = 3 { refl }");
    ok("theorem why(): Nat::half(3).add(Nat::half(3)) = 2 { refl }");
}
