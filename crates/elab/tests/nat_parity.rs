//! `lib/std/nat.hthr`'s parity section — `half`, `Even`, `Odd` and their kit
//! (`issues/nat-parity-and-half.md`).
//!
//! These are the library's first declarations whose recursion reads two past
//! values (`docs/course-of-values-recursion-design.md`), so what is asserted
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

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [("logic", LOGIC), ("bool", BOOL), ("nat", NAT)] {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => format!("{name}: {msg}"),
                other => format!("{name}: {other}"),
            });
        }
    }
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
    ok("theorem a(): half(0) = 0 { refl }
theorem b(): half(1) = 0 { refl }
theorem c(): half(2) = 1 { refl }
theorem d(): half(7) = 3 { refl }
theorem e(): half(8) = 4 { refl }");
}

/// A course-of-values `half` at a large closed argument was the first
/// reproducer of issues/kernel-native-depth-budget.md — one native re-entry
/// of the evaluator per level, and an abort long before the fuel was spent.
/// It is a *success* control rather than a refusal one: the run-program
/// arithmetic (issues/nat-run-algebra-primitives.md) classifies this fold and
/// iterates it over the run instead of descending it, so the depth this used
/// to cost is no longer spent at all (docs/native-depth-budget-design.md §2).
#[test]
fn half_computes_at_a_large_closed_argument() {
    ok("theorem t(): half(1048576) = 524288 { refl }");
}

/// The control that says the window slides the right way. A tuple assembled
/// one component off computes something at every argument — it is only *which*
/// value that gives it away, and `half(7)` is where an off-by-one shows.
#[test]
fn half_computes_the_right_values() {
    bad("theorem t(): half(7) = 4 { refl }");
    bad("theorem t(): half(8) = 3 { refl }");
    bad("theorem t(): half(2) = 2 { refl }");
}

// ---------------------------------------------------------------------------
// 2. `Even`/`Odd` reduce, which is why they are recursions into `Type` and not
//    `∃k, add(k, k) = n`. Both directions: the true one is `trivial` and the
//    false one is `False`, so its refutation is the hypothesis.

#[test]
fn parity_reduces_at_closed_arguments() {
    ok("theorem a(): Even(0) { trivial }
theorem b(): Even(4) { trivial }
theorem c(): Odd(1) { trivial }
theorem d(): Odd(7) { trivial }
theorem e(): ¬ Even(7) { λ (h: Even(7)) => h }
theorem f(): ¬ Odd(4) { λ (h: Odd(4)) => h }");
}

#[test]
fn parity_reduces_to_the_right_side() {
    bad("theorem t(): Even(7) { trivial }");
    bad("theorem t(): Odd(4) { trivial }");
    bad("theorem t(): Even(0) -> False { λ (h: Even(0)) => h }");
}

// ---------------------------------------------------------------------------
// 3. The kit at OPEN arguments, where nothing reduces. Each positive is
//    followed by the same statement attempted by `refl`/`trivial`, which is
//    what makes the positive non-vacuous.

#[test]
fn the_kit_holds_at_open_arguments() {
    ok("theorem bound(n: Nat): half(n) <= n { half_le(n) }
theorem inverts(n: Nat): half(add(n, n)) = n { half_double(n) }
theorem doubles(n: Nat): Even(add(n, n)) { even_double(n) }
theorem total(n: Nat): Or<Even(n), Odd(n)> { even_or_odd(n) }
theorem exclusive(n: Nat): ¬ And<Even(n), Odd(n)> { not_even_and_odd(n) }
theorem back(n: Nat, h: Even(n)): add(half(n), half(n)) = n { half_add_half(n)(h) }");
}

#[test]
fn the_kit_is_not_definitional_at_open_arguments() {
    bad("theorem t(n: Nat): half(n) <= n { trivial }");
    bad("theorem t(n: Nat): half(add(n, n)) = n { refl }");
    bad("theorem t(n: Nat): Even(add(n, n)) { trivial }");
    bad("theorem t(n: Nat, h: Even(n)): add(half(n), half(n)) = n { refl }");
}

/// One step of the recursion at an open argument: `Even(Succ(Succ(n)))` and
/// `Even(n)` are the SAME type, which is the definitional inversion the
/// two-step shape is chosen for and what makes every step arm above a bare
/// self-call. Its neighbour one `Succ` along is *not* definitional, and the
/// control is what records that this is the real boundary.
#[test]
fn two_steps_are_definitional_and_one_is_not() {
    ok("theorem up(n: Nat, h: Even(n)): Even(Succ(Succ(n))) { h }
theorem down(n: Nat, h: Even(Succ(Succ(n)))): Even(n) { h }
theorem odd_up(n: Nat, h: Odd(n)): Odd(Succ(Succ(n))) { h }");
    bad("theorem t(n: Nat, h: Even(n)): Odd(Succ(n)) { h }");
}

// ---------------------------------------------------------------------------
// 4. The decision, and the hypotheses.

/// `even_dec` is a `fn` and not a `theorem`, so it unfolds in conversion and
/// the decision at a closed argument *computes* — the property `le_dec` has
/// and the reason neither is a `theorem`. The instance is value-generic, so a
/// use site at an open `n` writes no arguments at all.
#[test]
fn parity_decides_and_resolves() {
    ok("theorem open(n: Nat): Or<Even(n), ¬ Even(n)> { decide<Even(n)>() }
theorem named(n: Nat): Or<Even(n), ¬ Even(n)> { even_dec(n) }
theorem closed(): Or<Even(4), ¬ Even(4)> { Inl(trivial) }
theorem resolved(n: Nat, no: ¬ Odd(n)): Even(n) { or_resolve(even_or_odd(n), no) }");
}

/// `half_add_half` needs its hypothesis, and the odd argument is why: `half`
/// throws the remainder away, so the unconditional reading is false. The open
/// attempt has nothing to supply, and the closed counterexample beside it is
/// what makes the first more than a typing accident.
#[test]
fn halving_inverts_only_on_an_even_argument() {
    bad("theorem t(n: Nat): add(half(n), half(n)) = n { half_add_half(n)(trivial) }");
    bad("theorem t(): add(half(3), half(3)) = 3 { refl }");
    ok("theorem why(): add(half(3), half(3)) = 2 { refl }");
}
