---
title: match h: on a local refined the hypothesis an arm passes h to
status: closed
labels: [elaboration, match, bug]
area: language
milestone: [lang-proof-modularity]
code: crates/elab/src/generalize.rs @ 7cda267
created: 2026-11-14
updated: 2026-11-14
---

In a `fn` body (and a theorem's proof),

    fn pick<A>(b: Bool, f: (b = True) → A, g: (b = False) → A) → A {
        match h: b { True => f(h), False => g(h) }
    }

was refused: "this has type `b = False`, but `False = False` is expected
here". The split on the local `b` refined the hypotheses the arms name
(`select_refined`, issues/elab-match-refines-hypothesis-kernel-rejects.md),
so `g` became `(False = False) → A` in the `False` arm, while the convoy's
`h` is stated about `b` as written. A computed scrutinee never had this:
design §5.1 of `docs/language/matching/dependent-match-compiler-design.md` already refines
nothing by occurrence under `match h:`, for exactly this reason.

## Fix

Under `match h:` a hypothesis that **takes an equation about the
scrutinee** (a Π telescope domain `b = c` or `c = b`,
`takes_equation_about`) is not refined for being named by an arm: it is
what `h` is passed to. Everything else is as before: a hypothesis the goal
mentions is still refined with the goal (the motive abstracts the
scrutinee out of it), and one an arm names that does not take the
equation (`k: b.IsTrue() → Nat` at `True => λ p => k(p)`) still is.

The same round made a lemma over such a `match` learn its arms from a
goal ([[unify-through-match-arms]]).

Probes: `pick_by`, `pick_by_true`, `pick_by_goal` in
`lib/_tests/std/core/bool_tests.hthr`. The whole library re-elaborates
unchanged (sweep, 2026-11-14).

## Log

- 2026-11-14: fixed (thread "Fix inference and printing around match").
