---
title: Split a goal on the tests a definition branches on, when the goal is not an equation
status: closed
labels: [tactics,proofs,ergonomics]
area: tactics
milestone: [tac-general]
created: 2026-11-11
updated: 2026-11-11
---

A function defined by a `match` on Boolean tests of its arguments, such as

    fn Regex::alt(a, b: Regex) → Regex {
        match a.is_no_match() { True => b, False => match b.is_no_match() { True => a, False => Alt(a, b) } }
    }

has a theorem per branch, and the natural proof is "by cases on the tests,
with each test's equation in hand". Today neither route reaches it
(`lib/std/text/regex/regex_dfa.hthr`, 2026-11-11):

- `match h: a.is_no_match() { … }` in the proof does not refine a goal that
  mentions the test only under the folded `Regex::alt(a, b)`: the arms keep
  the unreduced goal. As an arm of an outer `match` on an expression the
  kernel refused the motive (`NotConvertible`, sides that display the same).
- `split_all` splits the `match` an *equation's* side is stuck on; a goal
  that is a relation (`alt(a, b) ≈ Alt(a, b)`), an `↔` or a `Π` over one is
  handed to the leaf unsplit.

The workaround in the library is a second definition that takes the tests
as parameters (`alt_at(za, zb, a, b)`), a theorem over the tests as
variables with their equations as hypotheses, and an instantiation at
`refl`. It doubles each such definition and its statement.

Wanted, either or both:

- `match h: e` unfolds non-recursive definitions in the goal far enough to
  find `e` as a scrutinee (the reduction `split_all` already does after a
  split, [[split-all-reduce-defined-heads]]), and its motive is well-typed
  when nested in an arm;
- `split_all` (or a `split` beside it) finds the blocking `match` under any
  goal head, not only `=`, and keeps the test's equation as a hypothesis of
  each case for the leaf.

Done when `Regex::alt_same` and `Regex::seq_same` are proved against
`Regex::alt`/`Regex::seq` written directly, and `alt_at`/`seq_at` are gone.

Related: [[simp-tactic]] (unfold then split is its usual companion),
[[proof-scripts-as-tac-blocks]].

## Log

- 2026-11-11: Built as a rung of the motive synthesis, the first of the two routes: `match h: test` now reads the reduced goal below `Π` codomains and `Σ` components, strengthens the stuck positions it finds to the outer context and abstracts those that convert to the scrutinee (`abstract_below`, `expose_below` in `crates/elab/src/matching.rs`; `docs/elaborator/goal-motive-synthesis-design.md` §4.5). Tried only when every earlier rung found nothing. It also works as an arm of an outer `match`, which is where the kernel had refused the motive. `Regex::alt` and `Regex::seq` are written directly, `alt_at`, `seq_at` and `deriv_simp_seq` are gone: done-when met. Probes and the three limits (a test that mentions a goal binder, a call under a variable head, a goal that also writes the test) in `lib/_tests/std/core/match_motive_below_tests.hthr`. Not built: `split_all` under a non-equation head; with the `match` reaching these goals no customer is left for it here.
