---
title: Inline lambda predicate unification for I -> Type value parameters
status: closed
labels: [elaborator,unification,proofs]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-24
updated: 2026-11-24
closed: 2026-11-24
---

When unifying a Miller pattern `?P(n)` (e.g. from `Eventually::map` or
`Eventually::both`) against an inline predicate application where `n` occurs
nested — such as `Not(Q(n))` (`λ n => ¬Q(n)`), `DoubleNeg(P(n))`, or
`CloseAt(xs(n) - l, e)` — `unify_tm` saw `matching_value_spine == true`
(same spine arity 1) and skipped Miller abstraction for first-order spine
alignment, attempting `?P := Not` and failing to equate bound `n` with `Q(n)`.

## Resolution

- **`crates/elab/src/unification.rs`:** added `eta_spine_args(subj, &args)` to
  the Miller-pattern guard in `unify_tm`. First-order η-contracted alignment
  (`?C(x̄) ≟ H(ā, x̄)` → `?C := H(ā)`) is now used only when the trailing
  arguments of `subj` are literally `LocalVar(args[i])`; otherwise Miller
  abstraction `?C := λ ȳ => subj[x̄ := ȳ]` runs directly.
- **Tests:** removed the `NotAt` workaround in `lib/_tests/std/core/world_tests.hthr`
  and verified inline `λ n => ¬Q(n)`, `λ n => ¬P(n)`, `λ n => ¬¬P(n)`, and
  `λ n => CloseAt(xs(n) - l, e)`.



