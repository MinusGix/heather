---
title: Infer an anonymous predicate index from a subtype representation argument
status: open
labels: [elaboration,inference,subtypes]
area: language
created: 2026-09-05
updated: 2026-09-05
---

The packaged subtype showcase checks with the named predicate
`Positive(n: Nat) → Type { 0 < n }` as its `SubtypeRepr` index.
Replacing the result index of `positive_repr` by `λ n => 0 < n` makes
`lift_binary(positive_repr(), add, positive_add_closed, x, y)` fail to infer
its implicit argument `P`. The representation module itself still checks.

Reproducer: `docs/showcase/lift_positive.hthr`, replacing
`SubtypeRepr<Nat, PositiveNat>(Positive)` by
`SubtypeRepr<Nat, PositiveNat>(λ n => 0 < n)`.

Infer the already supplied predicate from the representation argument rather
than guessing a predicate from the carrier or arithmetic goal. Preserve scope
under lambda binders and relevant evidence, and retain refusal of inconsistent
indices. The named predicate is the current checked workaround.

Related: [[relational-index-inference-from-goals]],
[[subtype-transfer-and-evidence]].
