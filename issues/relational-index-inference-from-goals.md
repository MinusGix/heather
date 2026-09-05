---
title: Infer relation and operation indices from relational theorem goals
status: closed
labels: [elaboration,relations,inference,ergonomics]
created: 2026-09-05
updated: 2026-09-05
---

A compact Mergeable(≈, ⊔) theorem checks, but calling merge_twice_auto(known, incoming) at SameMembers((known ++ incoming) ++ incoming, known ++ incoming) leaves an unresolved relation/operation index and cannot resolve the dictionary. Original reproducer, now a positive regression: `relational_notation_infers_scoped_and_concrete_indices` in `lib_setoid_mergeable`. Infer only indices determined by the expected relation and operation applications or scoped evidence; never pick a default relation from the carrier. Cover concrete list use, locally constrained use, two relations/operations on one carrier, and an underdetermined call that still requests an explicit choice. Diagnostics should name the mathematical indices instead of generated #constraint/#op names.

## Bounded inference rule

Read the expected type before unfolding named relations. Match a flexible
operation or relation spine against a rigid declaration or local parameter;
a leading prefix of type arguments can specialize a generic declaration such
as `SameMembers<A>` or `append<A>`. Extra value arguments are not a license to
invent a partial application. This is structural inference, followed by the
ordinary kernel check, not a search for an arbitrary function with the same
behavior.

The expected conclusion takes precedence over scoped index proposals. Keep
native identity and unfolded/extensionally equivalent relation presentations
outside this rule unless another existing inference rule already handles them.
A relation that has disappeared into its definition cannot in general be
reconstructed uniquely.

The unifier's pattern and subject use different global worlds. Only the
pattern's indices below `n` are scratch metas; all subject globals are rigid,
including a newly declared relation at index zero. Regression coverage pins
this independently of library declaration order.


## Implementation

- The checking fallback preserves the original expected type when handing it
  to call inference. Both general inference and the existing identity LGG
  harvest inspect it before a reduction retry.
- Structural application matching admits rigid local heads and leading type
  arguments on rigid declarations. It preserves the rejection of extra value
  arguments and the existing scope-strengthening and withheld-meta rules.
- Symbolic constraint failures display `Mergeable<A>(≈, ⊔)` rather than
  generated `#op`/`#constraint` binders.
- Regression cases cover the concrete list client, scoped use, either of two
  structures on the same carrier, a recently declared relation, and a call
  whose result leaves its indices undetermined. The unifier control checks
  type specialization and rejection of partial value application.

The unchanged scope-proposal and designation rules remain owned by
[[operation-indexed-classes]] and [[surface-operators]]. More general
higher-order inference remains with [[elab-unifier-completeness]].

## Log

- 2026-09-05: Implemented expected-goal index inference, preserving named relations before reduction and matching local or type-specialized rigid heads. Added recent-declaration and refusal regressions, readable symbolic diagnostics, and the concise list-client documentation. Final furnace run -- scripts/test passed: 2,355 tests, 0 failed, 5 ignored.
