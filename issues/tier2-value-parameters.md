---
title: Recursive declarations with value parameters (ITree's events)
status: closed
labels: [inductives,elaboration,effects]
area: language
milestone: [it-core]
created: 2026-10-20
updated: 2026-10-21
---

An interaction tree is parameterised by its events as a *value*:
`inductive ITree<R>(E: Events) { Ret(r: R), Tau(t: ITree<R>(E)),
Vis(c: E.Cmd, k: E.Resp(c) -> ITree<R>(E)) }`. Neither recursive tier lowers
that today. The recursive occurrence `ITree<R>(E)` is an applied
*expression* in type position (`TyKind::OfExpr`), not the `TyKind::Named`
form `classify_field` recognises as the uniform occurrence, so a plain child
is refused as nested recursion and a function child as "a function whose
result mentions `ITree` under another type"
(`reject_function_fields`, `crates/elab/src/inductive.rs`).

The lowering side should be small: `lower_ctor_with_domain` already binds
value parameters as aliases over every field type, including a function
field's domain, so the shape, the positions and the leaf predicate of
`docs/inductive-tier2-w-lowering.md` see `E` like any other field type.
What is missing is classification: recognise `D<p̄>(v̄)` with `v̄` the
declaration's own value parameters, in order, as the uniform occurrence
(tier 1 §1's rule, extended), and refuse anything else as non-uniform.

## What it assumes from elsewhere

- **[[recursive-function-fields]]**: the tier-2 lowering, landed 2026-10-20.
  Assumed here: only that a function field's domain is lowered in the field
  context, where value parameters are already in scope.

## Done when

`ITree<R>(E)` above declares, its constructors build at an open `E`, and a
`match` with recursion through `k` checks, tested on the four axes of
`docs/testing-generated-terms.md`; a non-uniform occurrence
(`ITree<R>(F)`) is refused by name.

## Log

- 2026-10-21: LANDED, for both recursive tiers and for tier 0 (docs/surface-value-parameters.md §6, which now owns the rule; tests in crates/elab/tests/inductive_value_parameters.rs). Value parameters are accepted on every unindexed `inductive`. The lowering needed nothing: lower_ctor already binds them as aliases over every constructor's fields, including a function field's domain. The change is classification: `uniform_occurrence` in inductive.rs reads both `D<p̄>` (TyKind::Named) and `D<p̄>(v̄)` (TyKind::OfExpr) and accepts only the declaration's own type parameters then value parameters, bare and in order, for plain children, container elements and function-child codomains alike; `ITree<R>(F)`, `D(Succ(m))`, a permuted list and a bare `D` are refused by name. Value parameters beside an index stay refused by name; the field-shadows-parameter check now runs over every constructor. The ITree of this issue declares, builds at an open E and R, recurses through k, computes by refl, and proves an induction through every kind. Floating point's `Float(F)` can now be a real inductive; that migration is the float thread's, after PR #85.
