---
title: Recursive declarations with value parameters (ITree's events)
status: open
labels: [inductives,elaboration,effects]
area: language
milestone: [it-core]
created: 2026-10-20
updated: 2026-10-20
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
