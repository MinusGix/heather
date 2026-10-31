---
title: Ctors and quoting at parameterized types and dependent fields
status: open
labels: [metaprogramming,elaboration]
area: tactics
created: 2026-10-28
updated: 2026-10-31
---

`Ctors(ty)` answers a parameterless, non-indexed inductive only, and a
constructor with a field whose type mentions an earlier field comes back
with that field untyped and no constructor function
(docs/host-elaboration-interface-design.md §19). Quoting likewise turns only
a parameterless inductive's name into a type. So `generate congruences(T)`
cannot run at `List<A>`, `Option<A>`, a record with a dependent field, or an
indexed family, and issues/heather-checked-construction-api.md's "open types"
axis is not exercised by a generator yet.

## Acceptance

- A generator can be handed a type with parameters (an application such as
  `List<A>` written at the `generate`, or the type former with its
  parameters introduced by `Assume`), and `Ctors` answers its constructors
  with fields at those parameters.
- A dependent field is answered as a binder (its type as a function of the
  earlier fields, e.g. through `Pi`), so a generator can state a dependent
  congruence (`HEq`-free: transport along the earlier fields' equations), or
  the refusal stays and names why.
- `congruences(List)` (or `congruences(List<A>)`) declares the two-field
  congruence for `Cons` at an open element type; probes at a concrete and an
  open instance.
- Then decide whether `lib/kernel_model/kernel_reduction.hthr`'s
  hand-written `Tm::cong_*` group moves to a generator (it holds non-`Tm`
  fields fixed, which wants a `congruences_over(T, field types)` variant).

## Log

- 2026-10-31: `tac-host-interface` is marked done in docs/roadmap.md (its "done when" is met), so this issue no longer serves it; it stays open in area `tactics` with no milestone.
