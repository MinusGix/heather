---
title: Pos<A> sugar on member results, parameterised records and constructor fields
status: open
labels: [frontend,elaboration,ergonomics]
created: 2026-10-13
updated: 2026-10-13
---

Positions the `Pos<A>` binder sugar ([[pos-binder-sugar]]) refuses today,
each with what it would need. None has a customer yet; this issue owns them
until one does.

- **A member function's result**, `fn T::f(…) → Pos<A>`: its fact would be
  `T::f::pos`, which needs a member to own members
  ([[function-owned-members]] widened owners to functions, not to members).
- **A field of a parameterised record.** A value-parameterised record's rule
  `{n}, {r: R(n)}: 0 < r.field` did not unify `n` from the goal (probed
  2026-10-13: "could not infer the implicit argument" for the record binder);
  a type-parameterised one would quantify over a monomorphized family.
- **An inductive constructor's field** (`Some(n: Pos<Nat>)`): the field
  expansion is the record one, but the rule has no single projection to
  read.
- **A lambda binder or a function type's domain** (`Pos<Nat> → Rat`): no
  binder to expand into; this is [[positive-refinement-type]]'s.

## What it assumes from elsewhere

- **[[pos-binder-sugar]]** owns the three supported positions and their
  spelling. Assumed here: the record rule is named `R::field_positive`.
