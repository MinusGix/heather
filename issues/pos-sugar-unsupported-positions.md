---
title: Pos<A> sugar on member results, parameterised records and constructor fields
status: closed
labels: [frontend,elaboration,ergonomics]
created: 2026-10-13
updated: 2026-10-14
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

## Log

- 2026-10-14: LANDED for three positions (docs/positivity-evidence-design.md §13). Member results: `fn T::f(…) → Pos<A>` declares `T::f::pos`, attached to `T` the way an instance member `Le::Judge::verdict` already is (the owner rule splits at the first `::`). Parameterised records: the rule is generic in the type parameters and takes the value parameters as `{}` implicits; the 2026-10-13 probe failed only because its parameter appeared in no field (value parameters lower by substitution, so `R(3)` and `R(5)` were one type), and that case is now a parse error. Constructor fields: the record expansion with no rule, since a pattern binds the fact as a local; refused on an indexed family and unnamed. Construction in inference position now fills defaults for a declaration without parameters (records too). Lambda binders and function domains stay [[positive-refinement-type]]'s. Tests: crates/elab/tests/pos_binder_sugar.rs.
