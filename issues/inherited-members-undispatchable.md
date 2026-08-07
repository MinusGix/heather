---
title: An inherited class member can never be reached by a receiver
status: open
labels: [frontend,elaboration,traits,design]
created: 2026-08-07
updated: 2026-08-07
---

Found by the traits **library adoption** round (2026-08-07), in the first
`extends` hierarchy written as library code rather than as a test.

`extends` flattens: `AddCommMonoid<G>`'s field list contains `plus`, and so do
`AddMonoid<G>`'s and `AddSemigroup<G>`'s. A child instance *synthesizes and
registers* its parents ([[traits]] §4, the canonical-value discipline). Those
two facts together mean that at any carrier with any instance in the chain,
**every class in the chain has an instance and every one of them answers for
the inherited member** — so receiver dispatch reports ambiguity, correctly and
permanently:

```
error: `plus` at this receiver is a member of `AddCommMonoid<Nat>` and
`AddMonoid<Nat>` and `AddSemigroup<Nat>`, and each has an instance here —
write the projection you meant (`⟨instance⟩.plus(…)`) rather than letting the
receiver choose
```

Nothing is wrong with the rules as written (`docs/traits-receiver-dispatch-design.md`
§4: ambiguity is the finding, never the tiebreak). What the corpus shows is
that the two features, each right on its own, *compose to exclude the whole
Mathlib-shaped use case*: `x + y` — or `x.plus(y)`, its unsugared form — is
exactly a call to an inherited member, and it can never be written with a
receiver. Only the fields declared in a leaf class dispatch.

The library's current answer, in `lib/std/algebra.hthr`, is to declare
`Monoid<A>` FLAT (no `Semigroup` parent) so that `x.op(y)` works, and to spell
the hierarchy's inherited operation explicitly
(`Nat::AddCommMonoid.plus(a, b)`). That is a real cost: a library either has a
hierarchy or has receiver sugar for its operations, not both.

Pinned by `crates/elab/tests/lib_algebra.rs::an_inherited_member_cannot_be_reached_by_a_receiver`,
which fails the day this is decided differently — deliberately, so the decision
announces itself.

## The options, none taken here

1. **Most-derived wins.** Among classes that answer and are related by
   `extends`, prefer the most derived; report ambiguity only for *unrelated*
   classes. Sound-looking because flattening plus the canonical-value invariant
   means the fields are literally the same components, so the choice is
   observationally irrelevant — which is exactly the argument that makes it a
   tiebreak rather than a guess. Wants checking against the override case,
   where a child's field is a *different* value carrying an agreement
   certificate.
2. **Least-derived wins** (the field's declaring class). Same argument, other
   direction; reads better as "the member belongs to the class that declared
   it".
3. **Do nothing**; the library keeps declaring leaf classes flat. Cheap, and it
   is what shipped — but it means `extends` and dispatch are alternatives, and
   the operators round ([[traits]] §12: `+`/`==` migrate onto classes) will hit
   this immediately, since `Add<A>` is exactly the class an arithmetic
   hierarchy wants to inherit from.

## What it assumes from elsewhere

- **[[traits]]** owns the class semantics and the dispatch rules. Assumed here:
  only that parent instances are synthesized and registered when a child is
  declared, and that dispatch treats two answering classes as ambiguous.
