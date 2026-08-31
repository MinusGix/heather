---
title: Design an opt-in collection literal protocol
status: closed
labels: [frontend,syntax,traits,ergonomics]
created: 2026-08-30
updated: 2026-08-31
---

Collection literals began with two built-in expected-type readings: primitive
vectors and the canonical standard-library `List`. Adding arrays, sets, maps,
or user containers by more name/shape checks would make nominal types
accidentally acquire syntax.

The syntax now targets one canonical class from the implicit prelude:

```heather
class CollectionLiteral<C>(n: Nat) {
    element: Type,
    fromLiteral: [element; n] → C,
}
```

The expected container `C` and syntax-known literal length `n` fully determine
the resolution goal. Projecting `element` gives every entry its bidirectional
checking type; `fromLiteral` receives one primitive vector whose entries have
already checked. Consequently an instance controls ordering and duplicate
semantics explicitly, without receiving untyped syntax or reinterpreting
elements. Empty literals work because `element` comes from the dictionary,
not the first entry.

`std/list` provides the ordinary right-folding instance into `Nil`/`Cons`.
Primitive vectors remain the intrinsic bootstrap reading, analogous to
`Nat`'s intrinsic numeral reading, and retain their precise expected-length
diagnostics. An unrelated nominal container can opt in with its own instance;
same-shaped containers without one are rejected.

The implementation also admits value-generic class indices. A binder used
only in an index is recoverable by candidate-head unification; its registry
component is based on binder position (`#binderN`), so alpha-renaming cannot
create a second instance slot.

The form remains checking-only. With no expected `C`, neither a nonempty nor
empty literal defaults to a container. The present class is level-0 because
surface universe polymorphism remains unavailable.

Spread is intentionally not a `CollectionLiteral` field. It belongs to the
separate optional protocol owned by [[collection-literal-spread]], so a type
may support finite literals without supporting concatenation or open tails.

## Acceptance

- Opt-in is nominal and resolved from the expected type. **Done.**
- Element checking remains bidirectional. **Done.**
- Empty literals and universe levels are specified. **Done.**
- Ambiguous inference remains rejected. **Done.**
- List uses the abstraction while vectors remain the intrinsic bootstrap
  representation. **Done.**

## What it assumes from elsewhere

- **[[list-literal-syntax]]** owns the checking-only `[…]` surface.
- **[[collection-literal-spread]]** owns the separate optional spread layer.

## Log

- 2026-08-30: Filed after generic List/vector construction landed; deferred
  until a third concrete container supplied semantics rather than speculation.
- 2026-08-31: Landed `CollectionLiteral<C>(n)`, the standard List instance,
  intrinsic vector bootstrap, user-container coverage, canonical identity, and the
  value-generic-index support needed by length-indexed instances.
- 2026-08-31: Full-suite integration found that inserting a prelude class at
  sequential nominal tag 0 renumbered every existing inductive and pushed the
  conversion-sensitive x86 proofs over their fuel/stack cliffs. The canonical
  syntax protocol now uses reserved compact binary tag 65536 without advancing
  sequential allocation; tests pin that the first user declaration remains
  tag 0. The standard List fast path still requires its registered ordinary
  instance, but emits the equivalent `Cons`/`Nil` normal form directly so
  finite literals do not mint derived dictionaries or spend proof fuel on one
  projection per cell. Full-suite verification: 2241 passed, 0 failed, 1
  ignored.
