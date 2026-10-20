---
title: "A first-class proposition for three-way order cases"
status: open
labels: [design,stdlib,logic,orders,ergonomics]
area: mathematics
created: 2026-08-20
updated: 2026-08-20
---

Order trichotomy currently returns nested disjunctions such as
`a < b ∨ a = b ∨ b < a`. The proposition is mathematically fine but awkward
to name, pattern-match, transport, and specialize at zero. Investigate a
generic three-constructor proposition (for example `Trichotomy(lt, eq, gt)`)
with named less/equal/greater constructors and an eliminator.

Begin with a library structure, not dedicated parser syntax. It must remain a
proof-level proposition, distinct from a runtime `Ordering`; the latter is a
compiled representation of a decision procedure, as recorded by
[[strict-order-presentation]]. The abstraction should cover `0 < y`, `0 = y`,
`y < 0` without being specialized to zero.

## Acceptance

- Nat and Int trichotomy theorems can return the named proposition.
- Consumers can eliminate the three cases without remembering nested `Inl` /
  `Inr` association.
- Bridges to and from the existing nested disjunction are provided during
  migration.
- The design states how, but does not conflate, a compiled `Ordering` decision
  relates to the proposition.

## Log

- 2026-08-20: Filed from the standard-library surface review; syntax is
  deliberately deferred until the reusable proposition earns it.
