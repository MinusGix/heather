---
title: Two constraints over the same operations, without a combined class
status: open
labels: [traits,frontend,design]
area: language
created: 2026-10-30
updated: 2026-10-30
---

A declaration cannot say `A: OrderedField(≈, <, <=, +, *)` and
`A: CommRingOfInt(≈, +, *)` together: each constraint installs `≈`, `+` and
`*` again, and the second is refused (docs/linarith-design.md). The library
has answered with combined classes that add nothing but the pairing:
`OrderedFieldOfInt` (`linarith`'s certificates), and the
`OrderedFieldOfRat` that the [[interval-containment-once-over-ordered-field]]
assessment prototyped and then dropped. Minus (2026-10-30): the combined
classes are the wrong pattern; two constraints over the same operations
should work properly.

What "properly" has to mean:

- A later constraint's slots can *link* to indices an earlier one declared
  (the bare-name linked reference [[constraint-index-binder-introduction]]
  preserves), so both dictionaries are over one `≈`, one `+`, one `*`, and
  notation is installed once.
- Two dictionaries can reach one ancestor (`OrderedField` and
  `CommRingOfInt` both reach `CommRing`). Field reads through either must
  agree, or resolution must pick one deterministically. The
  ambiguity rule in [[requires-placement-syntax]] and
  [[class-default-operators]]' collision rule are the neighbours.
- A call at a concrete carrier resolves both from instances, as one
  constraint does today.

Not every pairing needs this: an embedding is better passed as a morphism
value ([[casting-standard]] §5.6) than as a capability of the carrier. But
`OrderedFieldOfInt` is a capability pairing, and it is the case to retire
first.
