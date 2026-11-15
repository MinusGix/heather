---
title: A merged constraint class made in two unrelated modules is two classes
status: open
labels: [traits,frontend]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Constraints that share a symbol at one carrier merge into one dictionary of
a synthesized class (docs/language/classes/operators-onto-classes-design.md §17,
[[constraints-sharing-indices]]). The class is made in the module that first
asks for it and found by name after that, which covers the library today:
`linarith` makes `CommRingOfInt+OrderedField` and its clients import it.

Two modules that do not import each other can each make it. A third module
importing both then sees two classes of one name: the bare name is
ambiguous where its own declaration asks for the merge, and a dictionary of
one does not answer a goal of the other at an open carrier (each assembles
fine at a concrete carrier). Nothing does this yet.

Directions: key the synthesized class by its structure rather than by the
module that made it (one class per parent set and linking, wherever it is
first made, as derived instances are canonical per goal), or let resolution
treat two merged classes over the same parents and linking as one (upcast
between them field by field).

A second, smaller gap from the same round: a named constraint
(`requires m: …`) never merges, since the body reaches its dictionary by
name. Two named constraints sharing an ancestor keep the old two-copies
behaviour.
