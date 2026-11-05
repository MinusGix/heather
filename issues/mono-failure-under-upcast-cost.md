---
title: A failing mono search at an ordered field costs gigabytes through upcast dictionaries
status: open
labels: [tactics,performance,traits]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

Since the ordered-algebra layers ([[ordered-algebra-api]],
docs/ordered-algebra-design.md), the product laws `mono` applies inside
`section<A: OrderedField(…)>` are `OrderedSemiring`'s (`mul_le_mono_r`, …).
`apply` fills their dictionary by upcasting the section's own, which builds
the record literal `OrderedSemiring(#constraint0.rel_refl, …)`, and every
subgoal the law leaves (`0 <= c`) then mentions that literal.

A successful search costs about what it did before. A failing one explores
every alternative and its notes under that literal. For
`a * c <= b * c` with nothing known about `c`, peak memory is about 2.8 GB at
`OrderedField`, against 0.76 GB for the same goal at `OrderedSemiring`, where
no upcast is needed. That pushed `lib/_tests/std/tactic/mono_tests.hthr` past
the rail, so its two refusal probes now sit in an `OrderedSemiring` section.

Wanted: a subgoal's projections of an upcast record are read as the
original dictionary's fields (`OrderedSemiring(…).unit` is `#constraint0.unit`
by one iota step), either where `Match` builds the premise types or where
`mono` reads a leaf. Then the refusal probes can return to the `OrderedField`
section, and a client's failing `mono` costs what it did.

## Log

- 2026-11-02: Filed from the ordered-algebra round. Probe: a scratch module
  with `section<A: OrderedField(≈, <, <=, +, *)> { theorem t(a, b, c: A, h: a <= b): a * c <= b * c { by mono() } }`
  needs more than 8 GiB of address space; at `OrderedSemiring` it fits in 1 GiB.
- 2026-11-05: gardener: cites a file it shares with [[warm-replay-relocate-cost]] (`lib/_tests/std/tactic/mono_tests.hthr`).
