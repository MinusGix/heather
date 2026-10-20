---
title: Keep computation and theorem requirements minimal in relational interfaces
status: open
labels: [setoids,design,backlog]
area: tactics
created: 2026-09-05
updated: 2026-09-05
---

The recent clients expose two costs of oversized constraints: selected-element functions must pin an unused union, and computational functions carrying a whole FiniteSets dictionary can make concrete compatibility proofs exhaust conversion fuel.

## Acceptance

- Separate operation inputs from law requirements where computation does not inspect evidence; retain explicit evidence when it is computationally relevant.
- Factor membership transport and image capabilities so clients need not select unrelated algebraic operations.
- Demonstrate concise calls with two valid algebraic structures on the same carrier. Do not guess an unused index from a global instance.
- Compare explicit dictionaries, smaller classes, and existing index/notation mechanisms before adding syntax. Preserve complete local dictionary coherence and existing clients.
- Measure ergonomics separately from the compiler performance workaround; users should not need a special layout merely to make checking practical.

Customers: `move_selected`, `image_selected`, and `augment`. Related: [[relation-indexed-algebra]], [[constraint-index-binder-introduction]], [[setoid-dictionary-projection-growth]], [[finite-set-client-design]].

## Scheduling

Captured for a future concrete driver; not scheduled by this filing. See [[setoid-roadmap-and-resumption]].
