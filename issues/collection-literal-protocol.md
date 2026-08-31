---

Collection literals currently have two built-in expected-type readings:
primitive vectors and the canonical standard-library `List`. Adding arrays,
sets, maps, or user containers by more name/shape checks would make nominal
types accidentally acquire syntax.

Design an explicit opt-in mechanism analogous in spirit to overloaded
numerals. The design must say how the expected container reveals its element
type, how empty literals work, whether construction is expressed as
`empty`/`push` or a bulk operation, and how ordering and duplicate semantics
remain visible for sets and maps.

## Acceptance

- Opt-in is nominal and resolved from the expected type.
- Element checking remains bidirectional; an implementation does not get to
  reinterpret already elaborated elements at unrelated types.
- Empty literals and universe levels are specified.
- Ambiguous inference remains rejected unless a separate, explicit defaulting
  policy is approved.
- Built-in List/vector behavior can be described by the abstraction without
  forcing the kernel vector representation through user code.

## What it assumes from elsewhere

- **[[list-literal-syntax]]** owns the current surface and its checking-only
  behavior. Assumed here: only the syntax `[…]` and expected-type dispatch.
- **[[canonical-list-literal-identity]]** owns the interim built-in List key.
  Assumed here: only that unrelated nominal lists do not opt in structurally.

## Log

- 2026-08-30: Filed after generic List/vector construction landed; deferred
  until a third concrete container supplies semantics rather than speculation.
title: Design an opt-in collection literal protocol
status: open
labels: [frontend,syntax,traits,ergonomics]
created: 2026-08-30
updated: 2026-08-30
---

