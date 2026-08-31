---
title: Remove the standard List literal lowering fast path
status: closed
labels: [frontend,elaboration,traits,performance]
created: 2026-08-31
updated: 2026-08-31
---

`std/list` opts into bracket construction through the ordinary
`CollectionLiteral<List<A>>(n)` instance, but elaborating every finite List
through that dictionary leaves one dependent projection/unfolding cost per
cell. Conversion-sensitive x86 proofs cross their fuel or stack boundary at
that shape, so the elaborator currently recognizes the exact standard List
instance and emits the definitionally equal `Cons`/`Nil` spine directly.

Keep the optimization honest by removing it once ordinary dictionary
projection and reduction can preserve the compact normal form. The desired
endpoint is that standard List follows exactly the same protocol path as every
other opted-in container without regressing proof fuel or minting a derived
dictionary per finite literal.

## Acceptance

- Delete `lower_standard_list_literal` and its syntax-specific registry-key
  knowledge.
- Standard List literals still reduce definitionally to the expected
  `Cons`/`Nil` spine.
- A finite literal does not add a derived dictionary binding per use.
- The FunctionIR x86 and x86_64 suites pass at their existing fuel and stack
  bounds.
- The improvement applies to ordinary class dictionaries rather than adding a
  different List-only shortcut.

## What it assumes from elsewhere

- **[[collection-literal-protocol]]** owns the ordinary List instance and its
  expected-type-directed semantics.
- **[[indexed-goal-derived-sharing]]** owns sharing of resolved indexed goals.
  Assumed here: any sharing change preserves deterministic dictionary identity.

## Log

- 2026-08-31: Filed from the protocol integration result: the ordinary path is
  semantically correct, but its projection shape exceeded established x86
  proof budgets.
- 2026-08-31: Replaced the List-only lowering with a generic compact protocol
  route. The elaborator normalizes `element` and `fromLiteral`, validates the
  projected function type, then annotates the primitive vector and conversion
  with the canonical `[element; n] -> C` contract before normalizing the
  completed application. This removes dependent dictionary projections from
  repeated term annotations without inspecting the container identity.
  Value-indexed classes now retain the declared parameterized instance
  application instead of minting one synonymous global per closed index.
  Standard List and a user `Bag` still reduce definitionally; the warm
  FunctionIR x86 boundary checks in 4.90 s (the pre-change semantic-image cache
  reproduced the old 60 s term until rebuilt), and the x86_64 boundary passes
  unchanged at its existing fuel and stack limits. Full suite: 2243 passed, 0
  failed, 1 ignored.
