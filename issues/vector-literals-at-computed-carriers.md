---
title: Recognize primitive vector literals at computed vector carriers
status: closed
labels: [frontend,elaboration,vectors,ergonomics]
created: 2026-09-28
updated: 2026-09-28
---

A computed vector type converts with the primitive `[T; n]` spelling, but a
collection literal checked directly against the computed type is routed to
`CollectionLiteral` class resolution instead of the primitive vector reader.

```heather
fn V<A>(n: Nat) -> Type { [A; n] }
fn empty<A>() -> V<A>(0) { [] }
fn two() -> V<Nat>(2) { [1, 2] }
```

The first function with a literal fails with no instance for
`CollectionLiteral<[A; 0]>(0)` under the ordinary prelude. An explicit
primitive annotation works:

```heather
fn empty<A>() -> V<A>(0) { let xs: [A; 0] = []; xs }
```

## Cause and boundary

`Elaborator::elab_check_hinted` dispatches `CollectionLit` to the intrinsic
reader only when `inductive::decoded(expected)` is `Type::Vec`.
`decoded` intentionally handles canonical code formers without unfolding a
function call, so `El(V<A>(0))` takes the class-protocol path. The intrinsic
reader in `ExprElab::check_vec_lit` has the same structural limitation.
Full type WHNF is not an adequate replacement: it unfolds a closed-length
vector into its Unit/Sigma representation before the reader can recognize it.

This issue owns shape discovery for literals at computed vector carriers.
It does not own the expression parser, which [[vector-types-as-expressions]]
repairs. Review the other intrinsic vector readers when selecting a shared
shape-discovery operation; do not make all type normalization preserve vectors
just for this client.

## Acceptance

- Direct empty and nonempty literals check at named vector aliases with an
  open element type and a closed length.
- Nested vector aliases and computed type-valued functions preserve the
  primitive vector reading without fully reducing the carrier.
- Incorrect literal lengths retain the intrinsic length diagnostic.
- A neutral expected length still refuses literal construction.
- Non-vector carriers retain their `CollectionLiteral` instance semantics;
  missing instances and failed type computation remain useful diagnostics.
- Kernel-checked tests include positive conversions and negative controls.

## What it assumes from elsewhere

- **[[vector-types-as-expressions]]** owns `[T; n]` in expression position.
  Assumed here: only that `fn V<A>(n: Nat) -> Type { [A; n] }` parses.
- **[[collection-literal-protocol]]** owns class-directed literals.
  Assumed here: only that primitive vectors retain an intrinsic bootstrap
  reading while other carriers use the protocol.

## Log

- 2026-09-28: Reproduced the refusal by replacing the parser round's annotated intermediate
  bindings with direct literals: 6 vector tests passed and the direct-carrier
  regression failed with the missing `CollectionLiteral` instance.

  Literal dispatch now asks `ExprElab::vector_literal_type` for the intrinsic
  carrier. It keeps the existing structural decode fast path; for a remaining
  `El`, it weak-head normalizes the code term with the ordinary semantic oracle
  and decodes only its resulting former. `TmVec` is already term WHNF, so this
  exposes the vector without reducing its closed length to Unit/Sigma. The
  resolved vector view is passed to the existing intrinsic literal builder;
  non-vector results leave the original expected carrier to class resolution.
  Fuel exhaustion is a local error at the literal, not a protocol miss.

  Reviewed the other intrinsic vector readers in `vec/surface.rs`: they retain
  their structural decode and are outside this literal-checking change. The
  kernel, global type normalization and instance-inference routes are unchanged.

  Kernel-checked surface coverage includes open element types, empty/nonempty
  and nested aliases, a type family selected by a match, a local type-valued
  function, a projected type-valued field, and equality of the produced values.
  Negative controls retain exact length diagnostics, refuse neutral lengths and
  wrong elements, and keep missing non-vector instances as protocol errors.
  A custom computed non-vector carrier and a neutral carrier with an explicit
  local dictionary retain class-based construction. Focused vector/list tests:
  19 passed; the independent zero-fuel diagnostic test passed. Updated the guide,
  design note and shared editor fixture. All 13 Tree-sitter corpus cases and all
  shared positive fixtures passed. Final full `scripts/test`: 3,083 passed,
  0 failed, 5 ignored.
