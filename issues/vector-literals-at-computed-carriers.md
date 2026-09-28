---
title: Recognize primitive vector literals at computed vector carriers
status: open
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
