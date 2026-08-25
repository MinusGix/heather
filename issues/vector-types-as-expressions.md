---
title: Make vector types writable as expressions
status: open
labels: [surface,parser,types]
created: 2026-08-25
updated: 2026-08-25
---

Heather's "types are expressions" surface accepts `Nat`, function types,
equality, `Fin(n)`, and named type applications in the body of a type-valued
function, but not the built-in vector former:

```heather
fn BitVec(n: Nat) -> Type { [Bool; n] }
```

The parser commits prefix `[` in expression position to a vector literal and
then reports `expected ] (vector literal), found Semi` at the semicolon. The
expected `Type` result cannot select the `[T; n]` vector-type production,
despite `Type::Vec` having a code and therefore being representable as a
type-valued expression after parsing. This is an oversight in the surface
grammar boundary, not a missing kernel or elaborator capability.

The immediate customer was [[fixed-width-bitvectors]], which had to use a
one-field value-indexed record over `[Bool; n]` to give the selected vector
representation a public name. That wrapper is sound and useful, but it must
not make the general spelling gap disappear from the tracker.

## Acceptance

- A type-valued function may return a vector type at an open length:
  `fn V<A>(n: Nat) -> Type { [A; n] }`.
- The resulting name works in both directions at a neutral length: a value of
  `V<Bool>(n)` is accepted where `[Bool; n]` is expected and conversely.
- Closed and empty lengths compute without special cases.
- Existing vector literals keep their expression-position reading, including
  `[]`, `[x]`, and `[x, y]`; the change does not use backtracking that can
  silently reinterpret a malformed literal as a type.
- Vector types remain writable in every existing dedicated type position.
- Diagnostics distinguish a malformed vector type from a malformed vector
  literal and point at the relevant delimiter.

## Design boundary

This issue owns the expression/type parsing seam for the built-in vector
former. It should follow the single-reading discipline of
`docs/types-as-expressions.md`: expected-universe checking may select a type
expression, but parsing must still produce an unambiguous AST without relying
on elaboration retries. It does not own bitvector representation or arithmetic.

## Log

- 2026-08-25: Filed from [[fixed-width-bitvectors]] dogfooding. The vector
  former is already codeable and usable in type position; only its
  expression-position spelling is missing.
