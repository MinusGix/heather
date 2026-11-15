---
title: Make vector types writable as expressions
status: closed
labels: [surface,parser,types]
created: 2026-08-25
updated: 2026-09-28
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
`docs/language/types-as-expressions.md`: expected-universe checking may select a type
expression, but parsing must still produce an unambiguous AST without relying
on elaboration retries. It does not own bitvector representation or arithmetic.

## Log

- 2026-08-25: Filed from [[fixed-width-bitvectors]] dogfooding. The vector
  former is already codeable and usable in type position; only its
  expression-position spelling is missing.
- 2026-09-28: Verified the gap at current HEAD: the new parser regression failed at
  `[A; n]` with `expected ] (collection literal), found Semi`. The expression
  parser now selects a vector type at the first semicolon, reads the already
  parsed element through `expr_as_ty`, and returns the existing `TyLit(Vec)`
  node. No kernel or elaborator change, speculative parse, or expected-type
  retry is involved. The dedicated type-position production stays intact.

  Focused tests cover neutral lengths with open element types, conversion in
  both checking directions, type equality and round trips, empty and closed
  lengths, nested/function element types, higher universes, malformed delimiters
  and semantic negative controls. Added a shared editor fixture and updated the
  language guide and types-as-expressions design note. Focused vector tests:
  7 passed. Final full `scripts/test`: 3,079 passed, 0 failed, 5 ignored.
  Tree-sitter: all 13 corpus cases and all shared positive fixtures passed.

  Dogfooding exposed a separate shape-discovery limitation: a literal directly
  checked at a computed vector carrier is sent to the class protocol. Explicit
  primitive annotations work. Filed [[vector-literals-at-computed-carriers]]
  for that elaborator follow-up; this issue owns only the parser seam.
