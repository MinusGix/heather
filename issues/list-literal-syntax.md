---
title: Add proper list literal syntax
status: closed
labels: [frontend,syntax,stdlib,ergonomics]
created: 2026-08-27
updated: 2026-08-30
---

Heather's `List<A>` values are currently written as nested constructors:
`Cons(a, Cons(b, Cons(c, Nil)))`. This is tolerable in recursive definitions
but actively obscures data in byte encodings, certificate rows, examples, and
theorems. The existing `[a, b, c]` surface is a fixed-length vector literal,
so list syntax needs an explicit design rather than silently changing that
reading based on a late expected type.

## Acceptance

- Choose an unambiguous expression syntax for empty and nonempty lists and
  document how it coexists with `[T; n]` vectors and vector literals.
- Lower list literals to ordinary `Nil`/`Cons`; the kernel and `std/list`
  acquire no literal primitive.
- Support an open element type in checking position, an inferred homogeneous
  element type where inference has enough information, and useful diagnostics
  for an empty literal with no determining context.
- Decide whether a final-tail/spread form belongs in the first round. If it
  does, specify evaluation order and ensure the tail is checked as `List<A>`.
- Preserve source spans well enough that an element error points at the
  offending element rather than the desugared constructor spine.
- Add positive computation/checking tests and negative controls for vector/list
  ambiguity, heterogeneous elements, and an undetermined empty literal.
- Replace representative readability-sensitive `Cons` spines, including the
  x86 byte fixtures, after the syntax lands; do not mechanically rewrite
  recursive library implementations where constructors remain clearer.

## Implemented design

List construction is `List[a, b, c]`; the empty list is `List[]`. `List` and
the opening bracket are adjacent, making the form contextual and preserving a
spaced `List [i]` as ordinary indexing. The three bracket forms stay distinct:

- `List[a, b]` constructs `Cons(a, Cons(b, Nil))` at `List<A>`.
- `[a, b]` is the existing fixed-length vector literal.
- `[A; n]` is the existing vector type.

The literal remains a surface form until elaboration. In checking position the
expected `List<A>` supplies the element type, including for `List[]`. In
inference position a nonempty literal uses its first element exactly as
ordinary `Cons` inference does; `List[]` asks for an annotation or argument
position. Each element retains its written expression and span while the tail
is lowered recursively, so a bad element is diagnosed locally.

There is no spread/final-tail form in this round. Open-tail construction is
precisely the case where `Cons(head, tail)` communicates the recursive intent
better than finite literal syntax.

The `manual-list-construction` lint is semantic rather than a name-only source
check: it fires once on the outermost finite `Cons(…, …Nil)` spine only after
resolution proves that the constructor belongs to the standard `List<A>`.
`Cons(head, tail)` in recursive code, bare `Nil`, and constructor patterns stay
quiet.

## What it assumes from elsewhere

- **[[std-list-api]]** owns the `List<A>`, `Nil`, and `Cons` API. Assumed here:
  only that literals elaborate to those existing definitions.
- **[[vector-types-as-expressions]]** owns vector literal/type behavior.
  Assumed here: only that list syntax must not make its current readings
  expected-type-dependent or ambiguous.
- **[[x86-64-machine-model]]** is a motivating consumer, not a dependency.

## Log

- 2026-08-27: Filed after the first `DecodedAt` byte proofs made three-byte
  values require repeated `Cons(..., Cons(..., Cons(..., Nil)))` terms in both
  the model and consumer tests.
- 2026-08-30: Implemented `List[…]`, checking and nonempty inference,
  element-local diagnostics, the concrete-spine lint, editor grammar support,
  and the motivating FunctionIR x86 construction.
