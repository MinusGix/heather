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
theorems. The existing `[a, b, c]` surface began as a fixed-length vector
literal; this issue now makes that surface generic over the expected container.

## Acceptance

- Choose an unambiguous expression syntax for empty and nonempty lists and
  document how it coexists with `[T; n]` vectors and vector literals.
- Lower list literals to ordinary `Nil`/`Cons`; the kernel and `std/list`
  acquire no literal primitive.
- Support an open element type in checking position and useful diagnostics for
  a literal with no determining container context.
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

Construction uses the same bracket literal for lists and vectors. The expected
type selects the container, much as an expected numeric type selects a numeral
interpretation:

- `[a, b]` constructs `Cons(a, Cons(b, Nil))` when checked at `List<A>`.
- `[a, b]` constructs the primitive fixed-length representation when checked
  at `[A; 2]`.
- `[A; n]` is the existing vector type.

The literal is deliberately checking-only: without an expected type even a
nonempty `[a, b]` cannot choose honestly between `List<A>` and `[A; 2]`.
Annotations, function results, and argument domains provide that expectation,
including for `[]`. Each element retains its written expression and span while
a list tail is lowered recursively, so a bad element is diagnosed locally.

Because `List` is no longer part of literal syntax, `xs[i]` and even a value
named `List` indexed as `List[i]` need no whitespace exception.

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
- **[[vector-types-as-expressions]]** owns vector type behavior. Bracket
  construction is now intentionally expected-type-dependent while `[A; n]`
  remains syntactically distinct.
- **[[x86-64-machine-model]]** is a motivating consumer, not a dependency.

## Log

- 2026-08-27: Filed after the first `DecodedAt` byte proofs made three-byte
  values require repeated `Cons(..., Cons(..., Cons(..., Nil)))` terms in both
  the model and consumer tests.
- 2026-08-30: Implemented `List[…]`, checking and nonempty inference,
  element-local diagnostics, the concrete-spine lint, editor grammar support,
  and the motivating FunctionIR x86 construction.
- 2026-08-30: Replaced the container-prefixed form with generic `[…]` after
  review. List and vector literals are now selected by their expected type;
  ambiguous inference is rejected instead of defaulting to either container.
- 2026-08-30: Checking-only is retained as a design invariant: without an
  expected type, even nonempty syntax cannot choose nominal List versus fixed
  vector honestly. Future opt-in belongs to [[collection-literal-protocol]],
  not a default inferred container.
- 2026-08-30: Follow-ups filed with separate owners:
  [[canonical-list-literal-identity]] for the immediate nominal-identity fix,
  [[collection-literal-fixits]] for automatic lint edits, and
  [[collection-literal-spread]] for open-tail/spread design.
