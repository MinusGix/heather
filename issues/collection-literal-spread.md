---

Finite `[…]` construction deliberately has no open-tail form, leaving
`Cons(head, tail)` as the honest spelling for recursive list code. A spread
form such as `[a, b, ..tail]` could improve concatenative construction, but
its meaning is container-dependent: a list tail is natural, a fixed vector
changes the result length, and sets/maps have different ordering and duplicate
rules.

Design the feature only alongside concrete consumers. Decide whether spread
is one final tail or may occur among elements, evaluation order, vector length
arithmetic, and how an eventual [[collection-literal-protocol]] exposes the
operation.

## Acceptance

- Grammar and evaluation order are explicit.
- List and fixed-vector typing/lowering are specified independently.
- The result length of vector spreads is available to dependent typing.
- Diagnostics distinguish an element from a spread operand.
- Recursive `Cons(head, tail)` remains supported and is not linted merely for
  avoiding spread syntax.

## What it assumes from elsewhere

- **[[list-literal-syntax]]** owns finite bracket construction.
- **[[collection-literal-protocol]]** owns user-defined collection opt-in;
  spread must not silently invent a second incompatible protocol.

## Log

- 2026-08-30: Filed from the generic collection-literal follow-up review.
title: Design collection literal spread and tail syntax
status: open
labels: [frontend,syntax,ergonomics]
created: 2026-08-30
updated: 2026-08-30
---

