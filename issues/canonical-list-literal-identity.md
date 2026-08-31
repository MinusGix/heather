---

`[…]` currently decides that an expected inductive is a list by checking the
basename `List`, one type parameter, and `Nil`/`Cons` constructor arities.
That is stronger than a raw constructor-name heuristic, but still grants
special syntax to an unrelated nominal declaration that happens to copy the
shape.

Key the built-in list interpretation on the qualified declaration identity
`list::List`. Constructor-shape validation remains a corruption/version-skew
guard, not the identity test. A structurally identical `other::List` must be
rejected as an unsupported collection until [[collection-literal-protocol]]
provides an explicit opt-in.

## Acceptance

- Standard `list::List` accepts empty and nonempty collection literals through
  unqualified and qualified expected-type spellings.
- A same-named, same-shaped declaration in any other module is not treated as
  the standard list.
- Import ambiguity does not affect a literal whose expected type canonically
  identifies `list::List`.
- `manual-list-construction` follows the same identity rule.
- Existing vector literal behavior is unchanged.

## What it assumes from elsewhere

- **[[list-literal-syntax]]** owns the `[…]` surface and checking-only rule.
  Assumed here: only that `List<A>` is one supported interpretation.
- **[[collection-literal-protocol]]** owns future user-defined opt-in. Assumed
  here: only that structural imitation is not that protocol.

## Log

- 2026-08-30: Filed from the post-implementation audit of generic collection
  literals; implementation started immediately.
- 2026-08-30: Landed. Both bracket construction and
  `manual-list-construction` compare the expected/resolved inductive's nominal
  tag with the declaration registered under `list::List`. The old basename
  test is gone; constructor shape remains a separate sanity guard. Tests cover
  an identical impostor, qualified canonical use under import ambiguity, and
  the impostor lint refusal.
title: Key list literals on the canonical List declaration
status: closed
labels: [frontend,syntax,correctness]
created: 2026-08-30
updated: 2026-08-30
---
