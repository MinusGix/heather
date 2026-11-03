---
title: partial fn: lower a tail-only body to CoTree::iter, with an iteration invariant rule
status: open
labels: [termination,coinduction,sequencing]
area: language
milestone: [lang-sequencing,nh-effects]
created: 2026-11-03
updated: 2026-11-03
---

A `partial fn` whose every self-call is in tail position could be one
`CoTree::iter` of a pass over its arguments (`Continue(args)` at a call,
`Break(v)` at a return), as docs/partial-functions-design.md §4.2 planned.
That is the shape a native loop has (`iter_refines` carries it to
`Program::iter` and the native `Repeat`), so round 3 (partial `runtime fn`
loops) wants it.

Round 2 (docs/partial-functions-design.md §9 item 7) lowers every
`partial fn` through `CoTree::rec`, tail calls included, because partial
correctness then always goes through `CoTree::rec_sound`. An `iter` lowering
needs the matching rule first:

- `CoTree::iter_sound`: an invariant `I` on states and `Q` on results; if
  `body(a)` returns `Continue(a')` only with `I(a')` and `Break(b)` only with
  `Q(b)` whenever `I(a)`, then `Returns(iter(body, a), b) → Q(b)`. An
  induction on the count, as `mrec_safe` is.
- Or an `Eutt` between `rec` of a tail-only body and `iter` of its pass, so
  that `rec_sound` transfers (needs `issues/eutt-iteration-and-io-reading.md`'s
  `Eutt::iter_cong`).

## Done when

A tail-only `partial fn` lowers to `CoTree::iter`, its result is proved by
the new rule in `lib/_tests/std/itree/partial_fn_tests.hthr`, and `search`
there runs at a literal by `refl` as today.
