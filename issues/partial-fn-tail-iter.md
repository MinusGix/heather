---
title: partial fn: lower a tail-only body to CoTree::iter, with an iteration invariant rule
status: closed
labels: [termination,coinduction,sequencing]
area: language
milestone: [lang-sequencing,nh-effects]
created: 2026-11-03
updated: 2026-11-06
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

## Log

- 2026-11-05: gardener: cites a file it shares with [[partial-fn-use-site-refusal]] (`lib/_tests/std/itree/partial_fn_tests.hthr`).
- 2026-11-06: Built (thread "Lower tail-recursive partial fns to iteration"); docs/partial-functions-design.md §10. `CoTree::iter_sound` (+ `iter_safe`, `Step::Within`, `Returns::ret`) in coitree_rec.hthr: an induction on the count, with the pass's hypothesis stated on `Returns` of the pass; the Eutt route was not needed. crates/elab/src/partial.rs lowers a body with no bound self-call to `f#body: A → CoTree<Step<A, B>>(E)` (a tail call is `CRet(Continue(e))`, a tail leaf its `Break`) and `f = CoTree::iter(E, f#body, x)`; a body with a bound call stays `rec`. Done-when: `search` lowers to `iter` (`search_is`), `search_returns_big` and `walk_sum` are `iter_sound`, `search_0` is still `refl` (partial_fn_tests.hthr). A tail-only `partial(E) fn` now issues `E`'s commands at `E`; making a body with a bound call spell them the same is [[partial-fn-event-spelling]].
