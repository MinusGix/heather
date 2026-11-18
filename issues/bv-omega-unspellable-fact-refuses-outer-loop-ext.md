---
title: bv_omega refuses a whole search when one fact in scope cannot be spelled, which declines an outer loop's #ext
status: open
labels: [tactics, bv_omega, loops, performance]
area: tactics
created: 2026-11-18
updated: 2026-11-18
---

A `for` in a `for` over a span (`Bytes::running_max`, `Bytes::add_earlier`
in `lib/_tests/native/runtime/runtime_lifted_loops_tests.hthr`) has its
outer loop's `T::f_loop#ext` refused, every time, after about a second of
work: a read's `bv_omega` default inside the companion stops with
"`bv_omega` got stuck: could not spell a fact in scope". The fact is the
lifted decrease obligation's hypothesis, which names the inner loop's call
with its squashed fact argument still a search:

```text
__dec_o1: toNat(len(running_max_loop_loop(n, s, i, ofNat(0), squash(bv_omega)).after) - (i + ofNat(1))) < toNat(len(s) - i)
```

`spell_type_source` has no spelling for `squash(bv_omega)`, and
`bv_omega::generate` turns one unspellable restated fact into a refusal of
the whole search (`crates/elab/src/bv_omega.rs`, the `restated` spelling),
although the goal (`i < len(s)`) never needed that fact. The refusal is
recorded and `f` still checks, so nothing fails; the outer loop simply has
no `#ext`, and its `_unfold` is never attempted.

Tried 2026-11-18: dropping an unspellable fact instead of refusing makes
the outer `#ext` (3.8 s) and `_unfold` (2.0 s) check, so the running
maximum got slower (6 s to 13 s) with more companions to show for it. So
the fix wants both parts: keep the search going without a fact it cannot
spell (or spell a squashed found proof), and make the outer companions
cheap, which [[store-under-if-in-lifted-loop-cost]] did for the inner ones.
That is a behaviour change to `bv_omega` (a search that refused now
succeeds), so it goes to Minus.
