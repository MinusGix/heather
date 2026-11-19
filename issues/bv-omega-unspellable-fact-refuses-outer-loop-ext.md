---
title: bv_omega refuses a whole search when one fact in scope cannot be spelled, which declines an outer loop's #ext
status: closed
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

## Log

- 2026-11-18: Fixed at the cause rather than in `bv_omega`. The squashed
  fact in `__dec_o1` was a search because the loop lifter wrote a bare
  `bv_omega` as the inner call's fact argument, which no lowering lifts:
  `measure::lift_found` lifts searches left to a parameter's default, and
  the outer loop's body has no other read, so it had no found proof at all
  and every companion copy searched again. The lifter now passes each fact
  where a loop starts as `bitvec_omega::found_fact<P>(fact := bv_omega)`,
  and the caller's lowering lifts that named search into `f#found_N` with
  the goal `∥P∥` as written (`Rewrite::found_fact`, no query needed). The
  decrease hypothesis then names `f#found_1(…)`, which spells, so the outer
  `#ext` and `_unfold` check, and the search runs once instead of per copy:
  with `--cache --timings` on `runtime_lifted_loops_tests.hthr`,
  `Bytes::running_max` 4.8 → 4.1 s and `Bytes::add_earlier` 3.1 → 2.3 s,
  the rest the same or faster. Probe: `running_max_outer_stops` cites the
  outer loop's `::done`, which master refuses.

  Tried first and dropped: giving the facts a parameter default and leaving
  them out at the entry. A default is checked in its declaring module's
  name scope, where `found_fact`'s search could not spell the caller's own
  `Bytes::len`. On the way it showed that a default's search under a plain
  `if` could not see the if's test (`if i < s.len() { s[i] }` refused): the
  hygienic context a default runs in dropped the match's pending
  equations. Fixed in the same change (`Cx::hygienic` keeps
  `pending_eqs`), probe `word_at_tested` in `squash_conditions_tests.hthr`.

  Not changed: `bv_omega` still refuses a whole search when a fact it would
  restate has no spelling. Nothing here needs it any more; if it shows up
  again, dropping such a fact rather than refusing is the measured option
  above.
