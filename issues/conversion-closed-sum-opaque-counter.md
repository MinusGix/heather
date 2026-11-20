---
title: A closed number against a sum of literals filled the value arena in one δ-step
status: closed
labels: [kernel,conversion,performance]
area: kernel
code: crates/kernel/src/eval.rs @ d7abb435
created: 2026-11-19
updated: 2026-11-19
---

Found on PR #808 (`lib/_tests/native/native_compile_tests.hthr`):

```
theorem alternating_left(): alternating().left(alternating().homes(), alternating().bodies()) = 8 + 3 * 40 + 3 * 40 { refl }
```

ran the kernel gate out of its 8 GiB rail in about five seconds, the value
arena failing to allocate, while the same goal stated `= 248` checks in a
tenth of a second. The test was written with the numeral to get past it.

## Cause

`Source::left(…)` unfolds to `Source::top(…) + 8`, so both sides are
applications of `Nat::add` and conversion's δ-lazy stage first compares them
argument by argument (`Conv::tm_w`, `Conv::delta_lazy`): `Source::top(…)`
against `8 + 3 * 40`. The newer side is advanced one opaque δ-step at a time
(`Dom::delta_tm`, `Eval::delta_step`), down to `Nat::max(reach_by(…),
functions_room(…))`.

One δ-step of that `Nat::max` was the whole cost. `max` is a fold the run
machinery accelerates (a synchronous one), and the machinery unfolds a glued
scrutinee of such a fold even in an opaque run (`Eval::step_neutral`), as it
does the right-hand counter of a synchronous fold (`fire_nat_sync`) and a
glued tail under a run (`Frame::NatRunTail`). But it forced the counter *in
the run's mode*, opaquely: inside `reach_by`'s body every match on a glued
value (the source's fields, the call graph's rows of levels) stalled as a
spine, and the next accelerated fold that wanted that value as a number
forced it in turn, replaying the spine. Sampled during the blowup: glued
neutrals with spines of 30 to 90 eliminations, `Memo`/`Elim` frames
alternating a hundred and more deep, and about seventy-five machine steps
per unit of fuel: the arena passed six gigabytes as the conversion's 2^20
units ran down, so the rail came first.

With `= 248` the other side has no defined head, so the left side is unfolded
by one transparent run (`delta_to_head_tm`) and none of this happens.

## Fix

`Eval::force_counter`: a counter the run machinery needs as a number is
forced δ-transparently, to its δ-transparent head, whatever the mode of the
run that meets it. The three sites above use it when the run is opaque; a
transparent run keeps the frame-pushing path, so it nests at most once. The
number is the same either way; only the replays go. Both spellings of
`alternating_left` now cost the same (about 350 K steps, 0.1 s gate).

The test file states `alternating_left` and `alternating_shallow_left` as the
sums again, and `scripts/bench-probes`' `conv/closed-sum` case
(`perf/bench/fixtures/closed_sum_conversion.hthr`) keeps both spellings side
by side.

## What is left

- **Fuel does not bound memory under the rail.** The gate died at the
  allocator, not with `OutOfFuel`: one conversion's budget let the value
  arena grow past the 8 GiB rail. Owned by [[kernel-memory-outruns-fuel]].
- **The memo is still mode-blind.** Forcing a glued unfolding transparently
  here is one site of [[value-memo-evaluation-mode]]'s proposal 2 (always
  force `n.unfold` transparently); the other opaque δ-steps are unchanged.
- **A tiny reproduction was not found.** Toy `max`-over-rows programs with
  records and options did not blow up on the old kernel; the fixture is the
  real compiler's `Source::left`. A kernel-level bench (`scripts/bench`) would
  want one.

## Related

[[runtime-link-compares-functions]] is the other cost found in the same-head
attempt; [[conversion-meet-past-newer-head]] owns the newer-side lockstep.

## Log

- 2026-11-19: found, fixed in the evaluator (`Eval::force_counter`), bench
  case `conv/closed-sum` added.
