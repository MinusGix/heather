---
title: Make a conversion's fuel bound its memory under the rail
status: closed
labels: [kernel,conversion,robustness]
area: kernel
created: 2026-11-19
updated: 2026-11-20
---

A conversion gets 2^20 units of fuel, and the evaluator charges a unit per
δ-step, per fold or run step, and per unfolding it forces, not per value it
allocates. A run whose machine steps mostly stall and replay (eliminators on
glued scrutinees, each pushed and replayed) allocates many values per unit.
In [[conversion-closed-sum-opaque-counter]] it was about seventy-five machine
steps per unit, and the value arena passed six gigabytes before the budget ran
out: the gate process died at the allocator under the 8 GiB rail, with no
refusal, no declaration named and no `--timings` row for the comparison.

A refusal is the better failure: `OutOfFuel` names the declaration and the
user can see what to change. Two shapes, not chosen yet:

- charge fuel per arena chunk (or per N values) the run allocates, so a
  budget implies a memory bound (cheap: the arena already knows when it
  grows a chunk);
- a byte budget per conversion beside the fuel, checked where the arena
  grows, failing as `OutOfFuel` does (no refund, the verdict independent of
  where it died).

Either changes which declarations pass at the edge of their budget, so the
library sweep and `scripts/bench --check` are the gate. Kernel change: for
Minus.

## Related

[[conversion-closed-sum-opaque-counter]], [[value-memo-evaluation-mode]], [[conversion-fuel-failure-says-where]].

## Log

- 2026-11-19: opened beside the Nat::max δ-step fix (linked above); nothing built.
- 2026-11-20: built the second shape, a byte limit beside the fuel
  (Minus: "tackle #1"). `ValueArena::bytes` sums its regions' values
  (a walk of their chunks); `Eval::spend` and `spend_n` read it each time
  the remaining fuel crosses a multiple of `ARENA_CHECK_EVERY` (1024) and,
  past `ARENA_BYTES_LIMIT` (2 GiB), spend the run's fuel, so the query ends
  as `OutOfFuel` with no refund and at a point fixed by the work done.
  Measured first, a cold library check (every gate folder, one store) with
  each run's arena size logged: the largest query held 770 MiB by this count
  (`lib/_tests/std/crypto`), then `lib/_tests/native` 753, `lib/_tests/std/core`
  380, `lib/_tests/std/tactic` 272, `lib/native` 233; everything else under
  140. Control: with the counter fix of the δ-step blowup taken out, the
  fixture's sum spelling is refused as `OutOfFuel` in 2.8 s of gate, with its
  `--timings` row, where it had died at the allocator.
