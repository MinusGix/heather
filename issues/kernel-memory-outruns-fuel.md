---
title: Make a conversion's fuel bound its memory under the rail
status: open
labels: [kernel,conversion,robustness]
area: kernel
created: 2026-11-19
updated: 2026-11-19
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
