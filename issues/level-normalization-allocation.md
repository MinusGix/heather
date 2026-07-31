---
title: Level normalization allocates a BTreeMap per comparison; ~14% of the ir_v1 profile
status: open
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-07-31
---

Found in the post-definitions perf profile of release `heather check
lib/ir_v1.hthr` (2026-07-31, ~2.1s): level arithmetic is ~14% of the
run — `Level::count` 4.0% self, `Level::normalize` 2.6%, `Level`
drop-glue 3.5%, plus clones. Filed as an accumulator per the 2026-07-31
perf-tracking decision; no round is chartered by this file alone.

Mechanism: `Level::normalize` (crates/kernel/src/level.rs:66) builds a
fresh `BTreeMap<UnivVar, u64>` on every call via `count`, and level
comparison on the conversion path normalizes both sides each time —
there is no caching and no cheap structural pre-check, so two
syntactically identical levels still pay two full walks and two map
allocations to be found equal.

Candidate levers, cheapest first:
- structural-equality fast path before normalizing (most compared levels
  are literally the same shape, often the same `Rc`);
- a small-vec or inline representation for the variable counts —
  `BTreeMap` is heavyweight for the typical zero-or-one-variable level;
- memoized `LevelNf` on the term side, which is a representation change
  and would need its own decision.

Trigger: level ops still a top-5 self-time block on a real workload
*after* the Ψ-clone round ([[context-representation-clones]]) lands —
that round owns today's #1 line and shifts every percentage here.

## Log

- 2026-07-31: Filed from the ir_v1 profile taken while sizing the round after definitions ([[simulate-conversion-cost]] close-out).
