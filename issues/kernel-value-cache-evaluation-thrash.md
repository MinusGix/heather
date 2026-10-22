---
title: Long evaluations by refl thrash the kernel's bounded value cache
status: open
labels: [kernel,performance,native]
area: kernel
milestone: [hih-pl-source]
created: 2026-10-22
updated: 2026-10-22
---

The effectful source's programs are meant to run by kernel evaluation first
(`docs/native-effect-source-design.md`; Minus, 2026-10-21). Running `cat`
(`crates/elab/tests/fixtures/native_source_cat.hthr`) against a scripted
world by `refl` stops a few loop passes in. The cause is that the value
cache drops values that are still live, not the cost of the work itself.

The run is width-64 FunctionIR arithmetic over an environment of word cells
(`lib/native_source.hthr`, `Env`). Each cell is a constructor field, so it
is forced once and shared through the term cache. But every 64-bit operation
forces a few thousand intermediate values. Once a run has forced more than
`VALUE_CACHE_CAPACITY` (64K) of them, the FIFO evicts cells that later
statements still read. Each evicted cell is then recomputed back through the
run's history, which compounds.

## Measurements

Release `heather check`, cloud box, kernel steps from `scripts/timings`.

| run | 64K FIFO | 16M-entry cache |
| --- | --- | --- |
| `cat_copies_one`, `Env` holding `BitVec(64)` cells | over 1,048,576 (`OutOfFuel`) | 102,894 |
| `cat_copies_whole`, same | `OutOfFuel` | 103,394 |
| `cat_copies_one`, `Env` holding `Nat` cells (as landed) | 928,434 | not measured |

- Second-chance (CLOCK) eviction at 64K did not help: the same four runs
  still went `OutOfFuel`. The workload scans; it is not a small hot set.
- PR #129's protected tier for costly forces moves `cat_copies_one` only
  from 928K to 893K steps.
- Continuation-passing `denote` (no `bind` rebuilding trees) reaches about
  297K steps on the `BitVec(64)`-cell environment. It shrinks the working
  set but does not remove the cliff: three bytes at one byte per call still
  ran out. The layer keeps `bind`/`iter`, which is its meaning.

The landed fixture's copy runs sit at about 90% of `DEFAULT_FUEL`, so they
are fragile. They are this issue's instrument.

## What would fix it

The tactic host already solved this for its own runs with
`ValueArena::retaining` (`docs/inductive-tier2-w-lowering.md`, part 3). Two
directions to price, as kernel design and not as a constant:
- A retaining arena for an evaluation-shaped gate query, for example `refl`
  at a closed goal, bounded by the fuel the query may spend.
- A cache keyed on liveness, where an entry stays while a reachable
  constructor field holds it, instead of on insertion order.

The memory cost of retention is the real question:
`issues/bitvec-closed-reduction-cost.md` records unbounded strong memos
exceeding the 4 GiB test cap on `lib_std_bitvec`.

Done when: the native source copy runs, including three bytes at one byte
per call, check with fuel to spare, and a run's step count grows linearly
in its loop passes.
