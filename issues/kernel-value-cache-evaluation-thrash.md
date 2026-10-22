---
title: Long evaluations by refl thrash the kernel's bounded value cache
status: closed
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

## Log

- 2026-10-22: 2026-10-22: Priced, and fixed by keeping: every `ValueArena` now keeps each value it forced until the query ends (`ValueArena::cache_tm`; kernel DESIGN.md's arena paragraph). The memory argument is the one the FIFO was missing: each cache key is a closure of the arena, which the arena already holds with its environment cells until the query ends, so one `Rc` value per forced closure is a constant factor over what the query holds — the order of its work, which fuel bounds — while a bound below the live set multiplies the work instead. The 4 GiB `lib_std_bitvec` failure that set the bound was from when values owned the closures they reached and the bitvector consumers were superlinear; neither holds now.

  Measured on this box (debug-profile `heather`, kernel and elab at O3, `HEATHER_KERNEL_WORKERS=1`), salted copies of the fixture's runs:

  | run | 64K FIFO + #129 tiers | kept |
  | --- | --- | --- |
  | one byte (`cat_copies_one`) | 892,787 steps | 79,431 |
  | a whole buffer (`cat_copies_whole`) | 895,686 | 79,921 |
  | three bytes one at a time (`at(14)`) | `OutOfFuel` (1,049,979) | 182,533 |

  Linear in the passes. Peak RSS over the suite's heaviest tests, same binaries with and without keeping: `linux_wp` 798/797 MB, `function_ir_lower_calls` 469/465, `lib_std_float_arith` 442/461, `lib_std_bitvec` 104/104, `lib_std_creal` 156/156, `native_source` 586/276 MB (and 7.2 → 2.1 s): less recomputation allocates fewer closures. The whole suite passed with keeping everywhere.

  Since nothing is evicted, PR #129's costly tier (`COSTLY_FORCE`) and glue tombs (`ValueArena::reglue`) had nothing left to do and are gone, as are `ValueArena::retaining` (the tactic host's arena is an ordinary one now) and the eviction counters. Rail: `cat_copies_three` in crates/elab/tests/fixtures/native_source_cat.hthr; `a_query_keeps_every_value_it_forced` replaces the bounded-cache unit tests. `scripts/perf ab --corpus full` numbers are on the PR.
