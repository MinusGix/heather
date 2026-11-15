---
title: The value domain's type memo answers 1.3% of its lookups on the certificate
status: open
labels: [kernel,conversion,performance,evaluator]
area: kernel
created: 2026-09-13
updated: 2026-09-13
---

Measured while taking the before column for
`docs/kernel/kernel-arena-terms-design.md` (2026-09-13, furnace-bb0218be4a, tree
af00689, release `--features value-metrics`, W=1, warm `reused_callee`
`build-x86`):

```
term_cache_lookups 11 728 592   hits 1 374 944   (11.7%)
type_cache_lookups 12 748 766   hits   163 309   ( 1.3%)
```

The **type** memo in `ValueArena` (`crates/kernel/src/value.rs:253`,
`memo_ty`/`cache_ty`) answers one lookup in seventy-eight. The other 12.6 M
each pay a failed table probe, a force, an `Rc<VTy>` heap allocation and an
insert into a 64 Ki-entry bounded FIFO — for a hit rate that would be within
noise of not having the cache at all on this workload. The term memo at 11.7%
is unremarkable by comparison.

A memo that misses 98.7% of the time is either serving a different workload or
serving none. Both readings are interesting and the measurement does not
distinguish them:

- **A different workload.** Omega's CutSat search and the library's own
  conversion-heavy checks may be where `TyClo` reuse actually happens; the
  certificate is generated code with one statement per theorem and little
  structural reuse between them. If so, the number to record is the hit rate
  per workload, and nothing changes.
- **None.** If the rate is this low everywhere, the type memo is costing an
  allocation and a probe per forced type to buy ~1%, and the honest options
  are to delete it (and let `TyClo::Val` carry the only memo) or to fix what
  makes the keys miss — the key is the closure's arena address, so two
  separately-allocated `TyClo`s over the same `(env, body)` never share, and
  `Env::values_ptr_eq` exists precisely because that happens.

## What would settle it

Read `type_cache_lookups`/`type_cache_hits` on the three workloads that
already have `value-metrics` probes (`docs/infrastructure/benchmarking.md`: `lib_std_bitvec`'s
carry test, `x86_64`'s module check, `certgen`'s `add`) plus a cold Omega
closure, and put the four rates beside each other. That is one furnace job and
no code.

## Why it is not folded into an arena round

Under `value-cache-memo-in-arena`'s lever the *allocation* half of this cost
goes away (a bump instead of a malloc) while the probe and the miss stay —
so the arena work would hide the symptom without answering the question, and
the counter it would be read from stops meaning "allocations" at the same
time. Answer this first, or at least record the four rates before that lands.

Trigger: the next round that touches the value memo, `value-cache-memo-in-arena`
first of all.

## Log

- 2026-11-05: gardener: cites a file it shares with [[dependency-policy]] (`docs/infrastructure/benchmarking.md`); [[env-lookup-depth]] (`crates/kernel/src/value.rs`); [[perf-tracking-consistent-environment]] (`docs/infrastructure/benchmarking.md`).
