---
title: Pool the value arena and the definition-body cache across one typing gate
status: open
labels: [kernel,conversion,performance]
created: 2026-09-06
updated: 2026-09-06
---

Module-only profile datum from the 2026-09-06 x86 kernel round
([[value-domain-allocation-constant]] carries the numbers): ~30% of the
five-node module's kernel wall is the allocator (`_int_malloc`,
`malloc_consolidate`, `unlink_chunk`), and ~8% is `ShiftGlobal` rescoping of
definition bodies. Both are per-query costs: `conv_type`/`conv_term` build a
fresh `ValueArena` (five typed arenas, two caches) and a fresh
`reduce::BodyCache` for every query, and a typing gate makes tens of
thousands of queries against one Ψ.

## Levers

- **Body cache per binding check.** The cache is keyed by `GlobalVar`
  relative to Ψ; within one `check_global_bindings` step Ψ is fixed, so the
  `Tc` can own one `BodyCache` and lend it to every query of that binding.
  Verdict-neutral: the memoized value is a pure function of (Ψ, index).
- **Arena reuse.** Keep one `ValueArena` per gate and reset it between
  queries instead of dropping and reallocating; the bounded FIFO caches
  must be cleared per query (closure addresses are recycled). typed_arena
  has no reset without drop, so this is either a pool of arenas or a
  first-party bump region with a reset.

## Acceptance

- `scripts/bench --check` shows the constant families (`conv/simulate-*`,
  `wf/check-tree`, `check/generated-terms`) moving together and no
  exponent change.
- No verdict, fuel policy or cache-eviction semantics change; the
  `value-metrics` counters still attribute per gate.

## What it assumes from elsewhere

- **[[value-domain-allocation-constant]]** owns the constant's history;
  this issue owns the two specific levers.
