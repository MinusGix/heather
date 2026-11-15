---
title: Pool the value arena and the definition-body cache across one typing gate
status: closed
labels: [kernel,conversion,performance]
created: 2026-09-06
updated: 2026-09-11
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

## Log

- 2026-09-11: Chartered (2026-09-11) as the session's one deliberate perf round, design-then-implement, managed agent. Design deliverable: docs/kernel/conversion-query-arena-pooling-design.md. Gate: scripts/bench --check on furnace (same box for before/after); fresh --fast timing table refreshed the same day as the before column.
- 2026-09-11: Design pass landed (2026-09-11): docs/kernel/conversion-query-arena-pooling-design.md. Lever 1 (one BodyCache per gate, owned by the typing Env, fresh on push_tele, also lent to Tc::whnf) is taken: module kernel -12.6%, Omega -3.4%, RSS flat. Lever 2 (arena pooling) is REFUSED by measurement: the allocator share is the value caches' ~1.94 M Rc<VTy>/Rc<Val> allocations per module, 33:1 against arena chunks; removing the chunk ladder entirely measured neutral-to-worse. Follow-on filed as [[value-cache-memo-in-arena]]. Implementation pass launched.
- 2026-09-11: LANDED (2026-09-11), lever 1 only: typing Env owns one BodyCache per gate (fresh on push_tele), lent to every conv query and Tc::whnf; public conv signatures unchanged; new test a_telescope_push_rebuilds_the_body_cache with a negative control. Same-box: module kernel -11%, cold Omega -3.3%, RSS flat, bench 106/106 within thresholds, full suite 2549/0 twice. Lever 2 refused; residue is [[value-cache-memo-in-arena]].
