---
title: Make the register allocator a class whose instances prove they are never refused
status: open
labels: [native,x86]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

Minus (2026-10-28): the allocator could be a type class with proofs that it
respects some properties, so it can be swapped or tuned; consider different
allocators per function. Today it is `record Allocator { assign: Source →
Homes }` (`lib/native/native_alloc.hthr`). Soundness needs no proof from an
allocator, since the compile checks its homes
(`docs/native-register-allocation-design.md` §4, §6). What an instance can
still prove is completeness: `∀ src, src.allocation_ok(assign(src))`, so
reason 12 is unreachable by proof.

## Scope

- The class: `assign` plus the completeness law.
- `spill_all` as the first instance. Its proof needs `loop_grow` to reach a
  closed set within `loop_fuel` (each non-closing pass adds a word below the
  slots) and liveness monotone in a loop's set.
- Per-function allocators once procedures exist: each procedure's homes
  checked against its body, composed through the boundary contract of
  [[native-register-moves-and-convention]].

## What it assumes from elsewhere

- **[[native-register-moves-and-convention]]** owns the calling convention.
  Assumed here: only that a call site's `Held` is re-established from it.
