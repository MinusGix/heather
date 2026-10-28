---
title: Make the register allocator a class whose instances prove they are never refused
status: closed
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

## Resolution

- 2026-10-28: Closed. The allocator is the class `Allocates<A>`
  (`lib/native/native_alloc.hthr`): `assign: A → Source → Homes` and the
  law `never_refused`, completeness against `Source::allocation_ok`. A
  tuning is a value of the type. Instances: `SpillAll`, and `Greedy {
  loop_weight }`, write-elf's at `Greedy::standard()`, so
  `Source::homes_ok` makes reason 12 unreachable for write-elf.
  `SpillAll`'s proof does not show the growth reaches a closed set within
  its fuel, as the scope above planned: where the growth stops is checked
  once more, and the widest sets (every word the program names, in every
  loop's set) stand in when it is not closed. `Stmt::checked_wide` proves
  those closed for every program by one structural induction, so no
  monotonicity or counting lemma is needed, and the growth stays a
  heuristic that gives the least sets. `Greedy`'s colouring is not proved;
  its `assign` falls back to the slots' homes when the check refuses them
  (`Homes::or_else`), and `lib/_tests/native/native_alloc_tests.hthr`
  probes that the colouring passes on its own. Per-procedure allocators
  need procedures; their composition is written down in the design doc §6
  and stays in [[native-register-moves-and-convention]]'s scope.
