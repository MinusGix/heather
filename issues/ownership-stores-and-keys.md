---
title: Stores, keys and generations: shared mutation's meaning, with the arena's windows as typed handles
status: closed
labels: [ownership,library,native]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

Shared mutation's meaning (`docs/language/ownership-design.md` §10.7): a store and keys, with a key's validity a proposition about the store's value, and the arena as the first customer. Pure library work.

## Scope

- **A store with keys**: allocation answers a fresh key and keeps every other key's value and validity; a store through a key keeps the others; freeing (or a reset) ends validity. `Valid(store, key)` is a proposition with a decider.
- **Generations.** A generation kept as erased state so that a key from before a reset is not valid after later allocations reuse its cells. The same generation kept at run time and compared is the helper: a checked access proved to decide `Valid`, so the static and the checked routes discharge one obligation (vision principle 13).
- **The arena** (`lib/native/runtime/arena.hthr`, `arena_laws.hthr`): a window and a vector header as typed handles; `read` and `store` ask `Valid`; `alloc`, `store` and `grow` keep the validity of other windows; `reset` ends the windows above its mark. `stale_windows_meet` is restated: the stale window has no proof of validity (a `¬` theorem), and an access to it with a found proof is an `expect-error` declaration.
- **A graph with shared nodes and mutation** over the store (§6 example 6): once with keys valid statically, once through the checked access.

How erased state that a `mut self` method changes is carried is the design note's open question §13.4; this issue settles it for the arena and records the answer there.

## Done when

The arena's laws are restated over typed handles with the existing ones as consequences, the stale window is a refusal with its reason, the graph example is proved both ways, and the library gate passes.

## What it assumes from elsewhere

- **[[ownership-paths]]** owns paths and `Valid` for parts of an owned value. Assumed here: only its statement of `Valid`, so a key can be a path step.
- **[[runtime-erased-parameters]]** owns compiling an access that carries a proof. Until it lands, the arena's `read` and `store` stay ordinary functions.

## Log

- 2026-11-24: Built (2026-11-24, branch `claude/ownership-stores-and-keys`).

  - **The store** (`lib/std/data/store.hthr`, probes `lib/_tests/std/data/store_tests.hthr`): slots `Live(gen, value)` / `Free(gen)`, keys `(index, gen)`. `Valid(s, k)` is `s.get(k).is_some()` being `True` (the partial read answers, the form paths use). `read`/`write` take it by `known`. Laws: `alloc_reads`, `alloc_valid`, `alloc_fresh`, `alloc_keeps`, `alloc_get_cases`, `alloc_index_fresh`, `put_reads`, `put_other`, `put_valid`, `free_ends`, `free_other`, `free_some`, `retain_get`/`retain_some` (a reset as keys). Generations: `free` makes a key `Stale`, which `alloc`/`put`/`free` keep (`*_keeps_stale`), so `stale_after_reuse`. The helper: `check` (the generation compare) with `check_decides`, and `checked: When<V, s.Valid(k)>` with `checked_option`. Negative controls: the stale key a `¬` theorem, its read refused naming `Store::Valid`, and the slot read without its generation answering the new value.
  - **The arena** (`lib/native/runtime/arena_handles.hthr`, probes `lib/_tests/native/runtime/arena_handles_tests.hthr`): `Heap { arena, claims: Store<Claim>, ok: HeapInv }`, `Window { base, count, key }`, `Heap::Valid` = the key's read answers the window. `read`/`store` take it; `valid_apart` (two valid windows of different keys are apart) makes `store_apart` premise-free; `alloc_valid`, `alloc_keeps`, `alloc_reads_kept`, `alloc_other_key`; `reset_ends`, `reset_keeps`, `reset_reads_kept`. Vector: `VecHandle`, `VecOk`, `vec_inv` (into the arena's `VecInv`), `Heap::grow` with `grow_keeps`, `grow_reads_kept`, `grow_items` (= `grow_abs`), `grow_ok`, `reset_ends_vec`. The existing laws stand and are what these are proved from (`Arena::store_apart`, `read_store_same`, `read_same`, `alloc_fresh`, `grow_abs`); `arena_laws.hthr` gained `alloc_limit`, `alloc_full_same`, `reset_limit`, `reset_top_cases`, `Grown`/`grow_moves`/`grow_cases`. `arena.hthr` untouched.
  - **The stale window**: `stale_window_invalid` (`¬Valid`), `stale_by_law` (from `reset_ends`), and `stale_read`/`stale_store` refused with "`read`'s `valid` was left to its default, which did not give `Heap::Valid((SECOND).after, W1)`"; `stale_windows_meet` restated beside it. After a grow the released data window is refused the same way.
  - **The graph** (`lib/std/data/store_graph.hthr`, probes `store_graph_tests.hthr`): `bump_shared` (a write through a shared node seen through both edges) statically; `bump_checked` with `bump_checked_valid`, `bump_checked_invalid`, `bump_checked_shared`.

  Decided on the way (recorded in `docs/language/ownership-design.md` §10.7 "Built" and §13.4):
  - §13.4 for the arena: an erased field beside the laid record, since `Mutated<Self, R>` cannot change a type parameter and the claims are history no function of the words recovers.
  - The generation is per slot, not per store: a reset frees only the windows above its mark.
  - `Heap::Valid` is the store's validity with the words agreeing (`key_valid` gives the store's), an equation rather than a Bool, so `known` finds it and a closed stale window is refuted by a constructor clash.
  - The arena's checked route is not a word compare without a layout change; left to [[arena-runtime-generation]].

  Residue filed: [[arena-runtime-generation]], [[arena-handles-push-and-new-vec]], [[runtime-record-erased-fields]], [[mutated-result-dot-call-diagnostic]] (a dot call of a plain-`self` function answering `Mutated` is refused as a `mut self` call, with its message lost under `.value`; the library spells those calls qualified).
- 2026-11-24: Verified: `scripts/test --pr` gave `== suite: 914 passed, 1 failed, 1 ignored ==`; the library gate (`crates/cli/tests/library.rs`) and `lib_closures` passed. The one failure was `frontend_bench_smoke`'s "split exceeds the run it came from" for `scale/declarations`, a wall-clock phase split under load, which passed alone right after (`== suite: 5 passed, 0 failed, 0 ignored ==`); nothing it measures is in this change.

  Aligned with `ownership-paths` (its `Path::Valid` is `Exists a. get = Some(a)`): `Store::valid_exists` and `Store::exists_valid` state the key's validity in that form both ways, so the later key-as-path-step is a definition. Nothing in `arena.hthr` or the `arena_laws.hthr` names that package cites was renamed.
