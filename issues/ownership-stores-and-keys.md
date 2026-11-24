---
title: Stores, keys and generations: shared mutation's meaning, with the arena's windows as typed handles
status: open
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
