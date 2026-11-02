---
title: An 8-byte Level needs an interned join table
status: open
labels: [kernel,performance,representation]
area: kernel
created: 2026-11-02
updated: 2026-11-02
---

Shrink `Level` from 16 bytes to 8, which takes `Term` from 104 to about 80 bytes and `Type` from 56 to about 48.

## Where it stands

[[kernel-compact-level]] made `Level` a 16-byte enum that is canonical by construction: `0`, `ℓ`, `k + 0`, `k + ℓ` and `ω` are inline, and a join of two or more components is an `Rc<Join>` (`crates/kernel/src/level.rs`). Sizes after that round: `Term` 104, `Type` 56, `Val` 72, `VTy` 56, `Elim` 104 (the size tests in `term.rs` and `value.rs`).

## Why 8 bytes needs a different design

The 16 is the floor for safe Rust without interning. An enum that has an `Arc` variant and an inline variant with a payload needs a tag beside the pointer, and the kernel has no `unsafe`, so it cannot pack a pointer and an integer into one word. An 8-byte level therefore has to be a `NonZeroU64` (or `u32`) that either encodes the small forms inline or is an index into an interned join table.

The interner is the hard part. Kernel gate workers run in parallel (eight by default), so the table is shared and needs a lock or a sharded concurrent map. It never shrinks unless it is scoped to a module or session. Interning also makes `==` on joins an integer comparison, which is better than today's pointer-first slice comparison.

## Before taking it

- Measure first. The 16-byte round's perf ab is the baseline. Take this only if node size still shows up after [[elab-probe-clone-copies-attempt]] and [[elab-cx-persistent-binders]] land.
- [[kernel-arena-terms-frozen-prefix]] would give levels an arena-scoped interner for free. If that decision is near, fold this into it.
