---
title: An 8-byte Level needs an interned join table
status: closed
labels: [kernel,performance,representation]
area: kernel
created: 2026-11-02
updated: 2026-11-10
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

## Log

- 2026-11-10: Done, without the arena. `Level` is a `Copy` `NonZeroU64` (`level.rs`): a three-bit tag, then a constant below 2^61, or `n + ℓ` with `ℓ` in 32 bits and `n` below 2^29, or the index of a join, or `ω`. Joins live in one process-wide table (`RwLock` over a `Vec` and a `BTreeMap` by content, entries leaked so a reader holds `&'static Join`), with a per-thread copy of what the thread has seen, so a gate worker takes the lock only for a join it has not met. `Zero`, `Omega` and `Var` keep their names as associated constants and a `const fn`, so the two thousand sites that write them did not change; one `match` on a `&Level` in the exporter needed a `*`. `Hash` hashes the spelling, not the word, because an index depends on the order a process met its joins in and a hash may outlive the process; the images and the Merkle walk already read `Level::parts`.

  The table is all but unused: after a cold check of the showcase and after the x86 certificate of `examples/x86-native/levels.hthr` it holds **no entry**. Every level those runs build is a constant or `n + ℓ`. So the lock, the leak and the per-thread copy are costs on paper, and the reference-model tests (300 seeds against the tree normal form) are what exercises the join path.

  Sizes: `Term` 104 to 80 bytes, `Type` 56 to 48, `Val` 72 to 56, `VTy` 56 to 48, `Elim` 104 to 80. The release binary 22.4 MB to 20.8 MB (no clone or drop glue for a level).

  Measured on the cloud box over the stack at [[emission-decode-walks-every-annotation]], `scripts/perf ab`, cold, five interleaved samples, 45 counter columns identical throughout. This change alone, width one, showcase: peak resident 430-492 MB to 386-411 MB (−9.7%, separate); wall median −4.5% and gate −5.5%, neither separate. Instructions 46,884 M to 44,553 M, but more than half of that is luck: a term node (two counts, a three-word head, 80 bytes) lands on the 128-byte class, a power of two, which is the one kind of size mimalloc 3 serves an aligned request for without a fallback ([[global-allocator]]).

  That luck is why this landed with two other changes, measured together in [[global-allocator]]'s log: the node head in two words ([[free-variable-bounds-in-the-node]]) and mimalloc 2. A term node is then 112 bytes in the 112-byte class (it was 144 in the 160-byte class) and a type node 80 in the 80-byte class (96 in 96).

  Left: `Term` is sized by `Case` and `ElimCodeTm` (nine words of payload), and a term node drops a class again only at 64 bytes, which is eight variants to slim; `Type` is sized by `TyPi` and by `GlobalTy`'s `LocalSubst` (40 bytes: a `Vec` and a tail). Neither is worth an issue until a profile says node size again.
