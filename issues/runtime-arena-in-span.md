---
title: An arena in a runtime fn's written span: allocation, windows and a growing vector
status: closed
labels: [native,runtime,memory]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-24
updated: 2026-11-24
---

Memory a `runtime fn` owns, as an arena inside the one span it writes
(docs/native/rung2-spans-design.md §4, §5): a laid header with the top and
the limit, allocation by compare and add answering a base or `Full`,
windows `(base, count)` read through `Accessor::read_at`, a vector as a
window and a fill mark that grows by allocating a larger window and copying
within the span, and reset to a mark.

Proved once in the library: allocation changes no byte below the old top;
a fresh window is disjoint from every older one; a store into a window
leaves every window disjoint from it; growing keeps the vector's meaning.
The compiler's theorem needs nothing new (one written span). `mmap` stays
[[native-arena-mmap]]; single frees stay [[ownership-discipline-over-code]].

Customers: a growing vector, then the rehashing table of
[[runtime-hash-map-spec]].

## Done when

A growing vector of words is pushed past its first capacity in a ledger row,
compiled, with a run by `refl` that shows the copy; `Full` is answered when
the arena's limit is reached; the four laws are theorems; a Rust export
over it is optional.

## Blocked by

[[runtime-span-of-codec]] for windows of elements other than bytes (a
byte-element vector can start before it).

## Log

- 2026-11-24: Built: `lib/native/runtime/arena.hthr` (`laid record Arena { top, limit, heap: [u64; 16] }`; `alloc` answering a base or `Full` = `2^64 - 1`; `reset` to a mark; a window's `read` and `store` at element `i` of `(base, count)`; the copy loop `copy_at`; a vector as a three-word header in the heap with `new_vec`, `push_in`, `grow`, `push`), its laws `arena_laws.hthr`, probes `lib/_tests/native/runtime/arena_laws_tests.hthr`, and the ledger rows "an arena in the written span" (`runtime_ports_tests.hthr`): allocation, `Full` at the limit, a vector of capacity 2 pushed a third time (the bytes show the copy: header `[5, 4, 3]`, old window `[7, 8]`, new window `[7, 8, 9]`), a push past the limit answering 0 with the bytes unchanged, reset, a stale window as negative control, `runs_held` at an open arena, and `PortArena(size)` at a run-time size (`alloc`, `store` compiled; its copy loop refused: "waits for the loop combinator", round 4 of `loops-on-one-combinator` unblocks it).

  The laws, proved over the compiled functions: `alloc_below` (allocation changes no heap word), `alloc_fresh` (an answer other than `Full` is the old top, inside the limit and the heap, the top past it) with `alloc_apart` and `alloc_full`, `store_apart` (a store into a window changes no read of a window apart from it), `grow_abs` (under `VecInv`, growing that answers 1 keeps the vector's list), and `push_in_abs` (a push with room appends). Representation and what changed in the design: docs/native/rung2-spans-design.md §5 "Built".

  Filed on the way: [[mut-self-arms-calling-two-functions]] (why `push` has no branch equations and its meaning is read off `push_in_abs` and `grow_abs`). Noted, not filed: the `mut self` copy loop gets step equations but no `induct` principle ("not a recursive function whose body is a tree of tests"); its invariant is proved by induction on its measure.

  Left: the arena at a run-time size (after the loop combinator's round 4: the record becomes `Arena(size)`, the limit the carried size); vectors of other elements (the blocker [[runtime-span-of-codec]] for records as elements); `VecInv` kept by `push_in` and `grow` (so a law can chain pushes); a Rust export. The hash map's rehash ([[runtime-hash-map-rehash]]) can use `alloc` for the larger table's window, `store_apart` for the old table's reads staying put while the new one is filled, and `copies`' shape for its reinsertion loop's invariant.
- 2026-11-24: No junk values (Minus, 2026-11-24): `Arena::read` and `Arena::store` take found proofs that the element is inside its window and the window inside the heap (`inside`, `fits`, `:= bv_omega`), as `Bytes::at` and `Vec::at` do, and answer no 0 past the count. A `runtime fn` of a laid record does not take a proof parameter yet, so they are ordinary functions; the compiled form is a refused ledger row (`Arena::port_read`, 'a type with no runtime layout'), and an index read without a test is refused with the found-proof message (`arena_laws_tests.hthr`). `store_apart` and `read_same` restated under the proofs; `read_store_same` and `alloc_inside` added. The vector's header in the arena is accepted as the default (rung2-spans-design §5). `alloc`'s answer moves to an outcome on `claude/span-multiword`.
