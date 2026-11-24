---
title: An arena in a runtime fn's written span: allocation, windows and a growing vector
status: open
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
