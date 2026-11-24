---
title: The word map at a capacity that is a parameter, rehashing into a window of twice the capacity
status: open
labels: [native,runtime,data]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-24
updated: 2026-11-24
---

The fixed-capacity word map is specified ([[runtime-hash-map-spec]],
`lib/native/runtime/word_map.hthr` and `word_map_laws.hthr`) at four slots,
the capacity its record fixes (`[u64; 4]`, `band(3)`). What is left of
docs/native/rung2-spans-design.md §7:

- **Capacity a parameter.** The table's slots a `Span<Entry>(cap)` in a
  window of the arena ([[runtime-arena-in-span]], [[runtime-span-of-codec]]),
  the next slot `(j + 1) % cap`. The laws carry over: every distance in
  `word_map_laws.hthr` is `(b + cap - a) % cap` with `cap` the literal 4,
  and the probe-step lemmas (`step_budget`, `wraps_past`, …) are the only
  places the number matters. At a variable `cap` they are nonlinear for
  `omega`; state them over `cap` with the remainder's laws, or over
  `dist` with its own step lemmas ([[arithmetic-definition-opaque-at-open-arguments]]).
- **Rehashing.** A full table (or a load factor reached) allocates a window
  of twice the capacity and reinserts every entry; its law is that every
  lookup is unchanged (`WordMap::Moves` both ways is the statement the
  insert proofs already use), and the reinsertion is a loop over the old
  slots whose invariant is "the new table is the old one's first `i` slots'
  rows".
- **The invariant keeps a slot empty** (insert answers full at `cap - 1`
  keys): backward shifting needs an empty slot to stop at
  (`WordMap::shift_at_full_is_wrong`). With rehashing the full answer goes
  away and the load factor keeps the slot.

## Log

- 2026-11-24: The arena is built ([[runtime-arena-in-span]], `lib/native/runtime/arena.hthr`, `arena_laws.hthr`) at a heap of sixteen words: rehashing can take its larger table's window with `Arena::alloc` (`alloc_fresh`/`alloc_apart`: apart from the old table), fill it while the old table's reads stay put (`store_apart`), and state the reinsertion loop's invariant as `Arena::copies` states the copy's (induction on the measure, words inside and outside the window). What it cannot use yet: a table of a run-time capacity in a window needs the loop combinator's round 4 (loops over a record that takes parameters), and entries that are records need [[runtime-span-of-codec]]'s elements.
