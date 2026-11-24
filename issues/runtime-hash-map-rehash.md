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
