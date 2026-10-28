---
title: Give each loop its own live set, not one per tested word
status: open
labels: [native,x86]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

`Homes.loops` is indexed by the word a `Repeat` tests
(`docs/native-register-allocation-design.md` §3), so two loops testing one
word share a set and the allocator gives them the union. The union is closed
for both unless the larger set makes a write interfere with a word sharing
its register, and then `Source::allocation_ok` refuses: a refusal no
allocator can avoid short of moving a word to its slot. The sets may also
hold an id twice (the union of lists does not dedupe across loops' growth),
which costs the check list work but not soundness.

## Scope

- Index loop sets by the loop's position in the statement tree (a pre-order
  count, as `emit` threads labels), or carry the set in the `Repeat` node of
  a checked annotation.
- Keep each set duplicate-free on the allocator side.
- A probe in `lib/_tests/native` with two loops on one word whose union
  interferes, refused today, accepted after.
