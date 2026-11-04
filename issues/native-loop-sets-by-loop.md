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
word share a set. The allocator grows all the sets together until each is
closed (`Homes::closed`), so a shared entry is closed for both loops and the
check passes. `yes STR` has two such loops. A first version joined
separately grown sets, and that left a nested loop's set unclosed. The cost
now is precision: each loop keeps the other's words alive, which can cost
a register.

## Scope

- Index loop sets by the loop's position in the statement tree (a pre-order
  count, as `emit` threads labels), or carry the set in the `Repeat` node of
  a checked annotation.
- A probe in `lib/_tests/native` with two loops on one word, whose homes
  improve once each loop has its own set.
