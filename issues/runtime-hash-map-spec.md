---
title: A hash table runtime fn proved to be a finite map
status: open
labels: [native,runtime,data]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-24
updated: 2026-11-24
---

The ledger's fixed-capacity word map (`PortMap`,
`lib/_tests/native/runtime/runtime_ports_tests.hthr`) is compiled with its
agreement, but nothing says it is a map. docs/native/rung2-spans-design.md
§7: since a `runtime fn` is the Heather function its agreement certifies,
its specification is a theorem about that function, against `assoc.hthr`'s
laws, with no `datarepr` between.

## Scope

- `abs(m)`: the association list of the occupied slots; `inv(m)`: every key
  reachable from its home slot without passing an empty one, distinct keys,
  `count` the occupied slots.
- `insert` keeps `inv` and, on its success arm, agrees with `assoc_set` at
  every key's lookup (not as lists: `assoc_set` shadows by consing); `Full`
  only when `count = cap`. `get` is `assoc_get` under `inv`.
- Deletion by backward shifting, keeping `inv`.
- Then, over [[runtime-arena-in-span]], a table that rehashes into a window
  of twice the capacity.

The table belongs in the library (a module under `lib/native/runtime/` or
`lib/std/data/`), with the ledger's rows citing it.

## Done when

The three laws (`get` after `insert` at the key and at another, `get` after
`remove`) are theorems at every table satisfying `inv`, over the compiled
functions; a negative control (a probe that skips the home slot) is refuted
by a `¬` theorem at a closed table.
