---
title: Arena allocation and datarepr cells for lists and trees in runtime fns
status: open
labels: [native,memory,datarepr]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-10-31
updated: 2026-10-31
---

Round R9 of `docs/compiler-milestones-proposal.md` (§4.2 N4, §7), milestone `nh-heap`: recursive data at run
time. `hih-first-alloc` moved here.

## Scope

- A short design section first: a bump arena in the data segment, then `mmap` as a Linux event, with exhaustion as a defined exit.
- `datarepr` instances that give `List` and small trees arena cells ([[datarepr-separation]]), and the default setup compiling functions over them.
- `sort` and `tac` as the customers.
- If the arena needs the footprints of [[wp-view-separating-product]] before anything runs, say so and stop there.
- A metered bound is [[memory-bound-certificates]]'s follow-up, not this round's.

## Done when

`sort` (lines into a list) and `tac`, written as ordinary Heather, pass their GNU tests.
