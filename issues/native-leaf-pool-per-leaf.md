---
title: Compute the leaf register pool once per compile, not per leaf and node
status: open
labels: [native,perf]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

`Layout::leaf_pool` filters the 14-register pool through `Homes::uses` and
is recomputed at every leaf and every node a leaf compiles
(`lib/native/native_compile.hthr`). In the kernel this dominates emission's
growth over the memory-resident compile
(`docs/native-register-allocation-design.md` §7). It brings
`native_cat_compiled`'s single-`refl` compile close to the per-declaration
fuel, which leaves little headroom for cat to grow. write-elf states emission
a part at a time and is unaffected.

## Scope

- Hold the leaf pool (and `Homes::registers`) in `Layout`, computed once,
  with a lemma that it is the filter.
- `native_cat_compiled`'s compile step count before and after, through
  `scripts/perf ab`.
