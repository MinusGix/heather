---
title: Compute the leaf register pool once per compile, not per leaf and node
status: closed
labels: [native,perf]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

`Layout::leaf_pool` filters the 14-register pool through `Homes::uses` and
is recomputed at every leaf and every node a leaf compiles
(`lib/native/native_compile.hthr`). In the kernel this dominates emission's
growth over the memory-resident compile
(`docs/native/native-register-allocation-design.md` §7). It brings
`native_cat_compiled`'s single-`refl` compile close to the per-declaration
fuel, which leaves little headroom for cat to grow. write-elf states emission
a part at a time and is unaffected.

## Scope

- Hold the leaf pool (and `Homes::registers`) in `Layout`, computed once,
  with a lemma that it is the filter.
- `native_cat_compiled`'s compile step count before and after, through
  `scripts/perf ab`.

## Log

- 2026-10-28: Done. `Layout` has two more fields, `pool` (the leaf pool) and
  `taken` (`Homes::registers`), and `Layout::of(low, capacities, homes)`
  builds a layout with both computed from the homes. `Source::layout`,
  `Target::layout` and every `fits` statement (the region's, the compile
  theorem's, the ELF theorems', write-elf's `{p}_fits`/`{p}_room`) go through
  `Layout::of`, so the proofs about a target still see the filters by
  unfolding; `Layout::of_pool` and `Layout::of_taken` state them. The kernel's
  thunk cache keeps a forced field for the whole query, so each filter is
  evaluated once per compile instead of at every read (seven pool reads and
  one `taken` read per leaf). No proof needed more than the spelling change
  from `layout.homes.registers()` to `layout.taken`.
- `scripts/perf ab --source-patch` over `native_cat_compiled` (cloud, width
  one): `cat_compiled`'s steps 966,109 → 765,366 (−20.8%), from 92% of the
  2^20 fuel to 73%; `cat_compiles` and `cat_short` move the same. Elsewhere in
  the run no counter moved by more than ~1%.
- What the remaining 765K is, by probe theorems over the same terms: the
  allocation check (`Source::allocation_ok`) ~104K, emission to a program
  ~385K, and the rest the finished program's `laid_out` check. The check's
  cost is [[native-allocator-cost]]'s.
