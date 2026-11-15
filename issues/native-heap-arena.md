---
title: Arena allocation and datarepr cells for lists and trees in runtime fns
status: closed
labels: [native,memory,datarepr]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-10-31
updated: 2026-11-03
---

Round R9 of `docs/native/compiler-milestones-proposal.md` (§4.2 N4, §7), milestone `nh-heap`: recursive data at run
time. `hih-first-alloc` moved here.

## Scope

- A short design section first: a bump arena in the data segment, then `mmap` as a Linux event, with exhaustion as a defined exit.
- `datarepr` instances that give `List` and small trees arena cells ([[datarepr-separation]]), and the default setup compiling functions over them.
- `sort` and `tac` as the customers.
- If the arena needs the footprints of [[wp-view-separating-product]] before anything runs, say so and stop there.
- A metered bound is [[memory-bound-certificates]]'s follow-up, not this round's.

## Done when

`sort` (lines into a list) and `tac`, written as ordinary Heather, pass their GNU tests.

## Log

- 2026-11-02: Design and the back half landed (docs/native/native-heap-arena-design.md).
  The arena is a `Source` buffer and a top word, so the compiler and
  `native_compile_correct` are unchanged, and running out branches to an exit
  the program gives (§1–§2). The stop condition did not fire: the arena needs
  no [[wp-view-separating-product]] footprints, because buffers are already
  disjoint in the source's meaning and the compiler's theorem (§1). The
  representation of `List<List<BitVec(8)>>` in arena cells and its laws,
  `ArenaRef::nil_abs`, `extend_abs` and `cons_abs` (the image on the
  allocation's success arm, FINDING 1), are proved in
  `lib/native/native_arena.hthr`. The builder's arena is
  `lib/native/native_build_arena.hthr` (it reads and writes names without
  shifts, which the compiler does not take yet,
  [[function-ir-x86-shift-legalization]]); `tac` and `sort` over it are in
  `lib/native/native_heap_tools.hthr`, with GNU tests in
  `crates/cli/tests/native_tools.rs`. "Written as ordinary Heather" needs the
  `runtime fn` front end to lower lists and I/O (R5, R6), so it moved, with
  this issue's done-when, to [[runtime-fn-arena-lists]]. Filed beside it:
  [[datarepr-guarded-images]] (the form for these laws),
  [[native-arena-cell-codecs]] (other elements, trees) and
  [[native-arena-mmap]].
- 2026-11-02 (later): closed. Getting both tools through `write-elf` met
  the certificate's per-declaration fuel twice: each part's live-out set was
  spelled from the root (now literals read on the fork,
  `emission::live_literals`), and a `Then` join works out liveness over its
  whole sibling, which inside `sort`'s pass was past the fuel. The tools
  now keep fewer words live (no word beside a name's bytes) and read a
  payload's length off the walk instead of back from the cell
  (design note §3, §3.1); the join's cost itself is
  [[native-write-elf-join-liveness]]. Both tools match GNU's on the tests'
  inputs, exhaustion included. What remains of the done-when ("as ordinary
  Heather") is [[runtime-fn-arena-lists]].
- 2026-11-03: 2026-11-03: The builder sort's write-elf gate is killed at the suite's rail on a fresh box; not a regression (identical certificate on master). Filed [[native-sort-gate-rail]].
