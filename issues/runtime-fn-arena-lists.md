---
title: Lists in runtime fns as arena cells, so sort and tac are ordinary Heather
status: open
labels: [native,memory,datarepr,runtime]
area: heather-in-heather
milestone: [nh-heap]
blocked-by: [effects-uniqueness-surface]
created: 2026-11-02
updated: 2026-11-02
---

The front-end half of [[native-heap-arena]] (docs/native-heap-arena-design.md
§7). The back half landed there: an arena is a `Source` buffer and a top word,
running out is a defined exit, and `lib/native/native_arena.hthr` proves the
representation's laws once (`ArenaRef::nil_abs`, `extend_abs`, `cons_abs`).
`tac` and `sort` are written with the builder over it and pass GNU's tests.

## Scope

- `rt::Ty` gains a list-of-byte-strings type laid out as an arena cell name;
  `Ty::Holds` at it says the port holds a name `at` with
  `ArenaRef(arena bytes, at).inv()` and `abs` the value
  (docs/runtime-fn-setups-design.md §8, "N4").
- `Nil` lowers to the name 0 (`nil_abs`), `Cons` to the arena's cell writes
  with the allocation's failure arm an exit (`cons_abs` on the success arm,
  `extend_abs` for every other live list), `match` on a list to a read of the
  cell's header; each a case of `Tm::lower_sound`.
- `foldl` over such a list as a loop (the design note's §7.4 shapes).

## What it assumes from elsewhere

- **[[effects-uniqueness-surface]]** (R6) owns I/O as capabilities and the
  `Source` statements a runtime fn lowers to. Assumed here: that a lowered
  body can exit, which the allocation's failure arm needs.
- **[[native-heap-arena]]** owns the arena and its laws. Assumed here: only the
  three laws' statements.

## Done when

`sort` (lines into a list) and `tac`, written as ordinary Heather marked
`runtime fn`, pass the GNU tests `crates/cli/tests/native_tools.rs` runs on the
builder versions, and the builder versions are deleted.

## Log

- 2026-11-02: First front-end round (docs/native-heap-arena-design.md §7.1). `tac` and `sort` are written as ordinary Heather over `Io` in `lib/native/runtime/line_tools.hthr`, using loops only and no recursion, and the arena stays write-once. `line_tools_tests` checks them against GNU's cases as literals by `refl`, and checks `tac` against its builder source at one line. Larger worlds pass one declaration's kernel fuel when the builder source is evaluated by conversion. `rt` gains `Ty::Lines`, `Op::ConsLine`, `Nil` as `Lit(Lines, 0)`, and `Fold` over any list code (`Ty::elem`/`Ty::items`). The reflector reads them, and each pins by `refl`, with negative controls. Left, in order: `Holds` at `Lines` as an arena name (this needs R6's lowering to `Source`); `ConsLine`'s case of `lower_sound` (`cons_abs`/`extend_abs`, exit when full); list `match`, which the host does not present as a `Case` ([[runtime-reflect-list-match]]); a byte push onto the open line, `for_in` exits, and records with list fields; then `runtime fn` on both tools and the builder versions deleted.
- 2026-11-02: 2026-11-02: Customers moved onto rt_io's word-level calls (`Io::read_into` into a kept buffer, `Io::write_from` of a span; PR #395) so they reflect through ETm once it has loops. A line written from the arena is then a span of the arena buffer, so `Bytes` values must be lowerable as (buffer, offset, length) views, not only as whole buffers. Review follow-ups filed: [[mut-self-early-return]], [[bool-conditions-and-literals]], [[effectful-loops-without-passes]], [[numerals-without-algebra-import]].
