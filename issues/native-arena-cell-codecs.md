---
title: Arena cells for lists of any encoded element, and for binary trees
status: open
labels: [native,memory,datarepr]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-02
updated: 2026-11-02
---

`lib/native/native_arena.hthr` represents `List<List<BitVec(8)>>` (a file's
lines): a cell is the next cell's name, the payload's length and the payload
(docs/native-heap-arena-design.md §4). Two generalisations wait on a customer
that holds something else (docs/native-heap-arena-design.md §4.2):

- **Encoded elements.** A list of any `A` with an encoding into bytes whose
  round trip holds (`decode(encode(x) ++ rest) = x`, the shape of
  `read_arena_word`): the same cell with the encoding as payload, the same
  `extend_abs` and `cons_abs`, the round trip in place of `take_whole`.
- **Binary trees.** A node cell with two names and a payload; both children
  are below the node, so the name is fuel enough again, and the laws are
  extension and the node image with two recursive reads.

## Done when

Both have `abs`, `inv` and the extension and image laws proved in
`native_arena`, and a builder tool over each (a word list, a tree) runs.
