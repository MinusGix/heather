---
title: Buffers as FunctionIR values on state edges, with uniqueness checked by the lowering
status: open
labels: [native,ir,proofs,memory]
area: heather-in-heather
milestone: [hih-pl-source, hih-memory-model]
blocked-by: [byte-memory-access-model, wp-proved-memory-contracts]
created: 2026-10-21
updated: 2026-10-21
---

Internal effects belong in FunctionIR as state edges, never as tree events
(`docs/native-program-logic-design.md` §10 item 6;
`docs/native-effect-source-design.md` §6). A buffer is a value of type
`Bytes(capacity)`, which is what a uniqueness-threaded `uniq Buf` denotes.
`Load(buf, index) → byte` and `Store(buf, index, byte) → buf'` are nodes. A
Linux read's answer fills a buffer value, and a write's argument reads one.

## Scope

- Port kinds for buffers beside `BitVec` widths; the nodes and their
  equations; `eval` over them ([[function-ir-total-evaluator]]).
- The lowering's abstract file says which buffer value each memory range
  holds. A `Store` updates the range in place to hold `buf'`, so a later use
  of `buf` fails the lookup and `lower` refuses. Uniqueness is then checked
  by evaluation, and the theorem stays "whenever `lower` returns code".
- The lowered region's contract names the buffer's range as its footprint
  ([[wp-proved-memory-contracts]]), related to the value by a view.
- `tr`'s byte map (a bounded loop over a buffer) as the example.

## What it assumes from elsewhere

- **[[byte-memory-access-model]]** owns reads and writes with outcomes and
  the view over a range.
- **[[function-ir-verified-lowering]]** owns the lowering and its file.
- **[[function-ir-lowering-loops]]** owns the bounded loop.
