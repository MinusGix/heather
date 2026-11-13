---
title: Lower byte nodes in S4 with registers held across them, a buffer footprint, and checked uniqueness
status: open
labels: [native,ir,proofs,memory]
area: heather-in-heather
milestone: [hih-pl-source, hih-memory-model]
blocked-by: [wp-proved-memory-contracts]
created: 2026-10-21
updated: 2026-11-11
---

Internal effects belong in FunctionIR as state edges, never as tree events
(`docs/native-program-logic-design.md` §10 item 6;
`docs/native-effect-source-design.md` §6). The nodes exist:
[[native-source-bytes]] built `BufferLoad`/`BufferStore` and
`StructuredRegion::run` beside `eval`, and [[native-compile-wider-leaves]]
compiles a leaf that mixes them with pure nodes node by node,
memory-resident. S4's `Region::lower` still refuses them, so a byte node
costs a slot round trip on every operand, and nothing checks that a stored
buffer's old value is never used again.

## Scope

- S4's register lowering of `BufferLoad`/`BufferStore`, with the values
  around them held in registers across the access.
- The lowering's abstract file says which buffer value each memory range
  holds. A store updates the range in place to hold the new buffer, so a
  later use of the old one fails the lookup and `lower` refuses. Uniqueness
  is then checked by evaluation, and the theorem stays "whenever `lower`
  returns code".
- The lowered region's contract names the buffer's range as its footprint
  ([[wp-proved-memory-contracts]]), related to the value by
  `DataRegion::buffer_view`.

## What it assumes from elsewhere

- **[[memory-model-machine-instances]]** owns `DataRegion::buffer_view`
  (built on [[byte-memory-access-model]], closed).
- **[[function-ir-verified-lowering]]** owns the lowering and its file.
- **[[function-ir-lowering-loops]]** owns the bounded loop.

## Log

- 2026-10-22: The buffer view these edges need exists: `DataRegion::buffer_view` (`lib/std/os/linux/linux_x86_64_byte_memory.hthr`, [[memory-model-machine-instances]]) relates a buffer's cells to a data region of an `X86Profile`, loads and stores at a named index, sound against the profile's `LinuxIo`.
- 2026-10-26: [[native-source-bytes]] (round 1 of `docs/native-real-programs-plan.md`) builds this issue's nodes and `eval` first, compiled memory-resident by the statement compiler under S3.2's `Target::Placed`. That needs no `Proved` footprint, so its blocked-by on [[wp-proved-memory-contracts]] does not apply to it. What stays here is S4's register lowering of the nodes, with its footprint.
- 2026-10-26: [[native-source-bytes]] built the nodes (`BufferLoad`/`BufferStore`), `StructuredRegion::run` beside `eval` (`run_empty` ties them) and the memory-resident compile of single-byte-node leaves. S4's `Region::lower` refuses the nodes. What stays here: lowering byte nodes in S4 with registers held across them, with the footprint, and uniqueness-checked buffer values.
- 2026-10-28: Re-scoped (tracker tidy): the nodes, `run` and the memory-resident compile landed in [[native-source-bytes]] and [[native-compile-wider-leaves]], and `tr a-z A-Z` is built (its byte map as a bounded FunctionIR loop stays with [[native-compile-wider-leaves]]), so the title and scope now name only S4's register lowering of the nodes, the footprint and the uniqueness check. Dropped [[byte-memory-access-model]] from `blocked-by` (closed); [[wp-proved-memory-contracts]] stays, since the footprint needs it.
- 2026-11-11: The function compiler reads buffers (U3a of [[native-one-compiler]], `function_ir_lower_reads.hthr`): `BufferLoad` under a path-known comparison, through a home that is two values of the scope, with `Stack::Lends` as the footprint's premise. Stores are U4. Limits kept from that round: (1) a loop inside a loop that carries a home is refused, since the outer pass must hand on the parameter itself and after the inner loop the home is the inner loop's outputs; the general check is "what the pass hands on is a home of the same buffer at the body's end" (`StructuredRegion::lends` of the body), which needs the pass's meaning in `loop_carries`. (2) The bound must be the comparison folded at the branch that guards the load, read through the file's knowledge at the load; a bound established earlier on the path and kept as a fact about values (rather than about flags) is the generalisation. (3) Buffers are the program's by number, so a function reads the same buffers whoever calls it: views ([[source-buffers-as-views]]) are a renaming at the call.
