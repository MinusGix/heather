---
title: Link structured conditional blocks to canonical x86 branch bytes
status: open
labels: [x86,compiler,encoding,control-flow,linker]
blocked-by: [function-ir-conditional-regions]
created: 2026-09-01
updated: 2026-09-01
---

`ConditionalBlock` now gives FunctionIR a checked state-dependent machine CFG:
it reads a materialized condition register, executes exactly one canonical leaf
block, and joins the result. Each leaf already has checked bytes and decoding.
The remaining physical-code boundary is to lay those leaves out and encode the
actual conditional and unconditional transfers between them.

## Acceptance

- Model the required `Jcc` and `Jmp` subset with exact canonical encodings and
  executable decoding.
- Calculate signed relative displacements from proved instruction and block
  lengths rather than accepting opaque target addresses.
- Make fallthrough choice explicit and prove both taken and untaken RIPs reach
  their declared successor blocks and common join.
- Link a generated FunctionIR conditional into one byte sequence whose decode,
  control-flow execution, result, memory frame, and final join are checked.
- Reject out-of-range short branches or deliberately select a near encoding;
  do not silently truncate a displacement.

## Progress (2026-09-01)

The first concrete rel8 layout is implemented. It has exact `JZ`/`JMP` bytes,
strict executable decoding, signed target semantics, calculated +8/+6
displacements for the current Add/Sub example, a 35-byte linked sequence,
checked per-component decoding, forward-distance/no-truncation layout facts,
canonical control execution, and generator rejection above `i8::MAX`.

The issue remains open because the final two acceptance obligations are not
yet discharged: both path RIPs must be equated to the declared physical join,
and the linked execution result must be related to the already-proved abstract
FunctionIR conditional. The focused proof design is tracked separately in
[[x86-64-linked-conditional-refinement]].
