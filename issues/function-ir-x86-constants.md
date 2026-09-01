---
title: Lower FunctionIR constants and generalize x86 instruction layout
status: closed
labels: [compiler,function-ir,x86,encoding,codegen,proofs]
created: 2026-09-01
updated: 2026-09-01
---

FunctionIR already validates and denotes `Const(width, output, value)`, but the
executable x86 lowering accepts only 64-bit register-register binary nodes.
Add the first constant selection rule, initially `MOV r64, imm64`, and use it
to remove the backend's accidental assumption that every selected instruction
is a three-byte RR form.

The target model needs a typed immediate instruction, canonical encoding,
executable decoding, decoded length, and execution semantics. Block layout,
byte-length theorems, RIP staging, and generated proof states must derive their
offsets from each selected instruction's actual canonical length. Do not hide
the transition behind another special-case `instruction_count * 3` formula.

The FunctionIR constant stores a mathematical Nat interpreted modulo the
declared bit width. The lowering must state precisely which immediate encoding
is chosen and must not confuse x86 sign-extension rules for shorter immediate
forms with FunctionIR semantics. Smaller encodings may be a later selection
optimization; the first rule should be obviously total for every BitVec(64)
constant.

## Acceptance

- A FunctionIR `Const(64, ...)` reaches a decoded and executed canonical
  `MOV r64, imm64` whose destination contains `ofNat(64, value)`.
- A mixed constant/binary DAG is selected, allocated, and kernel-checked end
  to end.
- Canonical instruction and block lengths are derived per instruction; a
  mixed block advances RIP by its real encoded byte length.
- Boundary constants cover zero, the signed-immediate boundary, the high bit,
  and `2^64 - 1` without unary-Nat expansion or host truncation bugs.
- Malformed/truncated immediate byte streams and dishonest length facts are
  rejected.
- The design records where later immediate ALU forms plug in without requiring
  them in this slice.

## What it assumes from elsewhere

- **[[function-ir-alu-core]]** supplies constant validity and semantics.
- **[[x86-direct-bitfield-decoder]]** supplies the executable decoder shape to
  extend with immediate bytes.
- **[[function-ir-x86-proof-scaling]]** supplies persistent instruction/proof
  staging that must survive variable lengths.

## Resolution

Implemented a total first constant-selection rule using canonical
`MOV r64, imm64`. The x86 model now exposes uniform `canonical_length` and
`decoded_canonical` operations, reconstructs the immediate from exactly eight
little-endian bytes, rejects malformed/truncated/trailing encodings, and gives
the instruction its exact register-write, frame, and ten-byte RIP semantics.
Canonical block decoding and execution now fold each instruction's real length
rather than assuming three-byte RR instructions.

The FunctionIR backend selects constants into a free register, emits their
full modulo-`2^64` immediate, and uses summed canonical lengths for byte and RIP
proofs. An end-to-end `Const(2^63) + input` certificate checks a mixed
ten-byte/three-byte block, its 13 canonical bytes, staged execution, result,
memory frame, protected registers, and RIP. Focused model controls cover low
and extended destination registers, zero and all-ones immediates, and rejected
bad REX/opcode, truncated, and trailing streams.

The first mixed certificate took about 121 seconds on the development host.
That is correct and bounded, but records useful motivation for the separate
proof-scaling work; it is not hidden by a fuel increase.
