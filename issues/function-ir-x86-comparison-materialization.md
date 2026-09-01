---
title: Materialize FunctionIR comparisons from x86 flags
status: open
labels: [compiler,function-ir,x86,flags,comparisons,proofs]
blocked-by: [function-ir-x86-constants]
created: 2026-09-01
updated: 2026-09-01
---

FunctionIR signed and unsigned less-than consume two BitVec(width) operands and
produce a BitVec(1). The x86 model already gives `CMP` flag semantics, but the
compiler has no representation for a value temporarily living in flags and no
modeled `SETcc`/zero-extension path that turns the predicate into an ordinary
SSA bitvector value.

Add a first proof-producing materialization sequence, likely `CMP` followed by
the appropriate `SETB` or `SETL`, plus an explicit move/zero-extension when the
chosen destination representation requires it. Decide whether flags are an
internal selected-value location, an explicit low-level dependency, or merely
an abstract rule-local intermediate. FunctionIR itself should remain free of
x86 flag identities.

The byte-register model must handle REX restrictions honestly. It is acceptable
for the first selector to use a deliberately small safe register subset, but it
must decline unsupported placements rather than pretend every GPR byte alias
is uniform.

## Acceptance

- Unsigned and signed less-than select distinct, correct x86 conditions.
- Boundary values distinguish signed from unsigned ordering, including the
  high bit and equal operands.
- The materialized result is exactly `BitVec(1)` at FunctionIR semantics, with
  any wider temporary representation related explicitly.
- Encoding, executable decoding, flag consumption, register framing, and real
  instruction lengths check end to end.
- Intervening flag-clobbering instructions cannot be scheduled between compare
  and materialization without an explicit proof/rule permitting it.
- Unsupported byte-register placements produce a structured decline.

## What it assumes from elsewhere

- **[[function-ir-alu-core]]** supplies signed/unsigned comparison semantics.
- **[[function-ir-x86-constants]]** supplies variable-length instruction
  layout and immediate/byte-stream infrastructure.
- **[[x86-64-machine-model]]** supplies CMP and architectural flag semantics.

