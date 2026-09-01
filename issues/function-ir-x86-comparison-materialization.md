---
title: Materialize FunctionIR comparisons from x86 flags
status: closed
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

## Resolution

Implemented canonical no-REX `SETB` and `SETL` over an explicit
`LowByteGpr` carrier containing AL/CL/DL/BL. Encoding and executable decoding
consume exactly `0F 92/9C` plus a register-direct ModRM byte; truncated,
trailing, bad-prefix, and unsafe high-byte forms are rejected. Execution writes
only the architectural low byte and preserves flags, memory, and unrelated
registers. The model proves symbolically, for every pair of 64-bit operands,
that `CMP`'s carry flag is FunctionIR unsigned-less-than and `SF xor OF` is
FunctionIR signed-less-than.

The lowering uses a rule-local flag intermediate and emits three adjacent
instructions: clear a distinct destination with `MOV r64, 0`, `CMP`, then the
appropriate `SETcc`. Clearing first makes the complete destination GPR exactly
the zero-extension of the one-bit FunctionIR result; adjacency prevents an
unproved flag-clobbering schedule. `BitValuePlaced` records this one-bit-to-GPR
representation explicitly. Unsupported temporary pools now return the
structured `NoSafeByteRegister` decline rather than selecting an invalid byte
alias.

This first straight-line allocator accepts a comparison only as the region's
observable result. Keeping a one-bit value live for a later structured
`Conditional` is the next concrete consumer that should generalize the live
placement map; arbitrary one-bit ALU consumption is not silently claimed here.

Both a direct signed comparison and an `ADD` feeding unsigned comparison check
end to end, including canonical block decoding, real lengths, execution,
one-bit refinement, final register movement, memory, RIP, and register frame.
Their warm generated checks took about 20 and 28 seconds respectively.

Concrete closed reduction of the `2^63` boundary still exhausts ordinary
kernel fuel; the symbolic all-operands theorem is stronger and the staged
compiler certificates remain green. That representation/performance flaw is
recorded under [[bitvec-closed-reduction-cost]], not hidden by raising fuel.
