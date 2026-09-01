---
title: Grow FunctionIR from Add into a useful fixed-width ALU core
status: open
labels: [compiler,function-ir,semantics,bitvec,x86]
blocked-by: [function-ir-x86-lowering-generator]
created: 2026-08-31
updated: 2026-09-01
---

After the Add-DAG lowering path is executable, extend the official pure
FunctionIR operation family with the smallest set that supports meaningful
straight-line programs: constants, bitwise operations, shifts, and signed or
unsigned comparisons where interpretation changes semantics.

Ordinary addition remains `Add`: signedness belongs to interpreting operations
such as comparison, division, and right shift, not to the BitVec value type.
Each operation must define its signature and graph semantics before gaining a
lowering rule. Use the second operation family to decide how much of the
operation-signature boundary should become generic; do not pre-build a dialect
framework without a concrete consumer.

## Acceptance

- Constants and a representative bitwise, shift, and comparison operation
  validate and denote at more than one width.
- The x86 generator selects and certifies representative mixed-operation DAGs.
- Width and signedness mistakes are rejected by compact validity generation.
- The design records any pressure toward multiple results, immediates, flags,
  or operation-family abstraction rather than hiding it in special cases.

## What it assumes from elsewhere

- **[[function-ir-x86-lowering-generator]]** supplies the executable lowering
  and certificate composition boundary that new operation rules extend.

## Progress, 2026-09-01

The official `Node` family now has fixed-width constants, modular add/subtract,
AND/OR/XOR, three immediate shifts, and signed and unsigned less-than. Compact
validity generation rejects width and comparison-result mistakes, and direct
semantic equations check at both 8 and 64 bits.

The first backend slice generalizes the former Add-only selector to 64-bit
register-register Add/Sub/AND/OR/XOR. A mixed DAG with two simultaneously live
subexpressions is selected, allocated, rendered, decoded by the x86 model, and
kernel-checked against `RegionHolds`. The reusable placement theorem uses
direct equality elimination: spelling the same substitution through generic
congruence and transitivity crossed the existing kernel fuel rail.

The issue remains open for constants/immediate encodings, shifts, and
comparison materialization. Those are intentionally the next slice because
they break the current accidental assumption that every selected instruction
is a three-byte destructive register-register operation.

A 20-node/22-instruction version was also probed. Its generated check had not
finished after five minutes and was removed from the ordinary rail; the
selector itself is instantaneous. [[function-ir-x86-proof-scaling]] owns that
proof-composition wall rather than lowering the intended program-size target.
