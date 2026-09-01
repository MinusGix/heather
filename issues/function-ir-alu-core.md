---
title: Grow FunctionIR from Add into a useful fixed-width ALU core
status: open
labels: [compiler,function-ir,semantics,bitvec,x86]
blocked-by: [function-ir-x86-lowering-generator]
created: 2026-08-31
updated: 2026-08-31
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

