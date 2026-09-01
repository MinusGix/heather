---
title: Reuse either operand for commutative FunctionIR x86 operations
status: closed
labels: [compiler,function-ir,x86,optimization,register-allocation]
created: 2026-09-01
updated: 2026-09-01
---

The spill-free FunctionIR x86 allocator currently treats every binary node as
left-destructive. It reuses the left register when that value dies, otherwise
copies the left operand into a temporary—even when Add, AND, OR, or XOR has a
dying right operand already sitting in a reusable temporary.

Teach selection to consider both operand orientations for commutative
operations. The selected plan must record the orientation explicitly so proof
emission relates the actual machine operands to the original FunctionIR node;
the generator remains untrusted and cannot silently appeal to host knowledge
of commutativity. Subtraction remains ordered.

This is deliberately not a general scheduler or allocator rewrite. It is the
smallest optimization that makes selected code sensitive to semantic operation
properties and tests whether those properties belong on `BinaryOperation`, on
selection rules, or in a separate proof-producing rewrite layer.

## Acceptance

- Add/AND/OR/XOR reuse a dying right operand when doing so avoids a move or
  prevents otherwise-declined temporary pressure.
- Sub never reverses its operands.
- The emitted refinement proof checks against the original, unpermuted
  FunctionIR equation.
- A mixed DAG demonstrates fewer instructions or lower temporary demand than
  the left-only selector.
- Deterministic tie-breaking keeps generated golden output stable.

## What it assumes from elsewhere

- **[[function-ir-x86-lowering-generator]]** supplies liveness, placement, and
  untrusted proof emission.
- **[[function-ir-alu-core]]** supplies the commutative and ordered operations.

## Progress, 2026-09-01

The selected plan now records original versus reversed operand orientation.
AND/OR/XOR can reuse a dying right-hand temporary, and generated proof emission
kernel-checks an explicit graph-equation swap before applying the ordinary
machine-order placement theorem. Sub remains ordered, and deterministic choice
prefers the requested output register when both operands are reusable.

The checked library gained structural `band_comm`, `bor_comm`, and `bxor_comm`
laws. [[bitvec-add-commutativity]] now supplies the corresponding checked
arithmetic theorem, so Add follows the same explicit proof-producing reversal
path. Unit controls cover all four commutative operations and ordered Sub; the
generated one-temporary Add DAG kernel-checks end to end.
