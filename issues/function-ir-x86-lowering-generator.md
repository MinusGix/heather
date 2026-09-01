---
title: Generate certified x86 lowering for pure FunctionIR Add DAGs
status: open
labels: [compiler,function-ir,x86,proofs,codegen]
created: 2026-08-31
updated: 2026-08-31
---

FunctionIR validity certificates are generated and scale to ordinary compiler
graphs, but instruction selection, placement, execution proofs, and framing in
`function_ir_x86.hthr` are still handwritten for add64 and sum4. The next
compiler-shaped slice should accept a concrete valid pure Add DAG and produce
both its x86 block and an ordinary kernel-checked refinement certificate.

The initial implementation may be spill-free. It should still be an actual
lowering rather than a per-fixture renderer:

- map function inputs to declared ABI/input locations;
- compute use counts or liveness sufficient to reuse temporary GPRs;
- account for x86's destructive two-operand `ADD`, inserting `MOV` when the
  selected destination does not already contain an operand;
- keep instruction selection and location assignment distinct internal
  phases even if one public generator runs both;
- emit canonical instructions/bytes plus staged facts for result placement,
  allowed execution, memory and protected-register framing, and RIP advance;
  and
- decline unsupported pressure, spills, operations, or placements precisely.

The generator is untrusted. Its output is Heather source checked against the
actual FunctionIR graph and x86 semantics. A stale graph, placement, or
instruction list must fail at the ordinary elaborator/kernel boundary.

## Acceptance

- Generated add64 and both sum4 schedules check end to end.
- At least one graph requires a temporary register and one graph exercises
  register reuse after a value's last use.
- A dishonest-model control is rejected by conversion or the refinement
  theorem's premises.
- Unsupported register pressure produces a structured decline rather than a
  panic or guessed artifact.
- Once generated artifacts cover their contracts, the handwritten add64 and
  sum4 x86 proof bodies are deleted rather than retained as a parallel path.
- The interface leaves room for spills without designing the final allocator.

## What it assumes from elsewhere

- **[[function-ir-validity-v2-adoption]]** supplies the sole compact validity
  boundary and staged certificate-emission pattern.
- **[[x86-64-machine-model]]** owns the target semantics. This issue consumes
  the existing canonical block and execution interfaces without broadening
  the machine model unnecessarily.

## Follow-on path

- **[[function-ir-alu-core]]** extends the operation and lowering rule family.
- **[[source-to-function-ir-certification]]** composes a source frontend with
  this backend.
- **[[function-ir-conditional-regions]]** is the first structured-control
  customer after the straight-line core.
