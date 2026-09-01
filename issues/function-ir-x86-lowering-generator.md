---
title: Generate certified x86 lowering for pure FunctionIR Add DAGs
status: closed
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

## Resolution

Implemented on 2026-08-31. The host-side lowering validates the concrete
64-bit, single-output Add DAG, computes use counts, assigns a declared
spill-free temporary pool, reuses a left operand's register after its last
use, and emits `MOV`/destructive `ADD` plus a final requested-output move when
needed. Pressure and malformed placements are structured declines.

The emitted Heather module proves each concrete instruction's result and frame
on an abstract machine state, then composes those local facts into staged
`ValuePlaced` proofs. This shape matters: asking reflexivity to normalize a
whole nested block exhausted ordinary kernel fuel even for sum4. The final
artifact includes canonical bytes/decoding, relational block execution,
FunctionIR refinement, memory and protected-register framing, and RIP advance.

`lib/function_ir_x86.hthr` is now a generated golden containing add64 and the
primary sum4 schedule. Its drift test regenerates from the same ordinary
Region models, while the semantic suite checks the complete module. The
alternate sum4 schedule is generated and checked in an independent module so
the two expensive kernel checks can run concurrently. The handwritten proof
bodies were deleted. A structurally stale model is rejected by conversion;
allocator tests cover temporary pressure, last-use reuse, and a 100-node chain
with constant temporary demand.

The accepted initial limits are explicit: only `Add` at width 64, one result,
no spills, and only left-operand destructive reuse. Reusing the right operand
would need either commutativity in the generated semantic proof or an
instruction-selection rule that carries operand permutation evidence.

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
