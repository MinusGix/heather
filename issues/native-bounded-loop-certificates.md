---
title: Generate native bounded-loop certificates from shared structured selection
status: open
labels: [compiler,x86,proofs]
blocked-by: [function-ir-bounded-readonly-loop, function-ir-recursive-structured-lowering]
created: 2026-09-20
updated: 2026-09-20
---

## Scope

Implement native selection and automatic certificate composition for the
bounded FunctionIR contract owned by [[function-ir-bounded-readonly-loop]].
The output must connect source meaning, physical execution, and published
bytes; a pure loop-model equality plus an encoding equality is insufficient.

## Acceptance

- Use the recursive structured selector's explicit port placements, local
  effects, and intermediate-state interfaces for the loop guard and body.
- Select guarded byte loads, carried-state updates, continue edges, and exits
  through shared machine operations. Access premises occur only on selected
  read paths, with explicit canonical/nonwrapping assumptions where needed.
- Resolve symbolic forward/backward labels and check encoded displacements;
  no per-client numeric-offset or fixed-register proof template.
- Fold the selected structure into small named certificates for initialization,
  guard/body execution, carried bindings, frames, backward edges, and exits.
  Claimed clobbers/placements must be checked against actual instructions.
- Instantiate a reusable bounded induction schema, proving the word/Nat
  counter invariant and a finite complete trace, including exhaustion.
- Package final results, common exit, preserved memory/registers, and exact
  published bytes with source refinement in the stated export boundary.
- Keep ABI adapter, RET, fetch/loading, and host I/O boundaries explicit wherever
  still external. No kernel trust extension or resource-limit increase.
- Use structured emission for new declarations; the proof constructor remains
  untrusted and its output goes through the ordinary elaborator/kernel.
- Reject dishonest guards, access premises, edge targets, carried bindings,
  counter updates, clobbers, exit values, and stale source at local boundaries.

## What it assumes from elsewhere

- [[function-ir-bounded-readonly-loop]] owns source/IR loop semantics. Settle
  that interface before adding native loop machinery.
- [[function-ir-recursive-structured-lowering]] owns recursive branch selection
  and proof composition; this issue extends it with bounded iteration.
- [[x86-symbolic-fragment-layout]] owns symbolic placement/relocation support.
- [[function-ir-x86-join-placement]] owns general join reconciliation; an honest
  initial placement restriction is acceptable and must be documented.
- [[native-shared-lowering-milestone]] owns validation with two independent
  source clients and the prohibition on per-application machine proof families.

## Historical context

The experimental scanner implementation at 4db435c was removed intentionally.
[[x86-buffer-scan-loop-refinement]] records its unfinished proof, not an API to
preserve or a completed correctness result. Recover individual facts from Git
only when the new shared interface needs them.

## Integration boundary

The source/IR contract is now concrete in `function_ir_loop.hthr` (see
`docs/function-ir-readonly-loops.md`). It supplies a typed `ReadonlyLoop<C>`
body reference and one `loop_run` evaluator. This issue must lower that checked
body through shared regions before physical selection; a resolved source name
is not a selected body or a physical certificate. The first source clients
use Nat counting and Bool search carries, byte comparisons, and explicit
input budgets. Counter representability and outcome ABI encoding remain
obligations here; they were not silently fixed by the semantic interface.

## Log

- 2026-09-20: Complete search_body now reflects through shared structured IR and
  receives a kernel-checked source expansion certificate. Added general Compose
  for structured producers feeding continuations, with shared validity/semantic
  contracts; transparent monomorphic Boolean helpers retain inherited inputs and
  computed scalar arguments. Generic two-constructor results use ordinary payload
  and discriminator ports, with nominal constructors restored at the source edge.
  The unused Nat cursor remains in the source theorem without a machine port;
  consumed Nat values still decline. An unrelated BitVec-carrying choice exercises
  the same implementation. Controls reject stale helper meaning, swapped result
  constructors, wrong discriminator/payload, unavailable bindings, and excessive
  helper depth. All ten focused tests pass. Plain scripts/test passes 2850 tests,
  0 failed, 5 ignored; diff and issue consistency checks pass. Physical
  Compose selection explicitly declines. Native multi-result/body execution,
  guarded reads, Nat representation, symbolic edges, and bounded traces remain.
- 2026-09-20: Started the shared-body prerequisite by generalizing the existing structured
  source reflector and IR-based source expansion renderer. Typed parameter lists
  now admit Bool and literal BitVec widths 0–64, with matching operation widths,
  Boolean guards/results, passthrough leaves, and retained local DAG sharing.
  Bool and BitVec(1) remain distinct at the source boundary; recognition uses
  resolved type/operation identities, including nominal Boolean payload codes.
  The loop clients' byte_equal helper now uses the ordinary StructuredRegion/Node
  path and a checked source certificate. No loop-specific predicate AST, node,
  or native profile was added. The native export adapter explicitly retains its
  two-word interface. Focused tests passed seven groups, including prior recursive
  selection/source agreements and the new typed/helper controls. Full validation
  is running. Whole LoopStep bodies, helper-call composition, Nat representation,
  physical byte/bit selection, symbolic edges, and complete loop traces remain;
  this is a bounded frontend checkpoint, not a completed native-loop issue.
- 2026-09-20: Shared typed frontend checkpoint validated: plain scripts/test passed 2847 tests,
  0 failed, 5 ignored, including the existing recursive physical certificates and
  native assembly execution regressions. No resource limits changed. Diff and
  issue consistency checks pass. This checkpoint is complete; the broader native
  loop acceptance remains open with the outstanding boundaries recorded above.
- 2026-09-20: Physical composition and explicit multi-result placement now use shared recursive
  selection and certificate emission under [[function-ir-recursive-structured-lowering]].
  Composed prefixes carry multiple outputs plus inherited inputs by port ID;
  branches share per-port result destinations, and each result is proved over the
  same physical execution. Conditional helpers also reach ordinary scalar native
  export. Multi-result DAG slices can recompute shared work; the optimization is
  tracked in [[function-ir-shared-multi-result-dag]]. Byte/Boolean leaf operations,
  guarded reads, Nat representation, symbolic edges, and bounded traces remain.
  Validation is in progress.
- 2026-09-20: Physical composition/multiple-result placement checkpoint is complete and
  [[function-ir-recursive-structured-lowering]] is closed. Plain scripts/test:
  2854 passed, 0 failed, 5 ignored, including the new composed-helper native
  export on 10,036 input pairs and multi-result kernel certificate controls.
  The loop body's byte/Boolean dataflow selection, guarded loads, and complete
  bounded trace remain open; no native search_body certificate is claimed.
- 2026-09-20: The next shared-body checkpoint adds explicit zero-extended placements for
  widths 0–64, normalized constants/copies, narrow bitwise operations, and unsigned
  comparisons. Generic bitvector zero-extension laws support the proof generator;
  there is no byte_equal or search-specific machine rule. The complete search_body
  is the source-driven physical-certificate customer, including its Boolean carry
  and payload/discriminator outputs. Narrow add/subtract and signed comparisons
  remain explicit refusals, tracked in [[function-ir-narrow-arithmetic]]. Validation
  is in progress. Typed source publication, guarded loads, and bounded traces
  remain separate from this body-certificate checkpoint.
- 2026-09-20: Focused validation passes: 16 tests, including the complete reflected search_body
  with kernel-checked physical payload/discriminator results and checked source
  expansion. Independent selected-instruction execution covers every byte value,
  five boundary needles, and both Boolean carry values (2,560 cases). Narrow
  constant normalization, zero-width policy, copies, byte bitwise operations
  including right-operand register reuse, unsigned comparison, and incorrect
  word-placement/signed-comparison controls are covered. Plain full scripts/test
  is now running.
- 2026-09-20: Shared narrow-value/body-certificate checkpoint validated: plain scripts/test
  passed 2858 tests, 0 failed, 5 ignored. This includes kernel-checked search_body
  payload/discriminator certificates, source expansion, negative placement and
  signed-comparison controls, 2,560 independent execution cases, and existing
  native regressions. The checked-in generated x86 example matches the emitter.
  No resource limits changed. Typed source-to-machine publication, guarded reads,
  and complete bounded-loop traces remain open; this completes the body checkpoint.
