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
