---
title: Export and consume reusable summaries for composed source callers
status: closed
labels: [compiler,x86,proofs]
created: 2026-09-19
updated: 2026-09-19
---

## Scope

Make a bounded composed source function usable through a reusable native call
summary. The first customer is the executable's entry calling a composed
function which itself calls one explicitly selected arithmetic leaf.

## Acceptance

- Export a checked summary for arbitrary input words, initial register values,
  flags, and stack memory in a stated bounded stack/placement profile.
- Compose the child leaf's checked source/ABI summary; do not replay a
  concrete-input source proof as a supposedly generic caller contract.
- Preserve RBX/RBP/R12–R15, restore RSP, return to the original return address,
  and describe the allowed child-call return-slot writes.
- Have the outer entry consume the composed summary with actual fetched-byte
  and access premises, and connect its result to the Linux exit request.
- Reject stale code/source contracts and missing preservation or stack facts.
- Keep the existing source-call examples and pass the plain full test suite.

## What it assumes from elsewhere

- [[x86-source-call-composition]] supplies the bounded source expression plan.
- [[x86-reusable-callee-certificates]] supplies leaf summaries and checked use.
- [[x86-call-memory-footprints]] owns broader frame allocation and aliasing.

General recursive call graphs, spill allocation, and stack relocation are
separate follow-up scope. The first strategy may reserve a restricted scratch
register set in the leaf to keep composed-function temporaries out of native
callee-saved registers.

## Log

- 2026-09-19: Implemented the opt-in --callable-caller profile. The generic summary quantifies over initial registers, flags, RIP, and memory with an explicit fixed-RSP entry template; it consumes the leaf contract, preserves the native ABI registers, restores RSP, and protects the parent return word through a child-return-slot footprint. The executable entry consumes that summary for both execution and source-result evidence. Focused neutral-state/refusal checks and ordinary/wrapping executable cases pass. Full-suite validation is running.

  Follow-ups: [[x86-caller-value-sharing]] owns repeated let-value computation; [[x86-composed-caller-register-saves]] owns larger leaf scratch demands; [[x86-composed-summary-refusal-fuel]] owns the whole-stream mutant's fuel-exhaustion diagnostic. General stack relocation and deeper call graphs remain with [[x86-calls-stack-frames]] and [[x86-call-memory-footprints]].
- 2026-09-19: Final plain scripts/test passed: 2826 passed, 0 failed, 5 ignored. The new native_callable target checked and executed both ordinary and full-width wrapping inputs; the neutral-state summary, stale-interface, missing-entry, ABI-clobber, and RAX-only pressure controls passed. All existing native and scaling gates passed under unchanged budgets. No kernel or proof-library changes were needed. The bounded milestone is complete; broader register saves, frame relocation, call graphs, and diagnostic work retain the owners linked above.
- 2026-09-19: Follow-up work now shares caller values ([[x86-caller-value-sharing]]), allocates around actual leaf clobbers ([[x86-composed-caller-register-saves]]), and checks instruction/child-span boundaries before summary conversion ([[x86-composed-summary-refusal-fuel]]). Save/restore frames remain with their existing owner.
