---
title: Keep stale composed-code refusals local under default fuel
status: closed
labels: [compiler,x86,proofs,performance]
created: 2026-09-19
updated: 2026-09-19
---

## Finding

While validating [[x86-composed-caller-summary]], changing only the composed
summary's declared code from `MovRR(Rcx, Rdi)` to `MovRR(Rbx, Rdi)` was rejected
at the final `probe_composed_summary` declaration with kernel `OutOfFuel`.
The honest neutral-state summary checks under the same committed budgets.
The mutant leaves the independently generated states and all proposed facts
unchanged, so the final whole-stream comparison must discover their mismatch.

The permanent local mutation control instead corrupts that canonical step's
state definition and requires a type mismatch at its register-evidence boundary.
Stale summary interfaces are separately rejected by type mismatch. This issue
owns the diagnostic/cost of the whole-stream mutation, not a soundness gap:
no certificate or executable was accepted for the altered code.

## Acceptance

- Attribute the first divergent instruction without normalizing the entire
  composed execution through the final summary/postcondition conversion.
- Retain exact instruction-list indexing and normal kernel checking.
- Exercise an altered instruction in the declared composed code while its
  generated states/proofs remain stale; refuse it locally under default fuel.
- Keep the honest arbitrary-input/neutral-memory summary and native examples
  within their existing resource limits. Do not raise fuel to hide this case.

## What it assumes from elsewhere

- [[x86-composed-caller-summary]] supplies the generated stream, state facts,
  and final reusable summary.
- [[function-ir-x86-proof-scaling]] owns the separate FunctionIR scaling rail.

## Log

- 2026-09-19: Added checked instruction-index boundaries on suffixes of the declared composed code, including its exact end. The original declared-code mutant now fails with NotConvertible at probe_composed_instruction_2 under unchanged default fuel, before generic state/postcondition conversion. The independent canonical-state mutant remains covered.

  Also check each executed child span directly against the code indexed by its leaf summary. An inserted, unreported R8 clobber then fails at that code boundary rather than exhausting fuel while comparing accumulated state projections. Honest neutral-state summaries for ordinary, shared-value, and multi-register fixtures pass the focused tests. This establishes local refusal behavior; no timing improvement is claimed.
- 2026-09-19: Final plain scripts/test passed: 2830 passed, 0 failed, 5 ignored. Local declared-instruction and child-span refusals, honest neutral-state summaries, and native examples all passed with unchanged budgets. Closed.
- 2026-09-19: The checked-save work adds named canonical instruction equalities before constructing symbolic states, so wrong save/restore operands are refused before whole-memory conversion. Tests and implementation details are owned by [[x86-composed-caller-register-saves]].
