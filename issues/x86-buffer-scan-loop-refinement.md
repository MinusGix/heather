---
title: Connect bounded scanner certificates to a complete machine-loop trace
status: open
labels: [compiler,x86,parsing,proofs]
created: 2026-09-20
updated: 2026-09-20
---

## Scope

The experimental `compile-x86 --buffer-scan` export compiles ordinary Heather
scanner bodies and emits a shared bounded native loop. Its certificate proves
body/source agreement for arbitrary machine states, preservation of the loop's
live registers and memory, lifting into the pure bounded scanner model, and
exact encoded bytes. These facts do **not** yet prove that the complete native
loop executes that pure scanner model. The command and documentation must keep
this limitation visible until this issue is closed.

## Acceptance

- Model the guarded R8+R10 MOVZX load with explicit readable, canonical,
  nonwrapping address premises, and prove the load is selected only after the
  cursor/length and fuel checks.
- Compose body block traces, actual branch RIP changes, state preservation,
  cursor increments, and fuel decrements into a finite machine-loop trace.
- Connect the concrete 256-word fuel counter to the abstract Nat fuel without
  assuming the very termination/correctness property being proved.
- Certify final value, cursor, status, untouched input memory, preserved ABI
  registers, and the common return address for every exit.
- Reject mutations of the guard, load permission, backward edge, live-state
  restoration, fuel update, and exit result under normal proof/process limits.
- Retain the external host ABI adapter, RET, fetch, linker and I/O boundaries
  explicitly; do not imply a loaded-memory trace from an encoding equality.

## Context

- [[x86-buffer-decimal-parser]] owns the decimal milestone and its remaining
  natural-number interpretation theorem.
- [[x86-buffer-cursor-recognizer]] supplies the prior single-byte load model.

## Log

- 2026-09-20: The experimental export's final full suite passed 2834 tests, 0 failed, 5 ignored. The current certificate includes a generic body frame protecting loop state and input memory, with frame checks emitted before source-result checks. Runtime guard-page, resource-bound, and mutation checks pass. These facts remain prerequisites for this issue, not a substitute for its complete machine-loop execution theorem.
- 2026-09-20: Added a checked physical loop-head traversal: bounds CMP/JAE, fuel MOV/CMP/JE, and MOVZX RDI,[R8+R10]. The load requires readable, low-canonical, nonwrapping address premises only on the selected byte-ready path. Early exits require no byte permission. Generated certificates include preserved loop/memory/ABI state and concrete end/limit/body-entry RIP proofs. Initialization, structured body machine traces, backward-edge composition, the word/Nat fuel invariant, and final-result/return composition remain open; the experimental warning stays. Added independent guard, permission, read-address, and RIP refusal controls; validation pending.
- 2026-09-20: The generic guard model checks under normal limits, including lemmas identifying the machine carry flag with cursor < length and the zero flag with a zero fuel word. The initial wrong-RIP control exhausted conversion fuel when comparing unequal nested symbolic increments; its accepted theorem remains general, while the refusal now fixes only the code base and leaves memory/data registers open. No proof or process limits were raised.
- 2026-09-20: The independent guarded-entry permission/path acceptance test passed. It accepts both no-read exits and the permitted open-memory load, and semantically rejects missing readability/canonical/nonwrapping premises, inverted guard conditions, and a wrong byte address. The full suite is rerunning after correcting a missing block-model import in the concrete RIP test fixture.
- 2026-09-20: Validation also prompted [[native-fixture-namespace-isolation]]: shared and direct native test artifacts now have per-run nonces to avoid process-ID reuse across sandbox namespaces. The scanner permission/path test passes independently; final plain-suite validation is still in progress.
- 2026-09-20: Both scanner acceptance tests passed in the full run: runtime/oracle/protected-page checks, generated certificates, concrete wrong-RIP refusal, and independent permission/path refusals. That suite had one unrelated fixture-directory collision (tracked separately); the final plain suite includes its fix. Full-loop composition and natural-number decimal interpretation remain open.
- 2026-09-20: Final plain scripts/test passed: 2835 passed, 0 failed, 5 ignored, including both scanner acceptance tests. Heather formatting, diff whitespace checks, and the issue tracker check are clean. Guarded physical entry is established; complete repeated-loop composition and its Nat-fuel invariant remain open. Reported target CPU includes descendants and is not a single process's CPU-rail usage.
