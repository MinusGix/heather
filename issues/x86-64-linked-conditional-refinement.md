---
title: Relate linked x86 conditional execution to its abstract FunctionIR block
status: closed
labels: [x86,compiler,function-ir,proof,control-flow]
blocked-by: [x86-64-conditional-branch-layout]
created: 2026-09-01
updated: 2026-09-01
---

The concrete linked conditional now decodes and executes, while the older
`PrefixedConditionalBlock` already refines the structured FunctionIR region.
Connect those artifacts without relying on whole-term conversion.

The important mismatch is real machine framing, not branch semantics. The
linked path executes `TEST` and a control transfer before its Add/Sub leaf, so
its entry state has different flags and RIP from the abstract leaf entry while
retaining the same GPRs and memory. Direct generated proofs either exhausted
kernel fuel or exposed this non-definitional state equality.

## Progress (2026-09-01)

The result-refinement half is complete. `GprOnlyStep` gives Mov/constant/ALU
instructions a small certificate that their GPR effect ignores incoming flags,
RIP, and memory. The generator composes those certificates over each concrete
leaf, TEST/JZ/JMP frame facts transport the common input GPR file, and
`linked_conditional_read_agrees` relates the machine selector to the FunctionIR
Boolean. The emitted `*_linked_refines_function_ir` theorem now proves the
actual linked machine result.

This representation was chosen after measuring and rejecting a generic
instruction case split in the base x86 module: that version raised the x86
rail from about 29 seconds to 80–90 seconds. Per-step certificates keep the
base rail near 29 seconds and the focused linked artifact near its previous
166 seconds.

The physical join-RIP theorem is complete as well. Layout positions are defined
by encoded byte spans, exact branch targets are certified alongside the rel8
distance facts, and generated named endpoint theorems connect real execution
to those positions. The small `selected_rip_reaches` theorem performs the only
Boolean choice; the emitted `*_linked_reaches_join` theorem proves either path
ends at the common join.

## Acceptance

- [x] Both paths reach the same proved physical join RIP.
