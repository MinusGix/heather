---
title: Relate linked x86 conditional execution to its abstract FunctionIR block
status: open
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

## Direction

- Define an instruction/block effect summary stating which state components a
  leaf reads and writes; the first useful class is GPR ALU code independent of
  incoming flags, RIP, and memory.
- Prove execution congruence under equality of the components actually read.
- Use TEST/JZ/JMP frame facts to establish that congruence at both leaf entries
  and that the unconditional jump preserves the yielded GPR result.
- Compose the resulting linked-to-abstract observation theorem with the
  existing abstract FunctionIR refinement.
- Separately connect signed rel8 distance facts to bitvector RIP equality and
  prove both paths finish at `linked_join_start`.

## Acceptance

- Both selector values execute the intended leaf and produce the FunctionIR
  output in the declared result register.
- Both paths reach the same proved physical join RIP.
- GPR and memory frame claims are explicit; undefined TEST AF does not affect
  branch selection or result correctness.
- The proof checks under ordinary fuel and scales with named block facts rather
  than expanding the complete linked artifact in one motive.
