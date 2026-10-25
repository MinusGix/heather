---
title: Keep words in registers across statements, and copy a read word-wise
status: open
labels: [native,x86,perf]
area: heather-in-heather
created: 2026-10-25
updated: 2026-10-25
---

The compiler of S3.2 (`lib/native/native_compile.hthr`,
[[native-effect-source-compiler]]) chose the simplest invariant to prove:
the environment lives wholly in memory, so every statement loads what it
reads and stores what it writes, through RBX as the slot's address. A read
lands in a scratch range and is copied into its buffer a byte at a time,
because Linux may write the range on a failed read (`LinuxLeaves`) and the
source says the buffer is then unchanged. Both cost code size and time, not
soundness. Found while proving S3.2 (2026-10-25).

## Scope

- A placement that keeps chosen words in registers between statements, with
  `Target::Placed` grown to say which registers hold which words; an input
  to the compiler outside the proof, as S4's placement is.
- The copy: a word at a time while eight bytes remain, or a read straight
  into the buffer where the program never reads the buffer after a failure
  (a source-side fact, so a refinement of `CallShape::answer`).
- Branch tests that jump on the slot's byte without masking it into RAX.
