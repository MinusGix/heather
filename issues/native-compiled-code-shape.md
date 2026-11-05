---
title: Keep words in registers across statements, and copy a read word-wise
status: open
labels: [native,x86,perf]
area: heather-in-heather
created: 2026-10-25
updated: 2026-10-30
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

## Log

- 2026-10-28: Keeping words in registers makes the correspondence depend on the program point. Abate et al. (docs/wp-preserving-compilation-survey.md §4) name the same need for register allocation as future work, with a location map per point and a value relation. Target::Placed would grow a per-point register map; Keeps already reads words through a value relation (word_in).
- 2026-10-28: Words in registers landed as [[native-register-allocation]] (`docs/native-register-allocation-design.md`): one home per word for the whole program, checked by evaluation, with no per-point map; `Target::Held` is `Placed` plus `Homes::Agrees` over the live words. What remains here is the word-wise copy and the unmasked branch test. Per-point homes and moves are [[native-register-moves-and-convention]].
- 2026-10-30: A constraint on any optimisation that drops stores: if secret erasure is ever built, the scrub stores at a cut are required by the compiler's theorem, so they must not be removed ([[native-secret-erasure]], `docs/zeroization-survey.md` §5).
- 2026-11-05: gardener: cites a file it shares with [[native-compile-stat]] (`lib/native/native_compile.hthr`); [[native-constant-time]] (`docs/zeroization-survey.md`); [[native-homes-read-in-place]] (`lib/native/native_compile.hthr`).
