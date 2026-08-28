---
title: Make proof-producing x86 opcode dispatch scale sublinearly in declarations
status: open
labels: [x86,performance,proofs]
created: 2026-08-28
updated: 2026-08-28
---

The direct decoder currently recognizes supported opcodes through a linear
chain of evidence-producing byte equalities. Completeness is factored through
one generic operand theorem, but each opcode specialization still normalizes
the preceding dispatch chain while its declaration is checked.

With the original five opcodes and no general completeness layer, the x86
module checked in about 15 seconds on the debug test path. After adding the
constructive completeness layer and four `SUB`/`CMP` opcodes, it checks in
about 42 seconds; the focused consumer is about 52 seconds. These figures mix
both changes and are diagnostic measurements, not benchmark thresholds.

## Acceptance

- Separate opcode classification from operand decoding with a finite opcode
  descriptor or another proof-producing dispatch shape that does not replay a
  growing prefix for each completeness specialization.
- Preserve `ByteDecode` soundness and `decode_instruction_complete`.
- Keep unsupported opcodes distinct from malformed operand bytes.
- Measure module-only and focused-consumer checks before and after, and add a
  multi-opcode growth regression rather than baking these host times into CI.
- Do not raise kernel fuel or cache limits to hide the term shape.

## What it assumes from elsewhere

- **[[x86-direct-bitfield-decoder]]** owns direct operand extraction and
  completeness. This issue changes only opcode classification/proof sharing.

## Log

- 2026-08-28: Filed from the `SUB`/`CMP` round when nine supported opcode
  branches made the repeated completeness-dispatch cost visible.
