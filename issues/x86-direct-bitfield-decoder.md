---
title: Refine the x86 reference decoder to direct bitfield extraction
status: open
labels: [x86,semantics,performance,proofs]
created: 2026-08-28
updated: 2026-08-28
---

The first executable decoder is proof-producing and intentionally simple: for
a recognized opcode it searches the 16×16 register-pair space, compares the
exact three-byte candidate, and returns the matching `DecodesInstruction`
witness. This is a trustworthy reference implementation and its bounded search
is adequate for the current three-byte fragment, but it is not the decoder
shape that should scale to SIB, displacement, immediate, or prefix streams.

## Acceptance

- Decode REX.R/REX.B and the ModRM.reg/ModRM.r/m fields directly from their
  bits, rejecting non-REX.W and non-register ModRM modes before operand
  construction.
- Return the same proof-producing result type or an equivalent one: successful
  execution must still carry evidence for the declarative `DecodedAt` surface.
- Prove the direct decoder sound for `DecodesInstruction` and complete for the
  currently supported relation.
- Prove or exhaustively check agreement with the bounded-search reference
  decoder across all supported opcodes, all 256 register pairs, malformed REX
  bytes, and every ModRM mode.
- Measure closed decoding and module elaboration before replacing the reference
  path. Keep the search decoder as an oracle if its maintenance cost stays low.
- Reuse generic `BitVec` slicing/reconstruction laws; any missing reusable law
  belongs in `std/bitvec`, not as an x86-local arithmetic fact.

## What it assumes from elsewhere

- **[[fixed-width-bitvectors]]** owns bit extraction and reconstruction.
  Assumed here: only that direct REX/ModRM field proofs use that generic API.
- **[[x86-64-machine-model]]** owns `DecodedAt`, instruction normalization, and
  the supported encoding set. Assumed here: direct decoding refines that
  relation rather than defining another one.

## Log

- 2026-08-28: Filed from the first executable-decoder round. The bounded search
  made soundness by construction small and kernel-checkable, while also making
  the scaling boundary concrete before memory operands are added.
- 2026-08-28: Debug consumer-probe measurement on the same tree: canonical and
  alternate low-register successes plus a matched unsupported opcode checked in
  about 24s; adding one extended-register success and two rejections that miss
  all 256 register pairs raised it to about 41s. This is acceptance-test scale,
  not a benchmark threshold, but confirms direct field extraction is required
  before the supported encoding family grows.
