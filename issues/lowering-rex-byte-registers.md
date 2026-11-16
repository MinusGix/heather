---
title: Let the structured lowering compare into REX byte registers
status: closed
labels: [x86,native,lowering]
created: 2026-10-01
updated: 2026-10-03
---

The structured lowering compares into a byte register through `LowByteGpr`,
which has only AL, CL, DL and BL: the legacy encodings without a REX
prefix. In the stream filter's step piece (docs/archive/native-stream-filter-design.md
§10, `crates/elab/src/function_ir_source/filter_step.rs`), RAX holds the
input byte and RCX belongs to the per-byte loop, so a step has only RBX and
RDX for comparison bits. Those are also the two results the contract fixes
(the emit flag in RBX, the byte in RDX). Lowering the emit straight into
place leaves the next piece no byte register (`RegisterPressure`).

The generator works around it: an emit computed from the state is held in
R9/R10 while the fields are updated, then copied into RBX/RDX
(`emit_copy`). Fields that read each other in a cycle are held the same way
(`tr -s`'s state). That costs up to three bytes per copy, and a hold
register each.

The proper fix: the lowering's byte registers include the REX forms (SIL,
DIL, BPL, SPL never needed, and R8B–R15B), with their encodings and decoder
cases in the x86 model (`lib/std/arch/x86_64/`), so a comparison can land
in any scratch register. Then the emit can go straight into place again.

## Log

- 2026-10-03: Landed with [[native-narrow-compare-fusion]]. `LowByteGpr` gains BPL, SIL and DIL (empty REX, 40) and R8B–R15B (REX.B, 41); SPL stays out. `setcc_bytes` puts the REX in front when the register needs one (`setcc_length` is 3 or 4). The decoder reads a REX without W followed by 0F 9x (`decode_rex_setcc`). It sits behind a W-bit check, so REX.W forms keep their cheap arm. The step-form decoder does the same (`decode_rex_setcc_form`, under 0F when REX.W is clear). Completeness and length lemmas go register by register. The lowering prefers AL–BL for a bit, since that is a byte shorter, and the REX registers for wide values. The filter step now computes an emit read from the state first, straight into RBX and RDX; `emit_copy` remains only for a cycle's held field. Against the fusion alone: tr -s 701 → 695 bytes and 907 → 791 step declarations (decls_gated 1369 → 1049); tr -d 637 → 631 bytes and 563 → 447 declarations (564 → 560). Counting and mapping steps keep their size. The W-bit check adds about 1% eval steps on wc_l's and wc's step modules. Tests: `comparisons_materialise_into_rex_byte_registers`, plus four REX destinations in the native encoder check.
