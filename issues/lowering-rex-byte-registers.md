---
title: Let the structured lowering compare into REX byte registers
status: open
labels: [x86,native,lowering]
created: 2026-10-01
updated: 2026-10-01
---

The structured lowering compares into a byte register through `LowByteGpr`,
which has only AL, CL, DL and BL: the legacy encodings without a REX
prefix. In the stream filter's step piece (docs/native-stream-filter-design.md
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
