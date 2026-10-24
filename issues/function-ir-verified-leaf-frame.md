---
title: Give a leaf function no stack frame in the verified lowering
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-24
updated: 2026-10-24
---

Every function `lower_program` emits opens a 64-byte frame
(`frame_allocate`, `ADD RSP, -64`) and frees it before `RET`
(`function_ir_lower_calls`), 8 bytes per function. A leaf that makes no
call spills nothing into it, so for a leaf the pair is dead code. The old
per-function path emitted none for a leaf.

What it needs: `emit_function` chooses the frame from the body (a body
with no `Call` has none), and the per-function statement
(`Site::Calls` / the RSP invariant across the body) takes the frame as a
parameter: with no frame, RSP at the body is the entry RSP, and nothing
in the body touches the stack. The frame lemmas (`moves_frame`-style
runs over `frame_allocate`/`frame_free`) become one case of two.

Found while measuring [[function-ir-verified-selection-rules]]: after
that round this pair and [[function-ir-verified-short-jumps]] are the
whole size gap on `examples/x86-native/branches.hthr`'s leaf examples.
