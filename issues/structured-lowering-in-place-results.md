---
title: Structured lowering refuses a result placed in one of its own input registers
status: open
labels: [compiler,function-ir,x86,register-allocation]
created: 2026-09-24
updated: 2026-09-24
---

Found 2026-09-24 by the bounded-loop probes (`docs/native-bounded-loops-design.md` §8 V2).
`select_here` in `crates/elab/src/function_ir_x86_lower/structured.rs` refuses a
temporary that is also an input (`InputOverlapsTemporary`), and an output must be
a temporary, so `cursor ← cursor + 1` in one typed certificate is refused.

A loop updates its head registers every iteration. It currently goes through
scratch plus a pure `copy(x) = x` certificate into the head register, which is
accepted today because the head register is not an input of the copy. That
costs a MOV and a separate certificate per updated value (13 bytes each at the
probe's placements) and three more steps in the generated glue.

Lever: let a requested output name a *consumed* input register. Select into a
fresh temporary, end with one move into the requested register, and drop that
register from the certificate's protected frame (it is clobbered by design).
The frame proof needs only that the move is the last write. Not a prerequisite
for the loop certificates; worth doing when code size or glue length matters.
