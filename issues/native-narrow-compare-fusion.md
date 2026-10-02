---
title: Fuse narrow (byte) comparisons into CMP + Jcc
status: open
labels: [native,x86,lowering]
created: 2026-10-02
updated: 2026-10-02
---

`fusable` in `crates/elab/src/function_ir_x86_lower/structured.rs` fuses a
branch's comparison into CMP + Jcc only at width 64. A byte test (width 8),
which every native filter step has, is materialised instead: SETB or SETE
into a low byte, then TEST and JZ. Since fd95e486, wc_l's newline test is
`cmp; sete; test; je`. It could be `cmp; jne`.

Narrow operands are already compared zero-extended (`unsigned_lt_zero_extend`,
`eq_bit_zero_extend`), so fusion needs the narrow condition's skip laws
stated through those, not a new mechanism. Smaller executables and fewer
instructions per byte.

Also tidy while there: `BitVec::increment_decrement` (bitvec) now duplicates
the unqualified `increment_decrement` in `x86_64_calls.hthr`.
