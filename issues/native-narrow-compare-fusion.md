---
title: Fuse narrow (byte) comparisons into CMP + Jcc
status: closed
labels: [native,x86,lowering]
created: 2026-10-02
updated: 2026-10-03
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

## Log

- 2026-10-03: Landed. `fusable` (structured.rs) takes a narrow comparison too, except a signed one, because zero extension doesn't keep the signed order. The fused operands keep their width. The branch's skip law is the 64-bit one over the zero-extended words, rewritten by `unsigned_lt_zero_extend` / `eq_bit_zero_extend` (structured_cert.rs). Tests: `narrow_fused_branches_check_and_refuse_another_test` covers equality and unsigned order of a byte against a literal and against a computed sum, refuses wrong-condition and swapped-operand mutants, and leaves a narrow signed comparison unfused. `a_narrow_fused_branch_past_rel8_is_near` covers the near jumps; `record_state_step_publication_checks` used to cover them, but its arms now fit rel8. Measured with build-x86 against master 4cbe35d, fresh cache each side. Executable bytes: wc_l 1587 → 1571, wc 5870 → 5710, tr -s 749 → 701, tr -d 669 → 637, tr 675 → 643. Declarations in the step's piece modules: wc_l 383 → 368, wc 2510 → 2360, tr -s 952 → 907, tr -d 593 → 563, tr 500 → 470. decls_gated: 673 → 631, 4116 → 3682, 1427 → 1369, 662 → 564, 870 → 832. Tidy: x86_64_calls' unqualified `increment_decrement` and its step are gone; `increments_decrement` uses `BitVec::increment_decrement`.
