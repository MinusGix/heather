---
title: Compile SInt::div/rem to IDIV with guards
status: open
labels: [native,x86,runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-08
---

`SInt::div`/`rem` on an i64 should compile to `CQO; IDIV r64` (REX.W 99,
REX.W F7 /7), guarded at a zero divisor and at `MIN / -1`, checked end to
end against C. The flags side is done ([[x86-undefined-flags]], round 5 of
docs/native/runtime-fn-setups-design.md §16.13): IDIV can leave all six flags
undefined (`DefinedFlags::none()`), and `Exception::DivideError` exists with
`Instruction::faults(gprs)` wired into `Execute`. What remains:

- **The model.** CQO writes RDX with RAX's sign. IDIV divides RDX:RAX by
  r/m64: RAX the quotient and RDX the remainder (truncating, `BitVec::sdiv`
  and `srem` at a sign-extended dividend); `faults(gprs)` is a zero divisor
  or a quotient outside i64, which is closed and computable from the 128-bit
  dividend (`Int` arithmetic), so the model stays exact rather than refusing
  a non-sign-extended RDX.
- **Admission.** `block_reads` admits no instruction that `may_fault()`,
  and it sees only the mask, not values, so a block holding IDIV is refused
  today. Needed: a value-level route beside it, where the lowering proves
  `faults(gprs) = False` at the IDIV from its own guard (the block lemma takes
  the instruction's fault freedom as a hypothesis over the state it runs
  from, as `Lowered`'s keeps proofs already reason about register values).
- **rt and FunctionIR.** `rt` has no division (signed or unsigned), and
  FunctionIR no division node ([[runtime-signed-extend-divide]]). The
  meaning at the two faulting points is whatever `BitVec::sdiv`/`srem` say,
  so the guard is part of the lowering: either a branch (a region with an
  else arm), or branch-free by substituting divisor 1 at both points (at
  `MIN / -1`, dividing by 1 gives `MIN`, which is `sdiv`'s answer; at zero,
  the result is then patched to `sdiv`'s zero-divisor value).
- **The C check.** A showcase function using `/` and `%` on `i64`,
  compared with C's on the same inputs, including both guarded points (C's
  own behaviour is undefined there; the comparison is against Heather's
  meaning).

The remaining instructions that leave flags undefined (MUL, IMUL, BSF)
come by the same mask and need no further model change.
