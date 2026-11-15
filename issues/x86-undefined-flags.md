---
title: Model flags x86 leaves undefined (IDIV, MUL, SHL by k)
status: closed
labels: [native,x86,semantics]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-08
---

`IDIV`, `MUL`, `IMUL`, `BSF` and the shifts by more than one all leave flags
undefined that the x86 model cannot express: its determinism theory
(`SameDefinedState`, the linux determinism files `linux_x86_64_determinism`,
`_io`, `_sim`, `_sim_co`, `_sim_paid`) erases only AF, which is all `TEST`
and the one-bit shifts leave undefined.

Found in the i64 round 3 (docs/native/runtime-fn-setups-design.md §16.13): shifts
went through as chains of one-bit shifts instead (`Instruction::ShiftOne`), a
shift by `k` costing `k` instructions. Signed division (`SInt::div`/`rem`,
[[runtime-signed-extend-divide]]) has no such escape.

## The choice (asked of Minus 2026-11-08)

- **An undefined-flags mask in the machine state**: each flag defined or
  not; `SameDefinedState` erases what is undefined; an instruction reading
  an undefined flag has no `Execute`. General: IDIV, MUL, `SHL r, imm8`
  (so the chains shrink to one instruction), BSF. Restates the five
  determinism files.
- **Division in software**: a shift-and-subtract `runtime fn`, no model
  change, ~64 iterations a divide, proved against `BitVec::sdiv`.
- **BMI2** (`SHLX/SHRX/SARX`, flagless, VEX) would fix shifts only, and
  binds compiled programs to Haswell or later.

## Acceptance

- The chosen route compiles `SInt::div`/`rem` with guards at a zero
  divisor and `MIN / -1` (x86 faults on both), checked end to end against C.

## Log

- 2026-11-08: Built the mask (docs/native/runtime-fn-setups-design.md §16.13, round 5): `DefinedFlags` in `Flags`, `SameDefinedState` erases undefined flags, reading one has no `Execute`, compiler blocks pass `block_reads` from no flag defined (`Prog::laid_out`'s `blocks_read_own`); the five linux determinism files check unchanged. Shifts by k are one `ShiftImm` (C1 ib). The IDIV acceptance moves to [[x86-idiv-signed-division]], which owns the value-level fault admission and the rt/FunctionIR division.
