---
title: A loop condition that is a bit variable compiles
status: open
labels: [native,effects,runtime]
area: heather-in-heather
milestone: [nh-effects]
created: 2026-11-12
updated: 2026-11-16
---

`ETm::placed` (`lib/native/runtime/rt_io_lower.hthr`) leaves a bit in the
port its region wrote when the region's last node writes it at one bit (a
comparison), because the compiler takes no one-bit `Move`. Any other bit
is still moved to a fresh word at width 1, and `write-elf` refuses that
statement ("a compose region the compiler does not take"). The common
case is a condition that is a variable, `while going` over a `Bool`
bound earlier: `Tm::lower` of a `Var` is an empty region naming the
variable's port, so it is moved at one bit. A `Lit` bit is a one-bit
`Const`, which stays in place, but whether the compiler takes a one-bit
`Const` has not been checked.

## Scope

- A bit variable's word holds 0 or 1 (`Ty::Kept` at `Bit`), so a wide
  move (`Move(64, …)`) copies it exactly; prove that and use it for any
  bit that does not stay.
- A probe in `rt_io_lend_tests` or `rt_io_loop_tests` that compiles a
  loop over a `Bool` variable.

## Done when

A loop whose condition is a bit variable compiles through `write-elf`.

## Log

- 2026-11-16: 2026-11-16: `ETm::If`'s test met it too: a test bound by an `ETm::Let` and read as `Var` made write-elf refuse tr_upper's pass. The reflector now writes an `if`'s test as one `Tm` with its lets inside, as a loop's is; a written `If(Var(b), …)` over a `Bool` variable still hits this.
