---
title: "System calls placed from a description, not from literal registers"
status: open
thread: Make compiler correctness proofs elegant
labels: [native,x86,linux,design]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-17
updated: 2026-11-17
---

`Prog::reads`, `writes`, `opens` and `closes` each write the Linux call out
at its use: the number as `MovRI(Rax, BitVec::ofNat(0))`, the arguments as
moves into `Rdi`, `Rsi`, `Rdx`, the result read from `Rax`, the scratch in
`R8` and `R9`. Their run lemmas (`Target::goes_reads`, `goes_writes`,
`goes_opens`, `goes_closes`) and the four arms of `Target::call_runs` are
the same argument four times.

## Wanted

A description of a call (its number, the registers its arguments go in,
where the result returns, what it may clobber) that the four instantiate,
and scratch registers named by role. One emitter places a call by a
description; one theorem says a call so placed runs as the model's call,
for any description. The theorems get more general as they get shorter
(`docs/library/program-and-proof-style.md` §2).

To settle: where the description lives (beside `linux_calls` in the Linux
model, which already knows the numbers and the argument order), and how an
operand that is a clamped length or a buffer address is said.

## Done when

`Target::call_runs` has one arm for the calls a description covers.

## Log

- 2026-11-17: filed from Minus's review of `lib/native/native_compile*.hthr` (`docs/library/program-and-proof-style.md`).
- 2026-11-17: first cut in `lib/native/native_compile.hthr`: `Abi` (where a call's number, first three arguments and result go, `Abi::linux_syscall()`), and a record per call naming each argument's place as its manual page does (`Read`, `Write`, `Close`, `Openat`, from `abi.read()` and so on). The four emitters take their registers from these. Left: the theorems are still stated per call (`Run::goes_asked` takes the code and a `CallShape`); one theorem "for any call placed by this convention" needs the call's arguments as data, not as builder steps.
