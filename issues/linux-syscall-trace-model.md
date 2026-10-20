---
title: Flesh out the Linux syscall trace beyond read-once and exit
status: open
labels: [x86,semantics,runtime,design]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-09-24
updated: 2026-10-20
---

## Scope

The first program ([[native-first-program]]) uses a deliberately basic Linux
trace: `LinuxRuns` with a `Read` rule (success only, bytes quantified) and an
`Exit` rule, over fetched steps. This issue owns making it a real model of a
process's interaction with Linux.

## Open questions, roughly in order of need

- **Error returns.** A failed read currently has no rule, so theorems are
  silent about it. Model negative `rax` returns (at least `EBADF`, `EFAULT`,
  `EINTR`) so a program can be proven to handle them.
- **write** as an event, with the partial-write return.
- **Syscalls inside loops.** Read-until-EOF needs a loop whose body is a
  syscall, not a `LoopReadable` buffer loop.
- ~~**Determinism.**~~ Landed 2026-09-28 as a theorem about the step
  relation ([[fetched-step-deterministic]]); the trace relation is unchanged.
- **Partial runs.** Claims compare complete runs (ending at an exit). A
  relation for a run cut off anywhere would let a claim say no run of the
  file diverges or stops between syscalls; `linux_steps_meet` is the
  ingredient.
- **RCX/R11 and the rest of the syscall ABI's register effects.**
- **Shape.** An event list over a relation, or an interaction tree, which
  [[effects-direction]] has open for the surface language. The machine-level
  trace is what a surface effects model will eventually be proven against,
  so the two should be decided with each other in view.
- Signals, other file descriptors, `mmap`/`brk` when a program allocates
  ([[memory-bound-certificates]]).

## Log

- 2026-09-24: On the "Shape" bullet: `docs/interaction-trees-fit.md` §6.1 sketches the trace as the `is_trace_of` set of a machine denotation over a syscall event container. That makes determinism structural (one tree, a function of the responses), turns error returns into response types, and models the world as a history-indexed oracle with no coinduction. Owned by [[interaction-trees-container-model]]; the boundary-as-interface view is [[open-component-refinement]].
- 2026-09-25: Took over from [[native-first-program]] (closed): the read size is fixed at 4096, one RW page. Reading until end of input in a syscall loop, under 'Syscalls inside loops' above, makes the input size independent of the buffer, so the bound is not turned into an argument first.
- 2026-09-27: Syscalls inside loops: read-until-EOF needs no new rule. The loop is an induction over the chunks in the process proof ([[native-read-until-eof]]).
- 2026-09-27: 2026-09-27: Decisions for the failure-paths round (with the user): (1) **shape**: keep `LinuxRuns` as a relation over an event list, not tier-2 plus container ITrees first. Each event becomes a command with its response (read: bytes or errno; write: count or errno), so a later move to Cmd/Resp is mechanical. (2) **wc -l's policy**: EINTR on read or write retries the call; any other error exits with status 1; a short write loops until the rest is written. (3) **Determinism** is its own later round (a FetchedStep uniqueness theorem), not part of this one. Motivation found while scoping: the built binary tests only RAX = 0, so a negative read return is counted as a huge byte count. The certificate is silent there, and the program is wrong there.
- 2026-09-27: 2026-09-27: Landed (docs/native-syscall-failures-design.md, §9 amendments, §10 probes). Read and write events carry Linux's response (`ReadResult`, `WriteResult`); a failed read's buffer is quantified junk. wc -l retries EINTR on read and write, exits 1 on any other failure, and loops over short writes. Both claims are universal over the histories (read steps + ending, write steps + ending); `prints_the_line` gives stdout on a run that ends well. New x86 form `JumpSignNear`. Still open here: determinism (filed [[fetched-step-deterministic]]), the syscall ABI's other register effects, the shape question (ITrees need tier-2 inductives), other syscalls and signals beyond EINTR.
- 2026-09-28: Determinism landed ([[fetched-step-deterministic]]): claims are universal over complete runs with the same responses (linux_x86_64_determinism). New open item owned here: a relation for partial runs, so that 'no run of the file diverges or stops between syscalls' can be stated; linux_steps_meet is the ingredient.
- 2026-10-03: Open, close and stat events (openat with AT_FDCWD and O_RDONLY, close, newfstatat/fstat with the stored 144 bytes quantified) are designed in docs/native-wc-command-design.md §4.3 and owned by [[native-wc-as-a-command]]. Neither EINTR on open nor EINTR on close is retried, because GNU retries neither.
- 2026-10-20: 2026-10-20: The Shape bullet has a design: docs/native-program-logic-design.md §2 splits LinuxEvent into a call/answer container (LinuxCmd, LinuxAns) and states claims as Sim at a coalgebra spec, bridged both ways to LinuxRuns ([[native-linux-spec]]). Partial runs and divergence stay here (design §10, question 3).
