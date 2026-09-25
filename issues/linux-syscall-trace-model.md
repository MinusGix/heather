---
title: Flesh out the Linux syscall trace beyond read-once and exit
status: open
labels: [x86,semantics,runtime,design]
created: 2026-09-24
updated: 2026-09-25
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
- **Determinism.** Current claims (this one and `LinuxFetchedTrace`) are
  existential: there is a run with this trace. Uniqueness of decoding for the
  supported byte forms makes it the run. Decide whether that is a theorem
  about `FetchedStep` or built into the trace relation.
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
