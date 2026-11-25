---
title: Site::Meets at the entry routine gives the program's RunsAs: the whole-program theorem over the Linux model
status: open
labels: [native,x86,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`Site::Meets` (`lib/std/arch/x86_64/x86_64_call_contract.hthr`, [[bytes-level-on-the-contract]]) states the machine's run against the world with the Linux model's own definitions (`LinuxSyscallAt`, `LinuxRequests`, `LinuxLeaves`, `linux_answered`, `LinuxResumes`, `LinuxExits`), but its own relation (`Site::Performs`, `Site::Step`) is not yet tied to the whole-program statements built on that model (`RunsAs`, `Sim`, `SimProgram` in `linux_x86_64_sim`, `LinuxRuns` in `linux_x86_64_io`). `docs/language/ownership-design.md` §18.2's whole-program theorem is that tie: at every fuel, the trace the code has performed is the history the meaning has reached, and an exit ends it.

## Scope

- From `Site::MeetsExited` and `Site::MeetsGoing` at a program's entry routine, entered as the image starts it, to `RunsAs` of the trace the meaning's history is (the world's answers read as the trace's), and from `MeetsDone` with an exit after it likewise.
- `Io::Answerable` (each answer of the world one Linux may give) against `Trace::LinuxValid`.

## Done when

A theorem from `Site::Meets` at the entry routine to the program's `RunsAs` at every fuel, with its probe at a two-call program.

## What it assumes from elsewhere

- [[bytes-level-lowering]] proves `Site::Meets` for lowered programs; this states what it buys a whole program.
