---
title: Site::Meets at the entry routine gives the program's RunsAs: the whole-program theorem over the Linux model
status: open
labels: [native,x86,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-26
---

`Site::Meets` (`lib/std/arch/x86_64/x86_64_call_contract.hthr`, [[bytes-level-on-the-contract]]) states the machine's run against the world with the Linux model's own definitions (`LinuxSyscallAt`, `LinuxRequests`, `LinuxLeaves`, `linux_answered`, `LinuxResumes`, `LinuxExits`), but its own relation (`Site::Performs`, `Site::Step`) is not yet tied to the whole-program statements built on that model (`RunsAs`, `Sim`, `SimProgram` in `linux_x86_64_sim`, `LinuxRuns` in `linux_x86_64_io`). `docs/language/ownership-design.md` §18.2's whole-program theorem is that tie: at every fuel, the trace the code has performed is the history the meaning has reached, and an exit ends it.

## Scope

- From `Site::MeetsExited` and `Site::MeetsGoing` at a program's entry routine, entered as the image starts it, to `RunsAs` of the trace the meaning's history is (the world's answers read as the trace's), and from `MeetsDone` with an exit after it likewise.
- `Io::Answerable` (each answer of the world one Linux may give) against `Trace::LinuxValid`.

## Done when

A theorem from `Site::Meets` at the entry routine to the program's `RunsAs` at every fuel, with its probe at a two-call program.

## What it assumes from elsewhere

- [[bytes-level-lowering]] proves `Site::Meets` for lowered programs; this states what it buys a whole program.

## Log

- 2026-11-26: From [[call-contract-tracks]] D: how `Site::Tracks` gives `RunsAs` (the route, not yet built).

  1. At the entry routine, entered as the image starts it, `Tracks` at fuel `n` gives the state read off the meaning:
     - done: returned, then the image's exit after it;
     - exited: at the exit call, its world the meaning's;
     - going: at least `n - 1` steps in the meaning's world.
  2. `Site::tracks_meets` gives `MeetsGoing` once: every world the code reaches in `j` steps before it returns is a prefix of a history the meaning reaches at some fuel, or the meaning gets stuck.
  3. `RunsAs` of the trace the meaning's history is (the world's answers read as the trace's) then follows by cases on the machine's run:
     - a run that ends at the exit call is `MeetsExited`'s world, the whole history;
     - any other prefix is `MeetsGoing`'s prefix of some history.

     An answerable world keeps every answer one Linux gives (`io.Answerable()`).

  What remains: the image's start (its `_start` CALL into the entry routine and the exit after a done return), and reading `Io.past` as an itree trace for `RunsAs`.
- 2026-11-26: From [[bytes-level-lowering-world]] item 5: `Site::tracks_runs_as` (`lib/native/bytes_level/bytes_level_whole.hthr`).
  - What it gives: `Tracks` at every routine, at every fuel, in every answerable world, is `RunsAs` of the trace the meaning's outcome reads (`Ran::trace`). Done and going end in `TEnd`, exited in `TRet(status)`, stuck in nothing.
  - How: through `Site::linux_runs_as`, for any Linux claim whose goal pins the world.
  - Probe: `echo_runs_as` (bytes_level_routines_tests).
  - Remaining for this issue's done-when:
    - the image's `_start`, which calls the entry routine and exits after a done return;
    - `Sim` over the meaning read as an itree, or over its fuel-indexed traces;
    - `Trace::LinuxValid` of the trace, from `Io::Answerable`;
    - the probe at a two-call program.
