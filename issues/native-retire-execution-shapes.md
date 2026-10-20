---
title: Every native program on the program logic; retire the five execution shapes
status: open
labels: [native,x86,refactor]
area: heather-in-heather
milestone: [hih-pl-retire]
blocked-by: [native-filter-on-program-logic]
created: 2026-10-20
updated: 2026-10-20
---

Round P5 of `docs/native-program-logic-design.md` (§3, §9): every native
program on the logic, and the five execution shapes gone as judgments.

## Scope

- `wc`, `wc -l` and the command (`elf64_command`, the process libraries)
  stated as `Sim` at their specs; their `eof_from` uses, `EofProcess` and
  per-process event functions deleted.
- Generated pieces (the loop generator's step, the typed generators'
  outputs) enter as `Proved` items: `Computes` is a contract's post;
  `AccessFragment`, `AccessBranch` and the `StructuredArtifact` route stop
  being how a program is stated.
- The design's §3 table done: `ExecuteFetchedBlock`, `LinuxFetchedTrace`
  and the `Linked*` family deleted; `FetchedOrStore`, the second syscall
  byte spelling and the conditional's extra byte spellings unified;
  `linux_runs_*` take `LinuxSteps` uniformly.
- Closes `hih-program-logic`; residue gets owners first.

Likely more than one PR; split by program if so.

## What it assumes from elsewhere

- **[[native-filter-on-program-logic]]** is the pattern this round repeats.
- **[[list-layouts-onto-labels]]** owns the parked list layouts; a list
  layout still standing is moved here only if a program's proof needs it.
