---
title: The touched process: alike states run alike, and the converse
status: open
labels: [native,machine-model]
area: heather-in-heather
created: 2026-11-17
updated: 2026-11-17
---

A file on the system's stack now touches its stack room as it starts, and
its theorem is `Source::elf_touched_runs` (`lib/native/native_compile_elf.hthr`,
`docs/native/system-contract-design.md` §4.3): the process runs in
`X86Profile::io(size)` to each store, a claim holds in every memory Linux may
leave there (`StackTouch`), and after the last the state, seen as one of
`X86Profile::process(size, top, room)` with the same registers, cells and
permissions (`Alike`), simulates the source. Two things are owed.

1. **Alike states run alike.** `Alike(x, y, t, u)` identifies two states that
   differ only in the proof their memories carry (`X86Memory.relied`). No
   step reads that proof, so every `LinuxStep` of one is a `LinuxStep` of the
   other between alike states; that is by inspection of the model today and
   should be a lemma (fetch, the instruction's reads and writes, the system
   calls' answers, each over the access records). With it `TouchedRuns` could
   end in a simulation of the `io` state itself, and `Alike` would leave the
   statement.

2. **The converse.** `Source::elf_runs_exact` says that every run of the
   process, with answers Linux may give, is the events of a whole trace the
   source produces. It is stated of the process whose stack room is presumed
   (`stack_from_system`, a process of `X86Profile::process`), which no file is
   any more, and that section of `native_compile_elf` is kept only for it. The
   touched process needs its own: a run of it is a run through the touches
   (each leaving a memory the rule allows) and then, by (1), a run of the
   alike state, which `Program::paid_run_produces` covers. Once it is stated
   the presumed section can leave.
