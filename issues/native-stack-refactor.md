---
title: Refine the native program stack before the next process
status: open
labels: [x86,native,design,refactor]
created: 2026-09-30
updated: 2026-09-30
---

The native program stack grew one process library per program (`wc -l`,
`wc`, `tr`), and each restated what the others prove: the layout four times
over plus a Rust mirror, the failure path, the read request and end-of-file
test, the chunk induction, histories, stored-byte lemmas and register
frames. Claims take 24 to 54 parameters, and a program author passes five
theorem names whose types nothing checks up front.

`docs/native-architecture-review.md` is the survey and the plan: R0
(mechanical cleanup), R1 (relocatable read head and failure tail), R2
(bundled parameters), R3 (one read-until-EOF driver over a body contract),
R4 (one layout description shared with the producer), R5 (uniform piece
contracts, one typed generator), R6 (a checked program bundle, profile from
the source's types), R7 (one stored-bytes kit and emit-then-write tail).
Emitting stores ([[native-loop-emitting-stores]]) waits on R3, which makes
`tr -s`/`-d` a body for the driver instead of a new process.

## Log

- 2026-09-30: R0 and R1 landed (review §8): one SYSCALL encoding, the write loop's duplicate targets retired, io_entry named; the read head and failure tail proved once in elf64_read_pieces and used by the state and map processes and the write loop. R2 next when chosen.
