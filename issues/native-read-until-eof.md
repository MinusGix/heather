---
title: Certified wc -l reads until end of file
status: closed
labels: [x86,compiler,runtime,proofs]
created: 2026-09-27
updated: 2026-09-27
---

The certified `wc -l` reads stdin once, up to 4096 bytes. On a pipe or a
larger file it counts only a prefix. It should loop: read, stop at the empty
read, count each chunk into a running total.

Design: docs/native-read-until-eof-design.md@4acf2fe. Decisions (2026-09-27, with
the user): the contract is additive (the loop from any count adds
`spec(chunk)`, and `spec` adds over concatenation); the read-once profile is
replaced rather than kept beside it.

## What it assumes from elsewhere

- **[[linux-syscall-trace-model]]** owns the trace. Assumed here: only that
  `LinuxRuns` takes any number of `ReadEvent`s, which it already does.
- **[[native-first-program]]** (closed) is the read-once program this
  replaces.

## Acceptance

- `build-x86 --read-loop` and `--print` write a program whose claim covers
  every split of the input into non-empty reads, ending at the empty read.
- The built `wc -l` matches the system's on inputs past one page and on a pipe
  written in bursts.
- Refusals: resetting the count per chunk, saving it to a register SYSCALL
  clobbers or the loop never restores, and a backward jump to the wrong place.

## Log

- 2026-09-27: 2026-09-27: Probes held (design §6). Library, producer, example and tests written; decisions: additive contract, read-once replaced. `omega` gaps met: [[omega-atoms-up-to-computation]]; a probable second sighting logged on [[tier1-arm-binder-has-no-spelling]].
- 2026-09-27: 2026-09-27: Landed. Both profiles build and match the system's `wc -l` on files past one page, on a 9999-line file (three reads) and on a pipe written in bursts. The exit build is 645 bytes (about 13 s cold), the print build 2780 bytes (about 30 s). The library refuses five new mutations: count reset, count saved where setup writes, end tested on another register, exit with clobbered R11, and a mis-stated back-jump span. Full suite 3010 passed; `wc_l_prints_every_line` took 43 s in the suite.
