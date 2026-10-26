---
title: Give native programs their command line
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-26
---

Round 6 of `docs/native-real-programs-plan.md` (§3.5, §6). A `Source` has no
arguments: its tree is fixed, and the process image maps no stack. The
machine side states argv's layout (`ArgvAt`,
`lib/std/os/linux/linux_x86_64_io.hthr`). Nine of the plan's fourteen tools
need argv.

## Scope

- `Source::denote` takes `args: List<List<BitVec(8)>>`. The environment
  starts with `argc` in a word, and a statement `Arg(k, buf, len)` copies
  argument `k` into a buffer, clamped to its capacity, with its length (or
  −1 past `argc`) in `len`.
- The compiler saves RSP to a slot at entry and copies an argument with the
  byte loop it uses for reads. The proof meets `ArgvAt`.
- The image side is [[io-image-process-stack]]: the stack region and RSP in
  the entry state. This round finishes it.

## Done when

`echo` (GNU's, no flags) and `yes STR` are built by `write-elf` and match GNU.

## What it assumes from elsewhere

- **[[io-image-process-stack]]** owns the profile's stack region.
- **[[native-source-bytes]]** owns constant bytes (the space and newline).
