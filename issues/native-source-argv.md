---
title: Give native programs their command line
status: closed
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-27
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

## Log

- 2026-10-27: Done: `Source::denote(args)` with `Env.args`; `Stmt::Arg(index, buf, len)` copies argv[k]'s prefix that fits and its whole length, or −1 past the last (no argc word: a program counts by asking past the end). Compiled by `Prog::args` (RSP saved at entry past the scratch range, argc/argv read through it, a byte loop to the NUL), proved in native_compile_args; `Placed` carries the command line (`Target::Stacked`). The ELF theorem takes `LoadedFrom(file)` below 0x412000 and `ArgvAt` above it at the entry RSP. Builder `arg(index, buf, len)`; `echo_source` (GNU echo, no flags) and `yes_args_source` (GNU yes) in native_tools.hthr, run against GNU in crates/cli/tests/native_tools.rs. An argument past its buffer exits 1 (Arg has no offset). The stack region itself stays with [[io-image-process-stack]].
