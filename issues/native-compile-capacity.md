---
title: Build native programs up to the file limit within the suite's memory rail
status: closed
labels: [native,cli,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-27
---

Round 2 of `docs/native/native-real-programs-plan.md` (§3.2, §6). Measured on
master `aee4a09`: `write-elf` of cat with its pass inlined twice (about 1.7×
cat's code) peaks at about a third of the suite's 6 GiB rail. Inlined four
times (about 3×), it aborts under the 8 GiB direct-run rail
(`memory allocation … failed` in `function_ir_source::evaluate_numbers` on
the fork). With the rail raised it peaks near 6 GiB. Inlined eight times
(about 6×), it is OOM-killed on the cloud box. Peak memory grows about as
the square of code size, and time about linearly. The plan's tools will be
many times cat, and the profile's file limit is 64 KiB of code.

## Scope

- Attribute the peak: the fork's read-back (`_numbers` and `_lens` each
  evaluate `Source::compile`, and the reader's `ValueArena` keeps everything
  until it returns) against the kernel's one-`refl` emission check
  (`<s>_elf_emitted`). Add `--timings` to `write-elf`, which refuses it today.
- Read the program back once and in pieces, holding one stretch at a time.
- If the kernel's emission `refl` is superlinear, state the emission a
  statement at a time. `Stmt::emit` threads a label counter through `Then`,
  so each statement's code is an equation at a known counter.
- Record the size-to-peak and size-to-time shapes under `perf/`.

## Done when

A program with 64 KiB of code builds under the suite's 6 GiB rail, and
`cat_x8` builds in a test.

## What it assumes from elsewhere

- **[[native-cat-executable]]** owns `write-elf` and its certificate shape.
  Assumed here: only that the certificate's statements may be split
  differently as long as they state the same file.

## Log

- 2026-10-26: profiled with `write-elf --timings` (new, with a
  `peak_growth_kb` column: the rise of the process's VmHWM while a row's
  scope was open, exact at kernel width one). On master the peak was the
  fork's read-back, not the kernel: `Prog::numbers` appended each item after
  everything before it down the left spine (quadratic), and the read re-ran
  `laid_out`, whose every jump walks the whole program to find its label;
  the reader's `ValueArena` kept all of it. Fixes:
  - `Prog::numbers` conses from the back (as `asm_lens` does), and the read
    evaluates only the emission; the certificate already proves the layout,
    and a cheap Rust check of names and targets (`layout_refusal`) keeps the
    refusal clear.
  - The read is one small evaluation per part of the statement tree
    (`Source::shape` reads the tree's shape; `crates/cli/src/native/emission.rs`
    plans parts of at most eight leaves, read with `Stmt::emission_reading`
    at `Start`, since emission never inspects the program before it).
  - The kernel ran out of fuel on the one-`refl` emission and the one-`refl`
    code length at cat_x8. The emission is now stated a part at a time and
    joined by `Stmt::emit_then_of` / `emit_repeat_of` / `emit_branch_of`
    (`native_compile_correct.hthr`, proved once), through projections
    (`Stmt::left`, `right`, `word`, `is_*`) so no statement spells a
    subtree; the length is stated a piece at a time (`List::len_append`).
- Shapes at kernel width one, cloud box, fresh copy of a warmed cache per
  size (`perf/fixtures/native_sizes/run.sh`; growth is above the process's
  start, of which ~0.9 GB is the library replay at every size):

  | probe  | code bytes | master peak | now: run growth | largest elf row | time |
  |--------|-----------:|------------:|----------------:|----------------:|-----:|
  | cat_x2 | 2400       | ~2 GB       | —               | 61 MB           | —     |
  | cat_x4 | 4322       | 6.1 GB      | 0.90 GB         | 79 MB           | 204 s |
  | cat_x8 | 8166       | OOM (15 GB) | 1.01 GB         | 139 MB          | 572 s |
| cat_x16 | ~16 K     | —           | 1.38 GB         | 297 MB          | 2490 s, refused |

  Peak memory no longer tracks the code: the largest certificate/read row
  grows about linearly (the byte pieces' reads, `piece_numbers_k`), and the
  library replay dominates. Time grows by about an exponent of 1.6 here,
  heading for 2: at cat_x8 the layout stretches (`landing`/`lands`/
  `named`/`unique`/`naming`/`fresh`) are 316 s, the byte pieces 80 s, and
  the two elaborations of the code literal (`at_k`, read and certificate)
  140 s. Those are [[native-compile-linear-layout]]. cat_x16 spent 1900 s
  in the stretches and then ran out of kernel fuel on its first byte piece
  (`cat_x16_elf_piece_0_is`, OutOfFuel): a piece's jump lookups walk the
  whole program, so at that size one piece no longer fits the fuel. Past
  about 8 KiB of code the quadratic lookups are a wall, not only a cost.
- Done-when status: memory is met (the read's peak per row is bounded by a
  part, the certificate's by a piece). `cat_x8` builds but not inside the
  suite's 300 CPU-s rail, so its test waits on
  [[native-compile-linear-layout]]; so does anything past about 8 KiB of
  code, since cat_x16's byte pieces run out of fuel.
- 2026-10-27: done. With [[native-compile-linear-layout]] (layout and
  bytes by a label table), cat_x60, 58 KB of code (as close to the
  profile's 64 KiB file limit as cat's passes come), builds under the
  6 GiB rail at width one in 892 s and runs as cat; cat_x8 builds and runs
  in `crates/cli/tests/native_cat.rs`. The run's growth is 3.5 GB, most of
  it the shape read (linear) and the library replay; the constants left
  are [[write-elf-build-constants]].
