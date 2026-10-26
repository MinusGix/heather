---
title: Build native programs up to the file limit within the suite's memory rail
status: open
labels: [native,cli,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-26
---

Round 2 of `docs/native-real-programs-plan.md` (§3.2, §6). Measured on
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
