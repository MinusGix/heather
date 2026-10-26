---
title: Size a native program's data region to the program
status: open
labels: [native,x86,memory,elf]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-26
---

Round 8 of `docs/native-real-programs-plan.md` (§3.6, §6). `write-elf`
places a program's whole environment in `DataRegion::io_page()`, 4096 bytes:
64 word slots, every buffer, and a scratch range as large as the largest
buffer. So a program's buffers together hold under 3.5 KiB, one buffer under
1.8 KiB, and `word_slots()` is a constant 64. `sort`, `rev` of a long line,
and `grep`'s line carried across reads need more.

## Scope

- The I/O profile takes its data size as a parameter. `p_memsz` is a 64-bit
  field in the ELF header, so a zero-filled segment costs nothing in the
  file. The loader proof (`io_perm_in_segment`, now `i < 8192`) is stated
  over the parameter, up to a fixed bound.
- `Layout` takes the program's number of word slots instead of
  `word_slots()`.

## Done when

A program with a 1 MiB buffer builds, runs and carries its theorem.

## What it assumes from elsewhere

- **[[io-image-on-byte-model]]** owns the profile and loader.
- **[[native-elf-every-program]]** owns the `fits` check `write-elf` makes.
