---
title: Size a native program's data region to the program
status: closed
labels: [native,x86,memory,elf]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-28
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

## Log

- 2026-10-28: Done. The I/O profile is `X86Profile::io(size)`: the RW
  segment is `size` zero-filled bytes at 0x410000 (`DataRegion::io_data(size,
  within)`, `within: size <= io_data_limit()`, a GiB), the header's
  `p_memsz` is `size`, and the loader (`X86Memory::io_load`), `LoadedFrom`
  and the stack's floor (`io_data_end(size)`) are stated over it. The old
  page/frame pair is gone from the library; the hand-proved Wp fixtures that
  used the frame define it locally over an eight-KiB segment.
  A source declares its words (`Source::words`; `Source::of` and the
  builder count them by `Stmt::word_bound`), `Layout` and `Target` carry
  them, and `Layout::word_fits` checks ids against them (the allocator's
  closure fuel is `words²+1`). `write-elf` gives the segment the layout's
  size in whole pages and states `<s>_elf_size`, `<s>_elf_within`,
  `<s>_elf_fits` in the certificate; a program past the limit is refused by
  reason. `mib_cat` (cat with a 1 MiB buffer, `lib/_tests/native`) builds
  with a 2101248-byte segment and a 1176-byte file, reads a MiB per call
  from a file, and carries `mib_cat_elf_simulates`
  (`crates/cli/tests/native_cat.rs`, `mebibyte_buffer_runs_as_cat`).
  Kernel cost: nothing in the certificate grows with the segment; addresses
  stay `add_nat` from the segment's start.
