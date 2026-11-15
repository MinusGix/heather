---
title: elf64_read_loop and elf64_read_print are named for processes they no longer hold
status: closed
labels: [lib, naming, native]
created: 2026-09-29
updated: 2026-09-29
---

Since `wc -l` moved onto elf64_read_state (docs/archive/native-wc-design.md §9), the
process that gave `lib/elf64_read_loop.hthr` its name is gone: what remains is
the read profile's pieces (blocks, `EofJumps`, the read trace, the chunk's
entry, `ReadEofComputes`). Likewise `lib/elf64_read_print.hthr` now holds
the printing pieces (blocks, `PrintJumps`, `ReadPrintFormat`, `print_sends`,
`write_events`, the write-loop arithmetic), and its process lives in
elf64_count_print.

A rename (e.g. `elf64_read_pieces`, `elf64_write_pieces`) touches the
bundle tables in `crates/cli/src/native/`, every importing library and test,
and the image cache keys; the `eof_` prefix on names that are about one
read, not the end of file, could go in the same round.

## Log

- 2026-09-29: Renamed after each module's own header: `elf64_read_loop` → `elf64_read_pieces`
  ("the read profile's pieces"), `elf64_read_print` → `elf64_print_pieces` ("the
  printing pieces"), in the bundle tables, every importing library and test, and
  examples/x86-native; the headers say what the modules used to be called.
  Design docs and issues keep the old names where they describe that time;
  native-wc-design.md §9 notes the rename.

  The `eof_` prefix stays, on purpose: about 550 occurrences (`eof_rip` alone is
  262), and most of the names are about the process that runs to end of file
  (`eof_input`, `eof_events`, `eof_rip`) or test for it (`eof_test_block`). Only
  the retry and fail blocks are about a single read, and renaming those alone
  would split one family of names in two.
