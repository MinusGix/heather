---
title: elf64_read_loop and elf64_read_print are named for processes they no longer hold
status: open
labels: [lib, naming, native]
created: 2026-09-29
updated: 2026-09-29
---

Since `wc -l` moved onto elf64_read_state (docs/native-wc-design.md §9), the
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
