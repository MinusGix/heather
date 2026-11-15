---
title: Compile open, close and stat in the effectful source's compiler
status: closed
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-source, hih-tools]
created: 2026-10-25
updated: 2026-10-28
---

`Prog::call` (`lib/native/native_compile.hthr`) compiles `Reads` and
`Writes`; `Opens`, `Closes`, `StatsPath` and `StatsFd` are refused. Found
while proving S3.2 ([[native-effect-source-compiler]], 2026-10-25).

## Scope

- `Closes` and `StatsFd`: operands from word slots, the result stored as
  `goes_writes` stores it (`lib/native/native_compile_calls.hthr`).
- `Opens` and `StatsPath`: a path read from a buffer, so the call's command
  names bytes in the region (`Target::span_cells` gives them).
- `StatsPath`/`StatsFd` land a stat record in a buffer; whether Linux may
  leave the range written on failure decides whether they land in the
  scratch range and copy, as a read does (`goes_read_back_ok`/`_failed`).

## Log

- 2026-10-26: Round 7 of `docs/native/native-real-programs-plan.md` (milestone `hih-tools`): `open` and `close` first, the path copied with a NUL into scratch; stat can wait (no target tool needs it). Done when `cat FILE…` matches GNU, diagnostics and exit status included. Probe 2026-10-26: a lone `Opens` is refused by `write-elf` with no reason ([[native-elf-every-program]]).
- 2026-10-28: Round 7 landed: `Opens` and `Closes` compile and are proved inside
  `native_compile_correct` (`lib/native/native_compile_opens.hthr`:
  `Target::goes_closes`, the path copy loop `goes_path_loop` and
  `Target::goes_opens`).
  - **Path semantics.** Linux reads a C string, so an `Opens` now names its
    buffer's first `len` bytes *up to the first NUL* (`List::before_nul` in
    `native_source`; `StatsPath` likewise). The compiled loop copies from the
    buffer to scratch until it has copied `len` bytes (clamped to the
    capacity) or meets a NUL, then stores a NUL after them. The proof's
    invariant is `Target::PathAt` (R8 the count, RSI/RDI the cursors, the
    scratch prefix equal to the path's prefix); `path_ended` turns the
    stored NUL into `CStringAt` for `OpenRequest`.
  - **Scratch is `largest + 1` bytes** (`Layout::stack_offset`), room for a
    full-length path's NUL; `Layout::scratch_below_stack` carries the change
    through the region, args, bytes and calls proofs.
  - **Builder and tool.** `open(path, len, fd)`, `close(fd, result)` and
    `write_span` in `native_build`; `cat_files` in `native_tools` is GNU's
    `cat FILE…` with no options: `-` and no arguments are stdin, status 1
    after any failed open, read or close, "cat: write error: …" and exit 1 on
    a failed write. Each file's errno is kept and one report after it writes
    the diagnostic, its message found by scanning a table in an initial
    buffer (`cat_table`: seven errnos in glibc's C-locale words, then
    "Unknown error", where GNU names any errno and adds the number).
    `crates/cli/tests/native_tools.rs::compiled_cat_files_runs_as_gnu_cat`
    compares stdout, stderr and status against GNU's for files, `-`,
    missing names, a folder (EISDIR from the read), a name too long for
    Linux, and `/dev/full`.
  - **Capacity met on the way.** `write-elf`'s fork read a long entry's
    bytes through left-nested appends and ran out of memory on cat's
    message table: `asm_code_ending_onto` (x86_64_asm_table) conses from the
    back, tied to `asm_code_ending` by a theorem. Then two certificate
    `refl`s ran out of kernel fuel: the builder's lowering of the tool and
    the entry's initial-byte stores. The tool now has one report site and a
    short table, and `List::fits_registers` no longer re-runs the register
    checks `leaf_checks` makes (constant truths of the pool's slices), which
    cut the lowering by about a third. cat FILE fits, narrowly; the fix that
    scales is [[native-tool-certificate-budget]].
  - Not here: GNU's check that an input is not the output (needs fstat) and
    its quoting of odd names. Stat moved to [[native-compile-stat]].
