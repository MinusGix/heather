---
title: Write cat's compiled bytes as an executable and run it
status: closed
labels: [native,x86,linux,testing]
area: heather-in-heather
milestone: [hih-pl-first-program]
created: 2026-10-25
updated: 2026-10-25
---

`cat_native_sends` (`lib/native/native_cat_compiled.hthr`) is about the
process Linux makes of a 232-byte header and cat's bytes
(`X86Memory::io_load`, `lib/std/os/linux/linux_x86_64_image.hthr`), but no
such file is written or run: the header that loader models (an RW segment of
eight zero KiB at 0x410000 after the code at 0x400000) has no builder in
`lib/std/os/linux/elf64.hthr`, whose `static_elf64_header` has one segment.
The module comment of `linux_x86_64_image` still names an `io_elf_header`
that does not exist. Found while proving S3.2
([[native-effect-source-compiler]], 2026-10-25).

## Scope

- The I/O header as a Heather function, with a theorem that Linux's loading
  of it is `X86Memory::io_load` (or the loader model restated over it).
- `compile-x86` (or a test) writing `header ++ cat_bytes()` to a file, and a
  test in `crates/cli/tests` running it on a few inputs against `cat`.

## Log

- 2026-10-25: Done. `io_elf_header`/`io_elf_file` are back in
  `linux_x86_64_image` (header length 232 by `refl`); the loader model is
  unchanged, and that Linux maps those headers as `X86Memory::io_load` says
  stays the environment's assumption. `lib/native/native_cat_executable.hthr`
  states `cat_file_sends` over `io_elf_file(cat_bytes())`. `heather
  write-elf <file> <source> -o <out>` compiles a nullary `Source` at the
  page, reads the program back (`Prog::numbers`, moved to `x86_64_asm`, now
  with the memory items and SYSCALL), and has the kernel check
  `<source>_elf_compiles` (the emission by `refl` against the literal, the
  layout in stretches, joined by the new `Source::compile_of`) and
  `<source>_elf_written` (the bytes a piece at a time, then the header)
  before writing the file 0755. One compile is ~770k of a declaration's
  ~1M steps (~220k emitting, ~550k checking layout), which is why the
  compile is never repeated in one statement; the literal spells region
  addresses `next_rip(DataRegion::io_page().low, o)` as the compiler does,
  so the emission's check compares them by their arguments (~1.5k steps)
  instead of their bits. `crates/cli/tests/native_cat.rs` runs the file:
  empty input, a line, 5000 bytes of every value, a full stdout (exit 1)
  and a directory as stdin (exit 1). cat runs at `cat(256)`: at 1024 the
  scratch address is past the kernel's evaluation depth, filed as
  [[native-compile-address-depth]].

