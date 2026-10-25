---
title: Write cat's compiled bytes as an executable and run it
status: open
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
