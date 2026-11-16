---
title: The ELF theorem admitted a 65536-byte file, whose header says an empty segment
status: closed
labels: [native,soundness,machine-model]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
---

`io_elf_file` writes the file's length into `p_filesz` and `p_memsz` as
sixteen bits (`BitVec::ofNat(length)`, `BitVec::ofNat(length.shr(8))`).
`Source::elf_file_simulates` asked `232 + code.len() <= 65536`, so it covered
a file of exactly 65536 bytes, whose header states a length of zero. Linux
would map none of that file's code, and the theorem's `loaded` premise (the
file's bytes resident at 0x400000) would be an assumption about a loader that
does not exist. Only the driver's untrusted `MAX_FILE = 65535` kept such a
file from being written.

Found by reading (2026-11-16).

## Fixed

`Source::elf_file_simulates` asks `<= 65535`, and the certificate's
`<source>_elf_short` states that bound. The theorems over an abstract
232-byte header keep the loader window's `<= 65536`, which is theirs.
