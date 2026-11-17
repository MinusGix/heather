---
title: The Linux model named a descriptor by its 64-bit word; the kernel reads 32 bits
status: closed
labels: [native,soundness,machine-model]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
---

`LinuxCmd::sent` and `received` (`lib/std/os/linux/linux_calls.hthr`), and so
`Io::sent`, `sent_to` and every specification built on them, decided whether
a call was to descriptor `fd` by equality of the two 64-bit words. Linux
takes a descriptor as a 32-bit `unsigned int` and never reads the register's
upper half: `write(2^32 + 1, …)` writes to descriptor 1.

So a theorem about what a program sends to standard output could be false of
the process. Repro (before the fix): the echo program of
`lib/_tests/native/runtime/runtime_program_tests.hthr` with its write's
descriptor changed to `BitVec::ofNat(4294967297)` goes through `write-elf`,
the model says it sends nothing to descriptor 1, and the ELF echoes its
input to standard output.

Found by testing the syscall model against the kernel (2026-11-16).

## Fixed

`descriptor(word)` is the word's low 32 bits, and `sent`/`received` compare
descriptors. The events still carry the word the process passed. Theorems in
`lib/_tests/std/os/linux/linux_world_tests.hthr`
(`write_to_upper_half_word_reaches_stdout` and two beside it).

Not changed: `LinuxAsks` still relates a call's `fd` to the whole of RDI, and
an opened descriptor is still a word below 2^31, both of which are exact.
