---
title: The Linux model promised the arithmetic flags back after a syscall
status: closed
labels: [native,machine-model]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
---

Every answer of `lib/std/os/linux/linux_x86_64_io.hthr` resumed the process
with `flags := state.flags`: the six arithmetic flags as they were before the
SYSCALL. Linux on x86-64 does that today (SYSCALL copies RFLAGS to R11 and
the return restores it), but the written call convention names only RCX and
R11 as destroyed and promises nothing about the flags, and a Linux-like
environment (an emulator, a compatibility layer) need not do the same. The
model is to rely on what Linux guarantees, not on what it happens to do
(Minus, 2026-11-16).

Not a flaw any program met: the compiler's blocks never read a flag they did
not set (`blocks_read_own`), so no compiled code carried a flag across a
call.

## Fixed

Every answer resumes with `syscall_flags()`: each flag undefined
(`DefinedFlags::none()`), written False as an instruction's undefined flags
are. A step that reads an undefined flag does not exist, and
`SameDefinedState` erases them, so no theorem can depend on the value. The
whole `cat` pipeline (`native_cat_executable`) and the weakest-precondition
and determinism modules check unchanged against the stricter rule.
