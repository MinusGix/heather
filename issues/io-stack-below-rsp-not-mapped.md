---
title: The process stack below the entry RSP is not all mapped at exec
status: closed
labels: [native,machine-model]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-17
---

`StackPlaced` lets a process rely on up to 128 KiB (`io_stack_limit`) of data
below its entry RSP, and the model's comment justified that by exec mapping
at least 128 KiB below RSP before the program runs, "never the growth".
That is not what exec does. `setup_arg_pages` reserves 128 KiB below the
argument strings; `create_elf_tables` then puts argc, the argv and envp
pointers and auxv below the strings, inside the reserve. Measured on the
written `cat` at its first instruction (gdb `starti`, `info proc mappings`):

| environment | mapped below RSP |
|---|---|
| empty | 134592 bytes |
| 2000 variables | 115984 bytes |
| 20000 variables | 2304 bytes |

The programs run all the same, because a touch below the mapping faults and
the kernel grows the stack (to RLIMIT_STACK). So the assumption holds of real
processes only through growth, which the model said it did not use. A process
started under a stack limit smaller than its `depth` plus its command line
and environment would fault where the theorem says it runs.

The comment in `lib/std/os/linux/linux_x86_64_image.hthr` now says this.

## Decided (Minus, 2026-11-16): state the premise directly

The assumption stays the kernel's stack, and the theorem says so:
`LinuxStart` (native_compile_elf) carries the stack room as a field, with
the stack limit named as what grants it, and `StackPlaced` lost its 128 KiB
cap, which rested on the mapping exec was thought to make
(`issues/elf-theorem-runtime-premises.md`). A target that owns its stack
inside its own segment, and so asks nothing of the limit, is
`issues/native-target-minimal-system-assumptions.md`.

## Superseded (2026-11-17): the program owns its stack

Minus asked to improve on the stated premise, so the premise is gone: a
written program's stack is in its own data segment
(`DataRegion::own_stack`), `X86Profile::process` and `StackPlaced` are
deleted, and nothing is asked of the kernel's stack but the command line
(`issues/native-target-minimal-system-assumptions.md`).
