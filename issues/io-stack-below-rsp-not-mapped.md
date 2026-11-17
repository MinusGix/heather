---
title: The process stack below the entry RSP is not all mapped at exec
status: open
labels: [native,machine-model]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
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

## Open: what the assumption should be

- State it as it is: the `depth` bytes below RSP are usable, by mapping or
  by growth, given RLIMIT_STACK leaves that much. Nothing changes but the
  documents (`issues/io-image-process-stack.md`, the design note).
- Or make it true without growth: bound `depth` by what exec leaves mapped
  for a bounded command line and environment, which needs envp in the model.
