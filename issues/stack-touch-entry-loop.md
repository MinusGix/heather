---
title: The stack's startup touch as a loop, not unrolled
status: open
labels: [native,machine-model]
area: heather-in-heather
created: 2026-11-17
updated: 2026-11-17
---

The entry code that touches a program's stack room
(`stack_touched_entry(room)`, `lib/std/os/linux/linux_x86_64_stack_growth.hthr`)
is unrolled: sixteen bytes of code for each page of the room. A room of
1 MiB is 4118 bytes of entry code, and since a written file is at most 65535
bytes (`issues/io-elf-file-length-sixteen-bits.md`) a room cannot pass about
15 MiB, less the program. Programs that recurse will want more.

A loop makes the entry code a fixed size: a counter in a register, a
`sub rbx, 4096`, the store and a branch back, then the remainder's one
touch. The proof changes from an induction over the list of strides whose
bytes are laid end to end (`stack_touches_run`, `stack_touches_bytes`) to
one over the count at a fixed address, with `StackTouched`'s list of strides
unchanged: the claim does not say where the code of each touch is.

Unrolled was the first form because every touch is then straight-line code
at an address the list gives, which is the shape the block lemmas already
prove. Raising the file's length limit is a separate matter and would only
move the bound.
