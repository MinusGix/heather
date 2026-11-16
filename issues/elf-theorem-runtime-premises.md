---
title: The ELF theorem's run-time premises under one name
status: closed
labels: [native,machine-model]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
---

What a written program's theorem relies on when it is run should be explicit
in the theorem (Minus, 2026-11-16: "`ulimit` is not an esoteric piece, we can
rely on there being space on the stack but that should be a part of the
theorem ideally. And so on for other parts."). It was spread over five
premises of `Source::elf_file_simulates` and the type of its memory, where
the stack's usability was a reliance of the profile and appeared in no
premise.

## Done

- `LinuxStart(size, file, top, room, args, s)` in
  `lib/native/native_compile_elf.hthr`: the file loaded as its headers say,
  the entry, RSP and its placement, the stack room below RSP as data (with
  the stack limit named as what grants it), and the command line. Its
  comment says what is not asked and what is not modelled.
- `Source::stack_room` names the room, `Source::elf_file_runs` is the theorem
  from `LinuxStart`, and every certificate states `<source>_elf_runs`.
- `StackPlaced` no longer caps the depth at 128 KiB.
- The flags are undefined after a system call
  (`issues/linux-syscall-flags-not-promised.md`).
- `docs/native/compiler-theorem.md` lists the premises.

## Left

- The answers Linux gives during the run are in the simulation relation
  (`LinuxAnswered`), not in `LinuxStart`: a reader finds them in
  `linux_x86_64_io`. A signal is not modelled at all.
