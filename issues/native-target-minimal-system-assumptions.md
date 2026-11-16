---
title: A compile target that assumes almost nothing of the system beyond ELF loading
status: open
labels: [native,machine-model,design]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
---

Minus (2026-11-16): "we should make so we can target compilation for
extremely limited amount of assumptions about the system beyond loading ELF
files and whatnot". Not urgent. Today a written program's theorem asks what
`LinuxStart` lists (`lib/native/native_compile_elf.hthr`); this target would
shrink that list to the ELF loading rule, the entry address, and the calls
the program makes.

## What would go

- **The kernel's stack.** The program carries its stack inside its own
  `PT_LOAD` segment: `p_memsz` grows by `Source::stack_room`, and the entry
  loads RSP with the top of that room before anything is pushed. `placed`,
  `stack` and the stack limit leave the theorem; the stack rests on the rule
  the data segment already rests on. The entry RSP is still read once, for
  the command line. No guard page: the proof's bound on the depth is what
  keeps the stack off the data below it.
- **The command line**, for a program that takes none: `argv` becomes a
  premise only of sources that read it.

## What would stay, and could be stated more narrowly

- `loaded` and `entry`: the ELF rule itself. Worth saying what it asks
  beyond the headers (the two address ranges free, so a fixed-address
  executable loads).
- The calls: each is answered as `LinuxCmd::Answers` allows. A program that
  only reads, writes and exits needs only those three rules; the theorem
  could name the calls a source makes.
- Signals: either a premise that none is delivered, or a model of the
  default dispositions (SIGPIPE ends the run).

## Notes

- The zero-filled segment is mapped lazily too, so "no growth" does not
  mean "no page faults": it means nothing depends on a limit set outside the
  file.
- Found while auditing the Linux model (`issues/io-stack-below-rsp-not-mapped.md`).
