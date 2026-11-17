---
title: A runtime fn main's theorem covers its read loop and exit mapping
status: open
labels: [native,effects,runtime,proof]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-16
updated: 2026-11-16
---

`examples/utf8/utf8check.hthr` proves `utf8_status_answers`: status 0 of the
lent span function means `utf8::is_utf8` of the bytes read. What it does not
state (examples/utf8/README.md, "What the proof does not cover"): that the
read loop fills the buffer with exactly stdin's bytes in order, and that
the ELF's exit status is that verdict. write-elf's certificate already
proves the ELF simulates `main::source`, and `main::bridge` that the source
agrees with the surface program.

## Scope

- A statement over the Io program's trace: for an input stream of at most
  N−1 bytes, `main` exits 0 iff the stream is UTF-8; composed with the
  certificate into a statement about the ELF.
- General: a loop-over-reads lemma (the buffer after the loop is the
  concatenation of the reads) that every reading program reuses.
- Joins the compiler-theorem work (`hih-program-logic`).
