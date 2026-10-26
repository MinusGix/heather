---
title: Compile open, close and stat in the effectful source's compiler
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-pl-source, hih-tools]
created: 2026-10-25
updated: 2026-10-26
---

`Prog::call` (`lib/native/native_compile.hthr`) compiles `Reads` and
`Writes`; `Opens`, `Closes`, `StatsPath` and `StatsFd` are refused. Found
while proving S3.2 ([[native-effect-source-compiler]], 2026-10-25).

## Scope

- `Closes` and `StatsFd`: operands from word slots, the result stored as
  `goes_writes` stores it (`lib/native/native_compile_calls.hthr`).
- `Opens` and `StatsPath`: a path read from a buffer, so the call's command
  names bytes in the region (`Target::span_cells` gives them).
- `StatsPath`/`StatsFd` land a stat record in a buffer; whether Linux may
  leave the range written on failure decides whether they land in the
  scratch range and copy, as a read does (`goes_read_back_ok`/`_failed`).

## Log

- 2026-10-26: Round 7 of `docs/native-real-programs-plan.md` (milestone `hih-tools`): `open` and `close` first, the path copied with a NUL into scratch; stat can wait (no target tool needs it). Done when `cat FILE…` matches GNU, diagnostics and exit status included. Probe 2026-10-26: a lone `Opens` is refused by `write-elf` with no reason ([[native-elf-every-program]]).
