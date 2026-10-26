---
title: Give every written ELF its theorem, its fits check and its refusal reason
status: open
labels: [native,cli,proofs,ergonomics]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-26
---

Round 3 of `docs/native-real-programs-plan.md` (§3.6, §6). Found by building
probe programs with `write-elf` (2026-10-26):

- `write-elf` never checks that the layout fits the region. `cat(2048)`
  (words, buffer and scratch past the 4 KiB page) was written and runs, but
  `native_compile_correct` takes `fits` as a hypothesis and no theorem covers
  that file.
- Only cat has its behavioural theorem (`cat_native_simulates`,
  `lib/native/native_cat_compiled.hthr`), written by hand, though nothing in
  it is about cat beyond names.
- A refused program says only ``did not compile, or its items' lengths did
  not read back``. `opens` (an `open` call) and a 15-node leaf both got
  exactly that message.
- A program file must import the certificate's modules (`native_compile`,
  `native_compile_correct`, …) or `write-elf` fails on an unknown module.

## Scope

- A library theorem, the generic form of `cat_native_simulates`: any
  `Source` whose compile at the I/O page is `Some(code)` and whose layout
  fits, loaded past a 232-byte header, simulates its tree. `write-elf`
  states `<s>_elf_simulates` from it, and checks `fits` by evaluation, in
  every certificate.
- An untrusted `Source::refusal` (or a Rust-side walk) that names the first
  statement the compile refuses and why: the call kind, a word id past the
  slots, a leaf's width, or a region form. `write-elf` prints it when the
  compile is `None`.
- `write-elf` adds its own imports to the probe and certificate closures.

## Done when

`head -c 10` gets `head10_elf_simulates` with no per-program proof, `big_cat`
is refused for not fitting, and `opens` is refused with a reason.

## What it assumes from elsewhere

- **[[native-effect-source-compiler]]** owns `native_compile_correct`.
- **[[native-cat-executable]]** owns `write-elf`.
