---
title: A program builder that lowers named, structured programs to the effectful source
status: open
labels: [native,frontend,ergonomics]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-26
---

Round 5 of `docs/native-real-programs-plan.md` (§3.3, §5, §6). A `Source`
is written as a hand AST over numbered words (`lib/native/native_cat.hthr`).
A leaf holds at most 14 values and may not write a word it reads, and loops
test bits the program sets itself. No real tool can be written this way.
The decided surface (uniqueness threading, [[effects-direction]]) is a
language round. This round builds the layer it will target.

## Scope

- `lib/native/native_build.hthr`: a structured program type with named words
  and buffers, expressions, `let`, `if`, `while`, `for` over a buffer's bytes,
  `read`/`write`/`exit`, and procedures inlined at build. A Heather function
  lowers it to a `Source`. It allocates ids, splits expressions into leaves
  that fit the register pool, adds temporaries for in-place updates, and
  makes the bits `Branch`/`Repeat` test. No proof: a tool's meaning is the
  `Source` it lowers to.
- Pure helpers written as ordinary Heather word functions, inlined as their
  reflected FunctionIR regions (the `compile-x86` reflector,
  `crates/elab/src/function_ir_source.rs`), with the reflector's agreement
  certificate.
- `write-elf` evaluates the lowering on its fork and states
  `<s>_lowered() = literal` by `refl`, then compiles the literal, so the
  builder's evaluation is not part of the emission check.

## Done when

`tr` and `head -c N` are rewritten in the builder, and a `wc -l` that
reports its count as the exit status builds and runs.

## What it assumes from elsewhere

- **[[native-source-bytes]]** owns the byte nodes the builder emits.
- **[[native-compile-wider-leaves]]** owns the region forms (conditionals,
  bounded loops) an inlined helper lowers to. Until it lands, the builder
  emits only dataflow leaves.
- **[[effects-direction]]** owns the eventual surface, which elaborates into
  this builder or straight into `Source`.

## Log

- 2026-10-26: [[native-source-bytes]] landed: the nodes are `BufferLoad(output, buffer, index)` and `BufferStore(output, buffer, index, value)`, and until [[native-compile-wider-leaves]] splits leaves, each must be a `Compute` leaf of its own (a leaf mixing them with pure nodes is refused). `lib/native/native_tools.hthr`'s tr is the hand-written shape.
