---
title: One native compiler: join write-elf and compile-x86 before exporting
status: open
labels: [native,design,compiler,memory]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-11
updated: 2026-11-11
---

Minus (2026-11-11): "Unify first and then export." `write-elf` and
`compile-x86` share FunctionIR and the verified lowering of a region and
have grown apart above it. Design and order:
`docs/native-one-compiler-design.md`.

## The three joints

1. A program cannot call a compiled function: `Source` has functions in
   its meaning and `StructuredRegion::code` refuses every `Call` region.
2. Buffers exist on the program side only, compiled by its own byte-node
   code; the function compiler refuses byte nodes.
3. Two kinds of call: System V functions, and `Source` procedures with
   their own convention and global word homes.

## Rounds

- **U1.** `Stack::Wrote` (the stores a call may make) replaces `Unchanged`
  in the function compiler's post; today's `compiled_returns` is its
  corollary. Absorbs [[x86-call-memory-footprints]].
- **U2.** `Source`'s `Call` region compiles to a CALL of a function
  compiled into the same program.
- **U3.** Buffers read through one home ([[function-ir-buffer-state-edges]],
  [[source-buffers-as-views]], [[runtime-default-setup-soundness]]).
- **U4.** Buffers written; `write-elf`'s byte nodes move to the shared
  lowering.
- **U5.** Procedures are functions whose bodies have effects, words in
  frames, a tree-valued claim ([[native-procedure-contracts]]). Its own
  design note first.
- **E.** Export ([[native-library-exports-design]], [[self-lexer-linked]]).
  Needs only U1 and U3; last because that is the order asked for.

## Done when

A `write-elf` program and a linked export are built by the same function
compiler: a program's helper is a `runtime fn` called by CALL, a buffer is
lent to a function by a program and by Rust through the same lowering
case and the same premise, and `Source` has one kind of call.
