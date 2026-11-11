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

## Log

- 2026-11-11: U1 built: `Stack::Own`/`Stack::Wrote` in x86_64_stack.hthr; `CalleePost` and `Framed` state the stores; `wrote_unchanged`, `wrote_resident` and `compiled_returns_keeps` are the corollaries; no emitted byte changed. Next is U2.
- 2026-11-11: U2 built: a `Source`'s `Call` region compiles to a CALL of a function the function compiler emits after the program's own code (`Prog::function_call`, `Prog::links`, native_compile.hthr; R10 carried in RBX across the call, so no allocator changes). The call is proved from the function's contract (`Target::functions_run`, native_compile_function.hthr: `Site::moves_call` on `Returns`, `Target::Held` kept by `Wrote`), and `native_compile_correct` covers a source with functions, with or without procedures; its stack premise gains a term per function. `write-elf` spells the functions in the literal (`Source::spelled` tag 3), carries the placement of their values in the homes (`Homes.places`, from `plan_program`) and states the linking as one equation. Runs: tr through a called function beside GNU's, a tool calling a `runtime fn` that calls another, a procedure and a function in one file (crates/cli/tests/native_tools.rs). Refusal reasons 16 and 17 name a call that does not fit and functions that do not link. Limit kept: the functions' linking is one statement in the certificate, so a called function is as large as one declaration lowers ([[native-function-emission-in-parts]]). Next is U3.
