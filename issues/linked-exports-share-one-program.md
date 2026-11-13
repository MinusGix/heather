---
title: Exports that share callees should be one program with several entries
status: closed
labels: [native,exports,linking]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

An export is a program of its own: `compile-x86` compiles one function with everything it reaches and certifies that program. `crates/linked` therefore holds the scanner's automaton twice, once under `scan_step` and once under `scan_token` (which reaches `scan_step`, `scan_accept` and `scan_begin`), and it will hold SHA-256's rounds once for each entry point that reaches them. `scan_token.s` is most of the crate's certified bytes.

It also costs certificates: each export's `_evaluable`, `_quiet`, `_lowers` and emission are checked over its whole program, so a function reached from n exports is checked n times.

## What it would take

- `compile-x86` takes several entry points of one linked program (`EXPORTS.tsv` rows that name the same group), emits the program once, and states one `_returns` for each entry over the one code. `compiled_returns` is already stated at a function index of a program, so the theorem side is a second index, not a new proof.
- The assembly file gets one global symbol for each entry.
- `scripts/linked` groups rows; `generated/exports.rs` does not change shape.

The generator already links by name (`f::program`, `lib/native/runtime/runtime.hthr`; [[runtime-generator-link-cost]] owns what linking costs), so two `runtime fn`s that share callees are one program whenever one reaches the other. The missing piece is two roots that do not reach each other, which needs a program with two roots: either a generator entry that links a list of roots, or `compile-x86` merging two linked programs whose shared functions are syntactically equal.

## Done when

`scan_step`, `scan_accept`, `scan_begin` and `scan_token` are one program in one `.s` file, and the tests in `crates/linked/tests` pass unchanged.

## Log

- 2026-11-12: Built (2026-11-12, PR #551). `docs/native-library-exports-design.md` §6.3 is the record.

  - `compile-x86 <module> <function> --entry <module>::<function>…` compiles the function's program once and exports each entry at its own label, with its own `_returns` in the one certificate. With no `--entry` the output is byte for byte what it was (the eight other exports' files did not change).
  - The generator publishes `f::sources`, `f::sourced` and `f::names` beside `f::program`: every function of the program against its source, and which function is where. The certificate reads `f::sourced` at the entry's index.
  - `compiled_returns_unlent` (`function_ir_compile.hthr`): a function lent nothing, in a program that stores into no span, has the plain contract of a function of words, whatever the root is lent.
  - `EXPORTS.tsv` has a fourth column, the export whose program the row is a function of. `scripts/linked` and `native_linked.rs` compile such rows with their program; `exports.rs` declares them from the signature the program's file states.
  - `scan_step`, `scan_accept` and `scan_begin` are entries of `scan_token`. `crates/linked/generated` has one scanner file where it had four, and `scripts/test -p heather-linked` passes unchanged (50 passed).

  Of "what it would take", the route was the first sentence of the last paragraph: the generator already links by name, so entries the root reaches needed no second root. Two roots that do not reach each other, entries lent spans, entries of a writer's program and the stack bound by index are `issues/linked-program-entries-limits.md`.
