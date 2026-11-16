---
title: A linked program's entries: two roots, entries lent spans, entries of a writer, the stack bound by index
status: open
labels: [native,exports,linking]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-16
---

Exports that share callees are one program with several labels since 2026-11-12 (`docs/native/native-library-exports-design.md` §6.3, `compile-x86 --entry`, the fourth column of `crates/linked/generated/EXPORTS.tsv`). What that round left, each refused by name where it applies:

## Two roots that do not reach each other

An entry is a function the root reaches. Two exports that share callees and neither of which calls the other are still two programs, with the shared functions in the crate twice. This needs a program with two roots. Either the generator links a list of roots (a `runtime` entry that takes several functions and publishes one `program`, `sources`, `sourced` and `names` for them), or `compile-x86` joins two published programs whose shared functions are syntactically equal and proves the joined program's `program_linked_files` from the two. The first is less proof and more generator; the second keeps the generator as it is.

No export needs it today: SHA-256's and SHA-512's three word functions share no `runtime fn`.

## An entry lent a span

`compile-x86` refuses an entry whose function is lent a span ("is lent 1 span: … only where it is a function of words"). The theorem is there: `compiled_returns_lent` is stated at any function index, and `f::sourced` gives the agreement at any index and any file. What is missing is text: the entry's `_returns` in the lent form, its `span` kinds in the signature, and which of the root's lending it is stated under. No export asks for it.

## An entry of a program that stores

A writer's group publishes `f::runs_over` at its last function and no `sources`, `sourced` or `names` (`runtime_span` in `lib/native/runtime/runtime.hthr`), and `compiled_returns_unlent` asks that the program is quiet. For a function of words inside a writer's program the statement wanted is the same plain contract, proved from `compiled_returns_run` over a lending that lets the root's span be written, at a file the entry does not touch. `raise_word` inside `raise_span`'s program is the example.

## The stack an entry is stated with

Built 2026-11-16 ([[stack-room-by-call-depth]], then [[function-frame-sized-by-use]]): the room is the frames on the deepest path below the function, by a table the lowering checks. What follows is the analysis as it stood.

`compiled_returns`'s premise was `120 * Succ(f) <= i` (72 before a function could save registers, [[function-frame-sized-by-use]]): room by the function's index in the program, since a function calls only functions before it. For a small function late in a large program that is far more than it uses: `scan_accept`, a few instructions, is stated with the room of every function of the automaton before it. The bound is sound, and Rust's stack makes it harmless in practice, but the `STACK:` figure in `generated/exports.rs` no longer reads as what the function needs. Tightening it is a change to the premise: room by the call depth below the function (a table computed from the program, checked by evaluation), not by its index.

## Done when

Each of the four is either built or decided against, with the refusal messages in `crates/cli/src/native/verified.rs` (`runtime_entries`) updated.

## Log

- 2026-11-12: A second consumer of "an entry lent a span" (2026-11-12): `sha256_init`, `sha256_update` and `sha256_finish` are three exports over one context, and `sha256_compress` a fourth; each is lent a span, so each is its own program and its own file, and the compression function's code is in `crates/linked` three times (about seventy kilobytes of assembly text each for `update` and `finish`). With entries lent spans they are one program with four labels.
