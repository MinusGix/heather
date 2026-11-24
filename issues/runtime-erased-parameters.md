---
title: Proof and erased parameters of a runtime fn, so an access carries its obligation into compiled code
status: open
labels: [ownership,native,runtime-fn]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

An access that carries its obligation has to compile (vision principle 13; `docs/language/ownership-design.md` §10.6). Today the reflector drops only trailing squashed arguments of a call, and a `runtime fn` of a laid record that takes a proof parameter is refused ("a type with no runtime layout"), which is why the arena's window `read` and `store` (`lib/native/runtime/arena.hthr`) are ordinary functions. This is the proof-parameter item of [[runtime-record-function-limits]], taken as its own round with a second half.

## Scope

- **Proof parameters of a `runtime fn`, in every shape the generator has** (pure, span, `Bytes(n)`, laid record): a parameter whose type is a proposition is erased wherever it stands, the callee's meaning and published agreement are stated under it, and a caller's found proof (`:= bv_omega`) is checked where the call is written and dropped from the code.
- **Erased data parameters**: a parameter marked as having no runtime presence (a generation, a region's token), erased the same way, and refused where the code would compute with it.
- **The customer**: the arena's `read` and `store` become `runtime fn`s keeping their found proofs, with their ledger rows (`lib/_tests/native/runtime/runtime_ports_tests.hthr`).
- Controls: a function that branches on an erased parameter is refused by name.

## Done when

The arena's `read` and `store` are compiled `runtime fn`s with their agreements published, a call with a found proof compiles to code with no trace of it, and the refusals are pinned.

## What it assumes from elsewhere

- **[[runtime-record-function-limits]]** owns the other limits of laid-record functions.
- **[[loops-on-one-combinator]]** owns the loop modules its round 4 moves; this issue stays out of them and says which loops over an erased parameter wait.
