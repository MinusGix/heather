---
title: Exports that share callees should be one program with several entries
status: open
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
