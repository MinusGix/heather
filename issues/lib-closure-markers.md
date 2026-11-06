---
title: Mark the remaining hand-written module lists for lib-closures
status: open
labels: [testing,tactics]
area: infrastructure
created: 2026-11-06
updated: 2026-11-06
milestone: [tac-general]
---

`scripts/lib-closures` writes a Rust module list marked `// lib-closure:
<roots>… [minus <roots>…]` from the imports, and
`crates/cli/tests/lib_closures.rs` holds every marked list to the loader
([[grind-closure-cost]] built both and marked the bundled proof library, the
x86 prefix, the read loop, `lib_std_float`'s list and `x86_64.rs`'s fetch
probe). The rest of the hand-written lists are not marked: about forty test
files list `int` with its closure, and `x86_64.rs`'s `X86_MODULES`,
`semantic_x86_warmup.rs`, the omega and ring lists and the `linux_*` extras
copy prefixes by hand.

Marking them is one line each where the list is a closure, and a decision
where it is not (a list holding modules nothing it holds imports, or in an
order a test depends on). It is also what a grind conversion in `int` (about
forty lists) or `x86_64` (the x86 prefix) needs before it is a one-line edit
plus `scripts/lib-closures --fix`; whether such a conversion is affordable is
[[grind-closure-cost]]'s question, not this one's.

## Done when

Every Rust list of library modules is either marked or says why it is not a
closure.

## What it assumes from elsewhere
- **[[grind-closure-cost]]** owns the marker format and the script. Assumed
  here: only that `scripts/lib-closures --fix` and the loader test exist.
