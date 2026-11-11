---
title: A real one-line elaborator edit still recompiles the crate's shared Vec unit
status: open
labels: [performance,build,tooling]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

After [[elaborator-crate-compile-per-edit]] a one-line elaborator edit recompiles `heather-elab-lib` in 13 to 17 s when it adds a line and in 5 to 7 s when it keeps the line's length. The difference is one codegen unit: the crate's `Vec<T>` code.

## Measured

Four-core cloud box, 2026-11-11, `cargo build -p heather-elab-lib` after an edit in `crates/elab/src/wf.rs`:

| edit | rebuild | objects written |
|---|---|---|
| other letters in a string, same length | 4.9 s | 1 (0.6 MB) |
| the string two characters longer | 14.5 s | 2 (7.2 MB) |
| one comment line added above it | 13.4 s | 2 (7.2 MB) |

`scripts/codegen-units` on that build: `alloc::vec::Vec` 8.2 MB (1,330 functions), `core::iter::adapters::map::Map` 6.6 MB, drop glue (`core::ptr`) 5.1 MB, `hashbrown::raw::RawTable` 2.7 MB, the B-tree nodes 2.4 MB; the largest unit of the elaborator's own code is 2.0 MB.

rustc groups generic instances by the generic's own module, so every `Vec<T>` method the crate instantiates is in one unit, whichever function asked for it. An edit that moves the spans of a closure (anything after the edit in the same function) changes the instances built from that closure, and the unit they are in is compiled again whole, on one core.

## Directions

1. Find which instances carry the unit: `nm -S -C` on its object, grouped by element and closure type. A few hot shapes (`.iter().map(closure).collect::<Vec<_>>()`) may be most of it.
2. The unit tests: `heather-elab-unit` compiles the same sources beside the library, so each edit pays twice ([[elab-unit-tests-wait-on-cli-dev-dependency]] is why it is a package of its own).
3. The 3,300 lines of methods still on `Elaborator` (shared helpers, `display.rs`, `access.rs`): an edit there is 31 s for the test binaries, against 22 to 24 s in a view.
4. Whether a nightly-only flag changes the picture is worth one measurement, to know what stable is missing, not to adopt it.

## Done when

A one-line elaborator edit that adds a line recompiles the library in under ten seconds, or the unit's cost is shown to be the floor.
