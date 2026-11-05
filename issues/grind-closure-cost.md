---
title: Importing grind costs its closure in every hand-written module list
status: open
labels: [tactics,testing]
area: tactics
milestone: [tac-general]
created: 2026-11-05
updated: 2026-11-05
---

Importing `grind` into a library module is cheap for `heather check` (images
are per module) and expensive wherever a module closure is written by hand:
`compile-x86`'s bundled proof library (`crates/cli/src/native/support.rs`)
and the Rust tests' module lists (`crates/elab/tests/support/read_loop.rs`,
`support/x86_prefix.rs`, `lib_std_float.rs`, and some forty lists holding
`int`). Each list holding an importer must also hold grind's closure past
`list` (`char`, `string`, `tactic`, `derive`, `egraph`, `grind`), and cold
that closure's elaboration (dominated by `grind`, then `tactic`) is a large
share of a test's CPU rail. The grind constructor-facts round converted
`x86_64_fetch`/`_data_read`/`_stack` (on the bundled path) and
`native::tests::the_bundled_library_checks` was killed at its CPU rail on
the first run after a compiler change, so those conversions were taken
back (docs/grind-design.md §14.5).

Two directions, either of which would let Minus's 2026-11-05 decision
(grind anywhere its imports allow) stand in practice:

- Generate the lists from the import graph (the loader already resolves
  closures; `support.rs` says "in import order", which is a computed fact
  copied by hand), so adding an import is not a multi-file edit.
- Make grind's own module cheaper to elaborate: measure where its
  elaboration goes (`--timings` on `lib/std/tactic/grind.hthr`), since it is
  the largest single share.

The reverted conversions are one-line edits: `Option::some_inj(…, trans(sym(a), b))`
→ `by grind()` / `grind_with([…])`, `absurd(trans(sym(h), e))` → `by
grind_with([e])`.

## What it assumes from elsewhere
- **[[grind-constructor-facts]]** owns the conversions. Assumed here: only
  that they close with grind once the closure is affordable.

- 2026-11-05: A second cost, inside a module: with `itree`/`coitree` imported, every grind call in `grind_tests` took several times longer (the same kernel steps; a trivial call's time unchanged without them), which put that probe module over its CPU rail. The codata probes moved to `grind_codata_tests`. Not yet measured where it goes (name resolution or `Lookup` over the larger scope are the first suspects).
