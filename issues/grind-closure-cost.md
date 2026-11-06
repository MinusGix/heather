---
title: Importing grind costs its closure in every hand-written module list
status: open
labels: [tactics,testing]
area: tactics
milestone: [tac-general]
created: 2026-11-05
updated: 2026-11-06
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

## Log

- 2026-11-06: Both directions (docs/grind-design.md §14.6). Measured with `--timings` at
  width one: the closure's cost was the kernel gate re-checking `Tac`
  constructor values, which spell `Tac`'s `W` encoding at every occurrence
  (about 20k kernel steps for a probe's `Pure(1)`, about 2.7k through a
  one-line function), multiplied by wildcard arms over `Head`/`Req`. Tactics
  now build values through `pure`/`ask`/`ask_then` and read views through
  plain functions; every module importing `tactic` was rewritten. Cold
  elaboration of grind's closure (release, width one) went from about two and
  a half minutes to just over one. The elaborator fix is
  [[tier2-constructor-value-cost]].

  The lists: `scripts/lib-closures` regenerates every list marked
  `// lib-closure:` from the imports, and `crates/cli/tests/lib_closures.rs`
  holds each to the CLI's loader. Marked: the bundled proof library, the x86
  prefix, the read loop, `lib_std_float`. The conversions were replayed and
  all check, but the bundled-library check then took about 216 s cold of its
  300 s rail against master's 36 s: grind's closure about 105 s, and about
  33 s of image recheck at each of `x86_64_fetch` and `x86_64_data_read`,
  where grind's chain meets the x86 chain. So they stay out
  (docs/grind-design.md §14.6), and this stays open for what is left: the
  recheck when two chains merge (the bundled session has no verdict store;
  find whether relocation must re-check at all,
  docs/module-interface-cutoff-design.md), and the closure itself
  ([[tier2-constructor-value-cost]]). The lists past these four are
  [[lib-closure-markers]]. Not looked at: the second cost (itree in scope slowing every
  grind call), now [[grind-scope-size-cost]].
