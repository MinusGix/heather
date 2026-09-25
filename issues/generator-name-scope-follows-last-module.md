---
title: Generators resolve source names in whatever module was checked last
status: open
labels: [compiler,x86,elaboration]
created: 2026-09-25
updated: 2026-09-25
---

The native producer's generators (`read_loop::generate_loop`,
`generate_format`) resolve source functions with `Elaborator::global_abs`,
which answers from the name scope of whichever module the session checked
last. Run `generate_format` after checking a module that does not import
`decimal_line`, and `decimal_line::line_word` fails with "unknown source
function", qualified spelling and all. The round fixed this by ordering:
generators run immediately after the context check, and the context imports
`decimal_line` whenever `--bound` is set (`crates/cli/src/native.rs`,
2026-09-25).

Order-dependence of that kind is a trap for the next generator, and for a
Heather-side generator even more ([[scoped-declaration-generators]]).

## Scope

Give generators a lookup that resolves a qualified name against the checked
global environment, not the last module's scope. Or name the scope
explicitly: resolve as if in module `M`. The latter matches what a
certificate's text will be checked in. A base name should still resolve per a
named scope, never per history.

## Acceptance

- `generate_format` works when called after an unrelated module's check, in a
  test.
- `native.rs`'s ordering comment goes, or states a reason that is not the
  lookup.

## What it assumes from elsewhere

- **[[host-elaboration-interface]]** owns the Heather-facing version of the
  same interface. Assumed there: only that it resolves names against an
  explicit scope.
