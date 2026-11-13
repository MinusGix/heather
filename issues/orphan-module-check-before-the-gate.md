---
title: An orphan library module is found only by the whole-library gate
status: closed
labels: [tooling,testing]
area: infrastructure
created: 2026-11-12
updated: 2026-11-12
---

A new library module that nothing imports fails `every_library_module_is_reached` (`crates/cli/tests/library.rs`), which runs in the whole-library gate at the end of `scripts/test --pr`. That is the one place the rule is checked, so it is found after the full run and costs a second one. It happened with `lib/lang/lexer/lexer_span.hthr` on PR #551: the module was reached only from `crates/linked`'s export table, which is not one of the ways the gate counts.

## What would fix it

- `scripts/lib-closures` (which a round already runs after adding an import) also reports a `lib/` module that no file imports, no `.rs` names and `KEPT_ROOTS` does not list. It has the import graph in hand.
- The gate counts a module named in `crates/linked/generated/EXPORTS.tsv` as reached: an export is a use. A module that is linked should still have probes, so this is the weaker half.

## Done when

`scripts/lib-closures` (no `--fix`) fails on an orphan module with the gate's message, in the seconds it takes now.

## Log

- 2026-11-12: Done by PR #578 (on master 2026-11-12): `scripts/lib-closures` runs the gate's orphan lint with the gate's reading, and `scripts/test` runs it before building.
