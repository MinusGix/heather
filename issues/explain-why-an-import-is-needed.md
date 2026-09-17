---
title: Answer "what does this import contribute" without deleting it and re-checking
status: open
labels: [tooling,modules,elaboration,diagnostics,ergonomics]
created: 2026-09-16
updated: 2026-09-16
---

`docs/showcase/calc_parser.hthr` imports `pair`, `int` and `omega` and names
none of them; all three are required by the mutual `decreases` machinery
([[feature-implicit-module-dependencies]]). Establishing that took three
separate `heather check` runs, one per import, each removing a line and reading
the refusal — about ten minutes of round trips for a fact the elaborator knew
the whole time.

The missing capability is the *inverse* of the unused-import lint: not "which
imports contributed nothing", but "what did this import contribute". Same
table, read the other way.

```
$ heather explain-import docs/showcase/calc_parser.hthr omega
omega: required
  - mutual `decreases` group {checked_expr, checked_factor, checked_atom}:
    flattened-measure obligations are stated over omega
  - no name in this module resolves through omega
```

Shape questions to settle when picked up: whether this is a flag on `check`, a
sibling of `obligations`/`axioms` (which are already the read-only inspection
commands and already take `-L` and the cache), or output of `--fix`-less lint
mode; and whether "required" needs to distinguish *this module uses it* from
*a feature this module uses is stated over it*, which is exactly the
distinction [[feature-implicit-module-dependencies]] wants to erase.

## What it assumes from elsewhere

- **[[lint-unused-imports]]** owns the module-finalization phase that records
  which module supplied each successful resolution, instance search and
  designation. Assumed here: only that this record exists and is complete
  enough to be read forwards as well as backwards — if it is, this issue is a
  presentation layer over it and should not be built separately.

## Log

- 2026-09-16: Filed from the `calc_parser.hthr` pass, where the three imports
  were confirmed load-bearing by deletion probes.
