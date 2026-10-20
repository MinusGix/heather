---
title: Tests re-elaborate library modules from source: list in 109 tests, nat in 182, the x86 structured block in 14
status: open
labels: [performance,testing,tooling]
area: infrastructure
created: 2026-09-23
updated: 2026-10-11
---

Tests elaborate the same library modules from source over and over. The
suite-wide declaration rows (`HEATHER_SUITE_DECLS=1 scripts/test --fast`,
run 2026-09-23; aggregated in the snapshot after it, dashboard section
"What the suite elaborates") count, per module, the tests whose threads
elaborated it:

| module | tests | binaries | seconds summed |
|---|---|---|---|
| `list` | 109 | 25 | 62.8 |
| `x86_64_structured_block` | 14 | 10 | 30.3 |
| `nat` | 182 | 33 | 21.0 |
| `int` | 20 | — | 6.9 |
| `logic` | 200 | — | 3.5 |

Out of 524 s of test time in the fast lane, and 406 s inside declarations.
A replayed image leaves no declaration rows, so these are genuine
re-elaborations: `include_str!` of `lib/std/list.hthr` into
`elab_module_source` per test (e.g. `lib_std_string` 6 tests / 10.5 s,
`lib_std_list` 10 / 8.0 s, `char_string_literals` 5 / 5.8 s, `nat_order`
17 / 4.6 s), and the `function_ir_*` binaries elaborating
`x86_64_structured_block` after their shared base image
(`function_ir_byte_read` 3 tests / 7.7 s, `function_ir_recursive_certificates`
3 / 7.4 s, six more at ~2.2 s each).

Levers, cheapest first:

1. **`x86_64_structured_block` into the replayed prefix** those binaries
   already share (`common::base_image` in `crates/elab/tests/function_ir_x86.rs`
   and the semantic warm-up in `scripts/test`). Most direct: 30 s of repeats
   of one module in binaries that already use images.
2. **A per-binary fixture**: elaborate the library prefix once per binary
   (a `OnceLock` of a checked elaborator, `fork()` per test — the pattern
   `base.fork()` already follows) instead of once per test.
3. The semantic-image replay for the `lib_std_*` binaries, like the x86 ones.

Danger: a test whose *point* is to elaborate the module (the `lib_std_*`
binaries check their module) must keep one test doing it from source; only
the others should fork. And the fast lane's contract (CLAUDE.md) is that
replayed images are vouched for or rechecked, so option 3 inherits that
rule, not a new one.

Trigger: any time the fast lane's summed time matters — it is ~12 % for
`list` alone. Wall-clock is dominated elsewhere (the lane's critical path is
one test; see [[fast-lane-heaviest-declarations]]).

## Log

- 2026-09-23: 2026-09-23: **Lever 2 landed** — `support::library(modules)` (`crates/elab/tests/support/mod.rs`): the module list elaborated from source on the prelude **once per test process** (current frontend, real kernel, no image replay — the same checks as the hand loops), each call a fork of its `SemanticImage`. Eighteen binaries converted (`lib_std_{string,list,tree,relation,order,bounded_list,certified_lookup,location}`, `char_string_literals`, `nat_{order,arith,parity,run_primitives}`, `logic`, `lib_list_algos`, `binder_symbol_notation`, `operators_onto_classes`, and `lib_std_int`'s probes — its module test keeps its own review-lint elaboration). Fast lane: library modules re-elaborated in test threads 125 s → 49 s summed (`list` 64 → 18 s), lane summed 271 → 223 s, CPU 360 → 266 s, tests wall 41 → 34 s; 2759 passed. Full lane 2916 passed, 95 s tests wall, 855 CPU-s. Lever 1 is moot: `x86_64_structured_block` is 4 s summed since [[elaborator-canonical-type-spelling]]'s constructor fix (was 30 s). Not converted (other shapes, ~3 s each): `radix_numerals`, `lib_algebra`, `operation_indexed_classes`; `lib_setoid_mergeable`'s 9 s is `omega`/`tree_finite_set` in its own module tests.
- 2026-10-11: Recurred with the wc command's library tests (C1–C4): ~545 s of a warm fast lane on a 4-CPU box was library modules re-elaborated per test. Converted through the read-loop fixture's `checker_with` (semantic image replay of each test's own module list); see [[suite-iteration-chokepoints-2026-10]].
