---
title: Tests re-elaborate library modules from source: list in 109 tests, nat in 182, the x86 structured block in 14
status: open
labels: [performance,testing,tooling]
created: 2026-09-23
updated: 2026-09-23
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
