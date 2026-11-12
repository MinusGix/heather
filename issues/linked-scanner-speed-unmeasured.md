---
title: Measure the linked scanner against the Rust lexer before the switch
status: open
labels: [native,lexer,perf]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-11-12
updated: 2026-11-12
---

The Rust scanner calls compiled Heather once for each token (`scanner::token`, [[self-lexer-linked]]), and nobody has timed it against `heather_syntax::lex` or against the Rust loop it replaced (kept as the reference in `crates/linked/tests/scanner.rs`).

What to expect, unmeasured: slower. There is no optimizer, the automaton's step is a called function inside the loop, every call saves and restores, a byte read is a compare, a branch and a load, and the loop's state moves between registers on every pass ([[function-ir-planner-register-pressure]]).

This matters for [[self-lexer-linked]]'s last step, the switch in `heather_syntax::lex`: a lexer several times slower is a cost every `heather check` pays.

## What to do

- A case in `scripts/bench` (or `perf/bench/cases.tsv`) that scans every `lib/**/*.hthr` through the linked scanner and through `heather_syntax::lex`, reporting bytes a second for each. Counters first: instructions for a token, from `perf stat` or callgrind.
- Read the loop's assembly once with the numbers beside it and file what dominates as its own issue (inlining of a small callee, the bounds test hoisted under `InBounds` facts, moves at the loop's back edge).

## Done when

The ratio is a number in `perf/`, and the switch's issue says whether it is acceptable or names what must be fixed first.
