---
title: Early return from a mut self method
status: closed
labels: [language,effects,frontend]
area: language
milestone: [lang-sequencing,nh-effects]
created: 2026-11-02
updated: 2026-11-02
---

A `mut self` method cannot `return` early. The parser refuses it with "`return` is not supported in a `mut self` method yet: its receiver goes back out beside the result, which an early exit would skip" (`crates/syntax/src/parser.rs`). So effectful code that should stop at a failure carries a flag out of the loop instead. `Io::read_lines` in `lib/native/runtime/line_tools.hthr` sets `failed := True; break` and then matches on the flag after the loop. Minus raised this reviewing PR #394 (2026-11-02).

## Scope

- `return e` in a `mut self` method returns `Mutated(<receiver as it stands>, e)`. That holds inside a `for` body (as a `ForStep::Return` carrying the receiver in the state, `docs/sequencing-surface-design.md` §15), inside statement `if`/`match` arms, and in tail position.
- The receiver at the `return` is the one the block has threaded so far. The lowering already threads it as loop state, so the `Return` leaf reads it from the state.
- A `return` from a nested or conditional loop is refused today for pure code too (`imperative-statements-built`). This issue does not lift that; it makes `mut self` match pure code.

## Done when

`Io::read_lines` is written with `ReadFailed(_) => { return None }`, it checks against the same literal probes (`lib/_tests/native/runtime/line_tools_tests.hthr`), and a probe pins a `return` inside a `for` in a `mut self` method at a neutral world.

## Log

- 2026-11-02: Built: the parser wraps each returning loop's `\0ret(e)` leaf in `Mutated(x, e)` over the receiver as threaded there (crates/syntax/src/imperative.rs `return_receiver`, sequencing design §15.7). `Io::read_lines` returns `None` at a failed read; probes: `read_lines_fails` at a neutral history (line_tools_tests), `tick_nonzero_*`/`tick_unless_zero_*` at a neutral receiver (imperative_statements_tests). Return outside a top-level loop stays refused as in pure code.
