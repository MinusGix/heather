---
title: Check a block's unused let values at the block's depth, not one binder deeper each
status: closed
labels: [elaboration,performance,proofs]
area: language
created: 2026-10-26
updated: 2026-10-26
---

A block's unspliced `let` values are checked by wrapping the rest of the
block around each one as `(λ _: T. rest)(v)`
(`statements::LetValue::discard_around`, `docs/language/let-and-blocks-design.md`
§11). Each wrap puts everything after it under one more binder. So a block
with `k` unused proof lets, each about the shared value chain before it,
reaches the gate with the chain at `k` depths: each depth is a separately
shifted copy, and the kernel's typing memo
([[kernel-typing-memo-on-node-identity]]) judges a node once per *scope*,
so it checks each copy once. That is quadratic in `k`.

The 2026-10-26 measurement (release, width one, `--timings` queries) on the
anchor issue's `dep` family (a proof `let p_i: (s_i = mix(s_{i-1},
s_{i-1})) = refl` after every link, none used): 868 / 2,756 / 9,604 at
k = 16 / 32 / 64, ×3.5 per doubling. The same chain with one proof `let`
at the end is linear (148 / 276 / 532). Before the typing memo, `dep` was
2^k (2.9M queries at k = 16).

## Options

- **Taken:** no binder over the body at all, `(λ _: T. λ b: B. b)(v)(body)`
  per value, so only `B` is shifted (once per block).
- Check all of a block's unspliced values under **one** binder: a single
  redex whose argument carries every discarded value (a Σ of them, or one
  application of a `k`-ary λ), so each value and its type is judged at the
  block's own depth, where the shared chain is the same node it is
  everywhere else in the block.
- Hand the discarded values to the gate as separate obligations over the
  block's context, rather than as part of the body. That changes what the
  module image stores, so it is the larger change.

## Acceptance

- `dep` at growing `k` is linear in gate queries
  (`crates/elab/tests/let_and_blocks.rs::a_shared_let_chain_is_checked_once_per_link`
  tightens from "checks" to linear), with the unused-value refusals of
  [[unused-let-value-unchecked]] still refused.

## Log

- 2026-10-26: The `dep` family is now the frontend bench family `let/dep` ([[tactic-scaling-bench-families]]). Its time is about 90% elaboration, which grows faster than the gate's quadratic: `heather check --timings`, release, width one, total against gate ms: 28 / 3.8 at k = 32, 293 / 21 at 64, 2,246 / 122 at 128, 26,788 / 1,518 at 256 (×8 to ×12 per doubling). Not attributed; it is plausibly the same nesting (each discarded value elaborated or shifted under one more binder), so a fix should be measured on the whole time, not on gate queries alone.
- 2026-10-26: FIXED: stack samples of `let/dep` at k = 256 (gdb, release, 14 of 14) were all in `LetValue::discard_around`'s `body.shift_local(1)`: each discarded value shifted everything already wrapped, so the elaboration was the shifts, not checking. Each value is now discarded as `(λ _: T. λ b: B. b)(v)(body)`: the value, its type and the body stay at the block's depth, and `B` is shifted once per block and shared by every redex (`docs/language/let-and-blocks-design.md` §11). `heather check --timings`, release, width one, total / gate ms / queries at k = 32, 64, 128, 256: 1.3 / 0.4 / 740, 2.4 / 0.8 / 1,476, 6.4 / 1.7 / 2,948, 14.8 / 5.2 / 5,892 (was 28, 293, 2,246, 26,788 ms total). `let/dep` slope 1.10 over k = 32..256 (four runs, 1.05-1.15), from 2.55 over 8..64. `a_shared_let_chain_is_checked_once_per_link` now holds `dep` to the linear gate-query bound with the other shapes, and its elaboration's substitution visits too; both fail on the old spelling.
