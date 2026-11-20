---
title: Runs over literals wider than a word cost superlinear time in the bit width
status: open
labels: [kernel,performance]
area: kernel
code: crates/kernel/src/value/program.rs @ 91339c55
created: 2026-11-20
updated: 2026-11-20
---

Found by the bench families `run/affine-literal`, `run/sync-literal`,
`run/mul-literal` and `run/open-tail`
(`crates/kernel/benches/kernel/fixtures/runs.rs`), which convert folds over
literals `2ᵇ - 1` for b from 16 to 4096 bits. Every counter is flat (four
evaluator steps for `add(N, 7) ≡ add(N - 3, 10)` at any width), as the run
machinery promises, but the time is not:

| bits | `run/affine-literal` |
|---|---|
| 64 | ~3 µs |
| 256 | ~180 µs |
| 4096 | ~8 ms |

A 60× step from one word to four, then a slope of about 1.5 in the width.
Cryptographic constants are 256-bit numbers, so this is the width that
matters.

## Where the time goes

A callgrind profile of the family: `count_add` (numeral additions of
composition lengths) is the largest self cost, then allocation and the
recursive drop of `ContextProgram` nodes, under `AffineTree::iterate_memo`
and the comparison's `cancel_matching_prefix`. A literal past a `u64`
becomes an `O(bits)` composition DAG (`ContextProgram::of_count`), and each
node's length is a multi-limb `Numeral`, so building, iterating and dropping
those DAGs is at least bits × limbs.

Nothing counts it: no kernel counter sees numeral arithmetic or program
nodes, so the exact-counter gate cannot catch a regression here, and the
families' bands record today's exponent instead.

## Log

- 2026-11-20: found by the new bench families; not investigated further.
