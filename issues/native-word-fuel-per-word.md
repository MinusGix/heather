---
title: Native word runs charge fuel per bit, so closed verdicts over word code run out early
status: open
labels: [kernel,performance,bitvectors]
area: kernel
created: 2026-11-14
updated: 2026-11-14
---

A closed verdict over word-level code ran out of fuel at a fraction of the
work fuel allows anything else, because a native bit-transducer run charged
one fuel unit per bit it read or produced (`spend_n(read)` in
`eval/transduce.rs`, design §8 of `docs/native-bitvector-values-design.md`).
A run is at most one word (`BIT_RUN_WIDTH_CAP`) and is a bounded number of
native operations, so the charge counted 64 units for one operation's
work. A literal's entry already charged one unit for the same reason.

## How it was found

`TOKEN_KINDS` (`lib/lang/lexer/lexer_kinds.hthr`, PR #628): one `refl`
that every spelling of every row is one token of its kind ran out of the
per-conversion budget (`DEFAULT_FUEL`, 2^20) and was split into three.
Measured on the cloud box, release, one kernel worker:

- The table itself is cheap: `token_kinds_numbered` over all 70 rows is
  ~19K steps. The cost is the scanner (`scan_step`, `Accepted::longest`)
  evaluated over each spelling: ~15K steps a spelling, almost all 64-bit
  word operations.
- A word operation in steady state costs ~80 (`eq_bit`) to ~270 (`add`)
  steps. In a chain of nine additions, 1,282 of 2,671 steps were the
  per-bit charge; over a third of the table's spelled check was.
- Real time is an even spread over the evaluator (perf: `drive_above`
  9%, arena allocation, substitution, no hotspot), about 0.2 µs a step.

## The change

A run charges one unit (`Eval::spend`) once the fold is known to fire.
It is still proportional to the data (a wider vector is one run per word)
and still at most what the structural path spends, so no verdict fuel
allowed becomes a refusal.

| item | per bit | per word |
| --- | --- | --- |
| `TokenKind::spelled(TOKEN_KINDS)`, one theorem | ~1.34M (`OutOfFuel`) | 586K |
| first 24 rows | 235K | 103K |
| middle 24 rows | 593K | 265K |
| last rows | 505K | 227K |

Time is unchanged: the charge had no time behind it.

## What is left

- The token-kinds proof can be one theorem again (coordinate with the
  thread that owns `lexer_kinds.hthr`).
- Word code still costs 80–270 evaluator steps an operation in wrappers,
  δ-unfolds, β and type decoding; that is the real-time lever, and a
  separate issue.
