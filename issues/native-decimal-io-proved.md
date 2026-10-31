---
title: Prove the decimal procedures' sources print `decimal` for every word
status: open
labels: [native,proofs,stdlib]
area: heather-in-heather
milestone: []
created: 2026-10-28
updated: 2026-10-31
---

[[native-decimal-io]] checks `put_decimal_padded` and `parse_decimal`
(`lib/native/native_decimal.hthr`) by running their lowered sources at
small values (`lib/_tests/native/native_decimal_tests.hthr`) and, compiled,
at the widest words against Rust (`compiled_decimals_round_trip_the_widest_words`).
Neither is a theorem for every word.

## Scope

- State, for every `value` and `width`, that the statement
  `put_decimal_padded` lowers to takes an environment to one whose buffer
  holds `pad_left(width, ' ', decimal(value))` at `at` (and the parse's
  converse, with its overflow flag), over `Stmt::denote`.
- The builder has no program logic of its own yet: a lemma per `Act`
  constructor over `items`/`packed` would be the first, and is the same
  shape the certificate-budget round's per-part lowering needs.
- `decimal` divides in unary, so the proof goes through
  `decimal_places`/`tens_is_div` (`std/text/decimal`), not evaluation.

## Why it is not urgent

`native_compile_correct` already makes every compiled tool simulate its
source; this would add that the source's numbers are the right digits.

## Log

- 2026-10-31: 2026-10-31: hih-tools closed (docs/compiler-milestones-proposal.md §8). No milestone; still not scheduled.
