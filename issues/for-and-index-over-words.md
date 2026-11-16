---
title: Write `for i in a..b` and `v[i]` over words, in compiled record functions too
status: closed
labels: [surface,loops,vectors,native,runtime-fn]
area: language
milestone: [crypto-hash]
created: 2026-11-14
updated: 2026-11-14
---

SHA-256 as compiled methods (`lib/native/crypto/`, PR #607) wrote each loop
as a hand recursion (`decreases (48 - j).toNat()`, `if h: j < 48 { …;
s.expand(j + 1) } else { j }`) and each element as `s.schedule.at(j + 14)`
and `s.schedule := s.schedule.put(j, x)`: the surface had `for i in a..b`
and `xs[i]`, but a range listed `Nat`s, an index was a `Fin`, and the
record-function generator took neither.

Built as docs/language/sequencing-surface-design.md §21: a range over words is a
counted `decreases` recursion with its test in scope (a `mut self` method
`T::f_loop` where the loop's state is the receiver, which the `runtime`
generator compiles as a loop and `T::f` calls); `xs[i]` at a non-`Fin`
index is `xs.at(i)` and `xs[i] := e` is `xs := xs.put(i, e)`, each proof
found from the test. Probes: `lib/_tests/native/runtime/runtime_held_for_tests.hthr`.

## What it assumes from elsewhere
- **[[runtime-record-function-limits]]** owns what a record function takes;
  assumed here only that a counted `mut self` method is one.
- **[[methods-on-the-vector-type]]** owns `Vec`'s members; assumed only
  that `Vec::at`/`Vec::put` find their `inside`.

## Not built (§21.3)
- `break`/`continue`/`return` in a loop over words.
- A loop whose state is the receiver and other locals, in a `runtime fn`.
- `→ ()` for a `mut self` method; and the one-call function a loop leaves
  its caller (`Sha256::expand` calls `Sha256::expand_loop`) is a call in
  the linked code, five more per SHA-256 block.
- `xs[k]` at a numeral in a `runtime fn` (the kernel's `nth`).

## Log

- 2026-11-14: Filed and built in one round (language-feature thread 3,
  /mnt/project-files/design/language-feature-threads-2026-11-14.md). SHA-256's
  five loops (`expand`, `begin`, `shift`, `rounds`, `end`) are `for` loops over
  `v[i]`; the linked `sha256_compress` keeps each loop's code and gains a
  one-call wrapper per loop (535 bytes, stack 2640 → 3240).
