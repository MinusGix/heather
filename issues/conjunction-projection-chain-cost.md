---
title: Projecting deep into a nested conjunction costs quadratically in depth
status: open
labels: [elaboration,performance,proofs]
created: 2026-09-25
updated: 2026-09-25
---

Reading hypothesis `k` out of a right-nested conjunction as
`facts.right.right…right.left` costs about quadratically in `k`. Each
projection re-infers the type of the whole conjunction below it. In
`lib/decimal_line.hthr` (2026-09-25), `line_word_value` pulled 24 facts out of
the conjunctions its `*_arith` lemmas returned and took **28 s**. The same
facts, returned as a record with named fields (`GroupFacts`) and read by field,
brought the item down to well under a second, together with naming the states
(`line_state_*`). `elf64_read_print`'s `ReadPrintFormat` and `PrintFormatted`
are records for the same reason.

Records are the better library style anyway, since a named field documents
itself. But a conjunction is what `⟨…⟩` builds and what `omega`-style tactics
return, and a person should not meet a quadratic when reading one.

## Questions

- Is the cost in elaboration (`.right` inferring `And(A, B)` by whnf of the
  receiver's type at each level) or in the gate? Attribute one item with
  `--timings` at growing `k`.
- If elaboration: can the receiver's type be carried rather than re-inferred
  per projection? The same question is open for records at
  [[per-instantiation-projection-boundaries]].
- Is it the same mechanism as [[proof-let-substitution-cost]]? `facts` there
  was a `let` bound to a lemma call, so each projection may also have copied
  the call.

## Acceptance

- A family: a `k`-fold conjunction projected to its last component, at
  growing `k`. The cost is recorded and made linear, or its shape is
  explained.
