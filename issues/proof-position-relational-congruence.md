---
title: Use relational congruence inside ordinary proofs
status: closed
labels: [relations,setoids,elaboration,testing]
created: 2026-09-05
updated: 2026-09-05
---

Connect a supplied lemma application to the expected local relation goal. Resolve compatibility from ordinary class assumptions and leave missing evidence as ordinary resumable goals. Use merge_twice as the client; keep relation choice explicit and reconstruction kernel-checked.


## Acceptance

- Check `merge_twice` with `rel_cong(A.idem(incoming))` inside transitivity.
- Resolve binary compatibility and reflexivity through local class parents.
- Expose missing unary preservation, binary dictionaries, and fixed-value
  evidence as ordinary local goals; discharge them with ordinary `on` clauses.
- Keep repeated and partial occurrences, distinguish separate calls' goals,
  reject unrelated changes and wrong relations, preserve observable evidence,
  and refuse invalid resumptions without registering a theorem.
- Bound the native homogeneous fragment; verify the checked showcase and finish
  with the plain full Furnace suite.

## Boundaries

This is an initial proof-position elaborator entry point. It does not replace
[[setoid-auto-lifting]]'s general relator engine, higher-order and dependent
contexts, or boxed-code integration. The source driver in
[[single-contextual-rewrite]] remains an inspectable construction example.
Calculation chains and a general tactic language remain separate design work.

## Log

- 2026-09-05: First six native proof-position tests passed on Furnace, including
  `merge_twice`, local observer evidence, goal resumption, and refusal controls.
  Expanded validation is in progress.
- 2026-09-05: Completed native `rel_cong`, updated the library's `merge_twice`, and added the checked showcase. Generated obligations keep a readable original-type spelling without changing their kernel types. Independent CLI checks verify the showcase and named missing-preservation diagnostic. Final plain Furnace suite: 2,348 passed, 0 failed, 5 ignored; all 33 setoid/generator/proof-position cases passed.
