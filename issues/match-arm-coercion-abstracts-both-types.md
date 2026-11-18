---
title: Inside a plain match, every checking fallback rebuilds both types to ask whether the test occurs
status: open
labels: [performance,elab,matching]
area: language
created: 2026-11-18
updated: 2026-11-18
code: crates/elab/src/readings.rs:224 @ 392affe4
---

Found by [[elaboration-cost-overview-2026-11-18]]. Arm readings stage 2 (#761, `docs/language/matching/arm-readings-design.md` §5) carries a term along a plain `match`'s pending equation when its type spells the test where the arm's constructor is wanted. `Readings::coerce` runs at the checking fallback (`checking.rs`, after `got` and `expected` turned out different as written) and, for each pending test, asks `expected.abstract_local(&test)` and `got.abstract_local(&test)`. The answer is only used as "does the test occur", but the question is a whole abstraction: every node under a free local is rebuilt to make room for `z`.

Measured 2026-11-18 (test-profile binary, `--only`, kernel width one, cloud box), by counting the loop's calls and the `local_subst_nodes` they caused:

| declaration | checks | all misses | cost | declaration |
|---|---|---|---|---|
| `supremum::OrderComplete::below_located` | 260 | yes | 18.4 s, 174 M nodes (median 138 k per check, up to 3.3 M) | 27.7 s; 7.8 s with the check skipped |
| `closed_interval_tests::cubic_nonconst` | 5,391 | | 4.8 s, 80 M nodes | 16.8 s |
| `x86_64::decode_opcode_reference` | 39,891 | | 0.07 s | 12.2 s |
| `native_compile_correct::Target::procedures_body` | 43,135 | | 0.1 s | |

So the price is (checks) × (size of both types), and the real-analysis proofs, whose goals spell an ordered field's structure out, have both factors large. Most checks are misses: the test (`K.rel_cotrans(…)` in `below_located`) is in neither type.

## What would fix it

- Ask whether the test occurs with a read, not a rebuild: a walk that stops at the first hit, skips subtrees whose free-variable bounds cannot hold the test's locals (`bounds::skip_term`), and keeps a visited set of shared nodes. Only a hit then pays for the abstraction.
- Or decide the conversion first where that is cheap (`got` and `expected` often convert, and then the term is left as it was).

## Benchmarks

`scripts/bench-frontend --filter match/`: `match/arm-checks` against its control `match/plain-checks` (the same `k` fallback checks with no `match` around them), and `match/arm-type-size`. On 2026-11-18 the arm cost 1.2 to 1.5 times the control per check at type size 16. The bench's types are small; the library's are what make it a third of a declaration. The probe case `analysis/below-located` (`scripts/bench-probes`) is the real one.

## Done when

`below_located`'s `local_subst_nodes` falls by the 174 M above, and `match/arm-checks` costs what `match/plain-checks` does per check.
