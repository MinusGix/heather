---
title: Level normalization allocates a BTreeMap per comparison; ~14% of the ir_v1 profile
status: closed
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-07-31
---

Found in the post-definitions perf profile of release `heather check
lib/ir_v1.hthr` (2026-07-31, ~2.1s): level arithmetic is ~14% of the
run — `Level::count` 4.0% self, `Level::normalize` 2.6%, `Level`
drop-glue 3.5%, plus clones. Filed as an accumulator per the 2026-07-31
perf-tracking decision; no round is chartered by this file alone.

Mechanism: `Level::normalize` (crates/kernel/src/level.rs:66) builds a
fresh `BTreeMap<UnivVar, u64>` on every call via `count`, and level
comparison on the conversion path normalizes both sides each time —
there is no caching and no cheap structural pre-check, so two
syntactically identical levels still pay two full walks and two map
allocations to be found equal.

Candidate levers, cheapest first:
- structural-equality fast path before normalizing (most compared levels
  are literally the same shape, often the same `Rc`);
- a small-vec or inline representation for the variable counts —
  `BTreeMap` is heavyweight for the typical zero-or-one-variable level;
- memoized `LevelNf` on the term side, which is a representation change
  and would need its own decision.

Trigger: level ops still a top-5 self-time block on a real workload
*after* the Ψ-clone round ([[context-representation-clones]]) lands —
that round owns today's #1 line and shifts every percentage here.

## Log

- 2026-07-31: Filed from the ir_v1 profile taken while sizing the round after definitions ([[simulate-conversion-cost]] close-out).
- 2026-07-31: Post-Psi-round profile (release heather check lib/ir_v1.hthr at 1.475s) confirmed the trigger: level arithmetic was the #1 block at ~17.5% -- Level::count 6.2% self, normalize 3.2%, Level drop glue 4.7% across four symbols, BTreeMap IntoIter::dying_next 1.7%, BTreeMap eq 0.8%, well_formed 1.0%. Lever (a) taken: equiv and le now test syntactic equality first (reflexivity -- normalize is a function, so a hit is sound and a miss falls through unchanged; Rc's pointer-first equality stops the walk at shared subtrees), and NormalizeLevels' mapper returns Zero and a bare variable untouched since each is already its own canonical representative. 1.475s -> 1.305s (min of 3). Lever (b) NOT taken, and the profile is why: after (a), Level::count is 0.39% and normalize 0.15%, with all BTreeMap symbols together under 0.5% -- an inline representation for the variable counts would now be buying tenths of a percent at the cost of hand-rolling a container in a zero-dependency kernel. The level cost that remains is drop glue on Level clones inside term construction, which is a term-representation question, not this one. Lever (c) (memoized LevelNf on terms) stays untaken and unlogged-for: it is a representation change needing its own decision. Tests: level.rs gains fast_path_does_not_make_equiv_stricter (six structurally distinct but equivalent pairs -- idempotence, succ-distribution, commutativity, the unit, the dominated constant, constants across a join -- each asserted distinct as syntax first, so it really exercises the miss) and fast_path_agrees_on_identical_syntax (including omega and an omega-poisoned level). Benches: a new level/ area, level/equiv-shared (slope -0.00, 4 ns flat at 4..64 variables -- the claim that reflexivity is decided at the root) and level/equiv-rebuilt (slope 1.09, the normalize path, guarding against a fast path that becomes the only path). Side effect visible in the suite: nat/check-numeral improved 0.79-0.80x across its sizes, so the baseline was re-recorded. Charter discharged; closing.
