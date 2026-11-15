---
title: Measure environment lookup depth; random-access-list Env if deep lookups show up
status: open
labels: [kernel,performance]
area: kernel
created: 2026-10-25
updated: 2026-10-25
---

`value::Env` (`crates/kernel/src/value.rs`) is a persistent singly linked
list in the query arena: `push` is one allocation, a closure captures the
spine by pointer, and `lookup(i)` walks `i` nodes. Rocq's kernel stores its
explicit substitutions in an Okasaki skew binary random-access list instead
(`esubst.ml`; `docs/surveys/segmap-survey.md` §4), which keeps `O(1)` push, persistence
and shared tails, and makes lookup `O(min(i, log n))`: never asymptotically
worse than the list.

Nobody knows whether Heather ever looks up deep indices. The `value-metrics`
counters record `env_nodes` (pushes) but not lookup steps. Recursor step
telescopes bind at most seven locals; a long `let` block, a function with
many parameters, or a native `Straight` stretch carrying every variable of a
run could bind far more.

## First step

A `value-metrics` counter of lookup steps beside `env_nodes` (and perhaps a
maximum), read over `scripts/perf report`'s corpus. Cheap, and decides the
rest.

## If deep lookups show up

Replace the spine by a skew binary random-access list over the same arena.
What must survive: `Env::ptr_eq`/`Env::ident` (head identity still means the
same environment), `values_ptr_eq_prefix` (walks entries; becomes a walk over
trees), `Env::identity`'s shared prefix spine, and `gshift` riding in the
handle. Measure with `scripts/perf ab`; a moved lookup counter with no seconds
delta is no result.

Trigger: lookups of more than a few dozen steps as a visible share of a real
workload's evaluation. Until then this waits, like any enabling issue with no
puller.

## Log

- 2026-11-05: gardener: cites a file it shares with [[signature-rescope-multiplicity]] (`docs/surveys/segmap-survey.md`); [[type-value-memo-hit-rate]] (`crates/kernel/src/value.rs`).
