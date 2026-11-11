---
title: Per-call memos pay for a hash table's capacity when they hold one or two entries
status: closed
labels: [kernel,substitution,performance]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

Found in the whole-gate instruction profile of a cold
`docs/showcase/calc_parser.hthr` (callgrind inside `time_kernel*`).

## What it did

Three memos live for one call and are keyed by addresses:

- the substitution traversal's shared-node memo (`subst.rs` `NodeMemo`, two
  tables),
- a local substitution's lifted payloads (`SubstLocal::lifted`),
- syntactic equality's equal pairs (`syntax_eq.rs` `PairMemo`).

Each was a hash table. On the showcase the node memo is made 2.4 M times and
used 500,000 times, and a used table holds **1.6 to 2.1 entries** on average;
the pair memo and the lifted payloads are the same shape (1.6 M inserts
against 711,000 first allocations; 414,000 against 157,000).

- `NodeMemo`'s tables came from a per-thread pool, to save the allocation
  and the first rehashes. A pooled table keeps the capacity of the largest
  call that used it (up to the pool's cap, 4096 slots, about 200 KB of
  buckets), and emptying a table costs its capacity: a 4 KB `memset` of
  control bytes and a scan for the entries to drop, per call that recorded
  anything, with the two entries written somewhere in those 200 KB. `Drop`
  for `NodeMemo` was 3.9% of the kernel's instructions.
- The other two allocated at the first entry and rehashed at the next few:
  2.1% of the kernel's instructions under `PairMemo`'s inserts.

## What was built

`few_map::FewMap`: the first four entries are an array in the map itself,
searched in order, and only a fifth goes to a hash table. The three memos
are `FewMap`s; the substitution memo's pool, its two caps and its `Default`
and `Drop` are gone.

## Log

**2026-11-10.** Cold `docs/showcase/calc_parser.hthr`, cloud box, width one.

- Every counter column is identical before and after: the memos answer the
  same questions.
- Instructions inside the kernel gate (callgrind): 21,955 M to 21,498 M,
  −2.1%. `NodeMemo`'s `Drop` and the pool are gone from the profile, and the
  three memos' lookups are under 0.5% together.
- Seconds (`scripts/perf ab --mode cold`, five interleaved samples): the
  kernel gate's median moved by −7.2% and the sample sets overlap, so this
  is no result in seconds. The claim is the instruction count and the code
  removed.
