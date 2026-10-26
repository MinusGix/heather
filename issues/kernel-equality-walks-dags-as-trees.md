---
title: Compare two equal DAGs in shared size, not as trees, in the conversion shortcut
status: open
labels: [kernel,performance,proofs]
area: kernel
created: 2026-10-26
updated: 2026-10-26
---

`Tc::conv_ty`'s reflexivity shortcut is the derived `==` on `ITy`/`Type`/
`Term`. `Arc`'s equality tries `ptr_eq` first, so a DAG compared with
itself is cheap. Two DAGs that are equal but were built separately are not:
the derived `Term::eq` walks them as trees, so the comparison costs the
number of paths, 2^k for a let chain.

Found by the `stmt` probe of `docs/mengine-survey.md` §4.2 once
[[kernel-typing-memo-on-node-identity]] made the gate's *queries* linear.
`theorem stmt(v0: Nat): { let v1 = g(g(v0, v0), 0); …; vk } = { … same … } { refl }`
elaborates the two sides separately, and `refl`'s check compares them.
Release, width one, `--timings`, 2026-10-26:

| k | queries (all shortcut) | misses | eval steps | gate ms |
|---|---|---|---|---|
| 16 | 287 | 0 | 0 | 2.9 |
| 20 | 359 | 0 | 0 | 71.8 |
| 24 | 431 | 0 | 0 | 787 |
| 32 | 575 | 0 | 0 | 198,321 (debug build) |

`gdb` stacks during the k = 28 run are 30 frames deep in
`<Term as PartialEq>::eq` and nothing else. In the library, two copies of
one value meet wherever a value is elaborated twice (a statement and its
proof, two sides of an equation, an expected type and an inferred one).
Whether any library item pays for it today is not measured.

## Options

- **A pair memo in the comparison.** Term and Type equality with a
  per-comparison memo of node pairs already found equal (keyed by both
  addresses, live for the comparison, so the addresses cannot be reused).
  Equality's answer does not depend on the memo, so it may be filtered on
  `Rc::strong_count > 1`, as `subst.rs`'s `NodeMemo` is, with no determinism
  argument. The cost is a hand-written `eq` per variant (the derive cannot
  be intercepted at the `Rc` child), or a one-level children accessor that
  the `eq` can be written over.
- **Share at the source.** The elaborator could hand the kernel one copy
  (hash-consing let values, or reusing the statement's elaborated sides in
  the proof). That narrows the cases, but the kernel's shortcut would stay
  a tree walk for any it misses.

## Acceptance

- The `stmt` family's gate time grows linearly in `k` (time here, since the
  query count is already linear), with a Rust test on a counter if the fix
  adds one.
- `scripts/bench --check` shows no regression on the conversion and checking
  rows: the shortcut is on every query's path.
