---
title: Compare two equal DAGs in shared size, not as trees, in the conversion shortcut
status: closed
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

## Log

- 2026-10-26: `stmt` is now the frontend bench family `let/stmt` (k = 14..20, [[tactic-scaling-bench-families]]). Its elaboration is 2^k as well, about half the time at every size (probe-run split at k = 20: elab 46 ms, kernel 45 ms). Not attributed; the elaborator's own `refl` check reaches the same shortcut, so a fix here may move both halves.
- 2026-10-26: LANDED (option 1, the pair memo): `crates/kernel/src/syntax_eq.rs`. `==` on `Type`, `Term` and the structs that carry them (`LocalCtx`/`CtxEntries`, `LocalSubst`, `Motives`, `Branches`, `IWfSig`, `MSig`) is hand-written per variant over a `SharedEq` trait that threads one `PairMemo` through the whole comparison: a pair of `Rc` children with `strong_count > 1` on both sides is looked up by both addresses and recorded once found equal. No keep-alive is needed (the memo lives for one `==` call and only reads what its two borrowed roots reach), the table is allocated on the first shared pair, and debug builds compare one level again behind a sample of hits. Every enum match is exhaustive on `self` and every struct is destructured whole, so a new variant or field does not compile until it is compared. Counters `syntax_eq_nodes` / `syntax_eq_memo_hits` (`scripts/timings` columns `eq`, `eq memo`).
      - **The elaborator's half was the same equality.** `gdb` on master at k = 30 had the elaboration in `Elaborator::note_refl_mismatch`'s `lhs == rhs` (the "two syntactically identical sides skip the probe" test before a `refl` note is recorded), so the one fix moves both halves.
      - **`stmt`, release, width one, total / gate ms:** k = 20: 52 / 27 → 0.7 / 0.3; k = 24: 776 / 397 → 0.7 / 0.3; k = 26: 3,244 / 1,561 → 1.0 / 0.3; k = 30 (was past a 200 s rail): 1.0 / 0.4. Frontend family `let/stmt` re-swept over k = 32..256: slope 1.04 (four runs, 0.90-1.11; was 9.58 over 14..20), band now 0.75-1.45. `crates/elab/tests/let_and_blocks.rs` `two_equal_let_chains_compare_once_per_link` pins `syntax_eq_nodes` growing < 3× from k = 16 to 32.
      - **Does the library pay? Not measurably.** Whole folders with the new binary: lib/std 59.8M node pairs compared, 3.8M memo hits; lib/native 58.3M / 4.2M; every verdict counter (queries, misses, steps, check_terms) identical to master. `scripts/perf ab` (master vs this, three interleaved cold samples, width one) over `nat.hthr` and `float/round.hthr` (the folder run's largest apparent movers): every counter identical, wall and gate within the spread (round: gate −9%, "spread exceeds the delta"). A first whole-folder timing that read some float items +40% slower was a loaded box (a test build overlapped it); the interleaved A/B does not reproduce it. So the hits are short re-walks today; the win is the shape, for the generated and let-shared terms that would have met it.
      - `scripts/bench --check` flags `conv/perturbed-pairs` and `check/generated-terms` slopes on the cloud box, and master on the same box flags them the same (1.65 / 1.51 master vs 1.63 / 1.59 here; baseline is another CPU), so no regression from this.
      - `rewrite/let-addr0` is unchanged (5.85): its 2^k is the abstraction walk and the motive/transport the gate checks, not the final `refl`.
