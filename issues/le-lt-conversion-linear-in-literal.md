---
title: Converting `k < Succ(n)` against `k <= n` costs a step per unit of the literal
status: closed
labels: [kernel,conversion,performance]
created: 2026-09-18
updated: 2026-09-28
---

Converting `k < Succ(n)` against `k <= n` at a *literal* `k` and a neutral
`n` costs a reduction step per unit of `k`, and runs out of fuel somewhere
between `k = 16` and `k = 1024`. Both sides are stuck after one unfolding —
`Le(k, n)` whnfs to a match on the neutral `n` — so the linear cost looks
like the conversion checker peeling one `Succ` off each side per round
instead of noticing that the two stuck matches agree.

Minimal repro (`import logic; import nat;`):

```heather
theorem conv_small(n: Nat, h: 16 < Succ(n)): 16 <= n { h }      // checks
theorem conv_only(n: Nat, h: 0xD800 < Succ(n)): 0xD800 <= n { h } // OutOfFuel
theorem mid(n: Nat, h: ¬(Succ(n) <= 1024)): 1024 <= n {         // OutOfFuel
    Nat::lt_of_not_le(1024, Succ(n), h)
}
```

`nat::Lt(n, m)` is *definitionally* `Le(Succ(n), m)`, and `nat.hthr` sells
that as the reason `lt_succ_iff_le` and `lt_succ_self` need no proof. The
identity is unreachable above a small literal, so any lemma that moves
between the two forms at a Unicode-sized constant is unwritable.

Found while writing `lib/std/char.hthr` ([[string-char-spec-types]]): the
first spelling of `scalar_dec` refuted the surrogate range by `le_trans`
against `¬(Succ(code) <= 0xD800)` and hit this. The landed spelling avoids it
by deciding `0xD800 <= code` with `le_dec` directly — cheap at a closed code,
since `le_dec` descends both arguments together — so nothing is blocked; the
pathology is filed rather than worked around further.

## Log

- 2026-09-18: Coordinator repro 2026-09-18 on the release binary at the default kernel width: the `0xD800` case aborts the checker with a kernel-worker stack overflow rather than `OutOfFuel`, so the cost is a deep recursion, not only a long one.
- 2026-09-25: The worker-stack abort above is its own defect, filed as [[kernel-worker-stack-below-depth-budget]]: pool threads get Rust's 2 MiB default stack while the depth budget assumes 8 MiB. With `RUST_MIN_STACK=8388608` the same kind of item answers `OutOfFuel` at width eight.
- 2026-09-28: Fixed the comparison of suspended Nat induction hypotheses. The two sides reached identical step syntax over separately allocated environments; forcing the captured hypotheses before comparing them unrolled one nested neutral match per literal unit. The value-domain identity shortcut now compares suspended Nat folds structurally, including their scrutinees, levels, motives, bases and steps, under a bounded search. It resolves captured variables and compares the captures actually used by an application, accounting for branch binders that have not yet been installed in the environment. Captured global offsets and the outer carrier scope still gate identity; an inconclusive search falls back to ordinary conversion. Ordinary closed computations retain their existing fuel/depth path.

  Regression coverage checks both conversion directions, the explicit successor step and the `lt_of_not_le` repro through `0x10FFFF`, with shifted-literal and different-neutral controls. Kernel controls vary every fold component, pending binder counts, used captures and global offsets, and compare independently allocated folds at a saturated numeral with just one conversion fuel unit.
- 2026-09-28: `scripts/perf ab` (three interleaved cold samples, HEAD versus this fix) confirms the scaling change: evaluator steps for the identity conversion at literals 16 / 64 / 256 fall from 116 / 404 / 1556 to 22 / 22 / 22. Query counts stay at 14 for each item. The machine was busy with full verification, so this round claims only the exact counters, not a seconds delta.
- 2026-09-28: Verification: full `scripts/test` passes (3066 passed, 0 failed, 5 ignored); the release CLI checks the Unicode-sized repro and the corrected `Nat::lt_of_not_le` example at its default worker width. The quiet full `scripts/bench --check` has only the pre-existing `wf/check-tree` lower-slope-band flag: 0.79 against 0.85–1.35 here, also reproduced at unchanged HEAD (0.77). This stale band was already recorded in [[wf-ih-rebuilt-per-node]]; no benchmark time regressions remain in the quiet full run. `scripts/issue check` passes with its existing unrelated tracker warning.
