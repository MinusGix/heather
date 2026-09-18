---
title: Converting `k < Succ(n)` against `k <= n` costs a step per unit of the literal
status: open
labels: [kernel,conversion,performance]
created: 2026-09-18
updated: 2026-09-18
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
    lt_of_not_le(1024, Succ(n), h)
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
