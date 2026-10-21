---
title: Deep pattern at a field a later field depends on is a kernel rejection
status: open
labels: [frontend,elaboration,inductives,diagnostics]
area: language
created: 2026-10-20
updated: 2026-10-20
---

`match b { Mk(Ask, k) => k(3), _ => 0 }` over
`inductive Box { Mk(c: Cmd, k: Resp(c) -> Nat), Nope }` (with `Resp(Ask) =
Nat`) is accepted by the elaborator and rejected by the kernel
(`NotConvertible`, "that type has no surface spelling"). The deep pattern
compiles to a nested `match` on the field `c`, and a nested `match` on a
field has a non-dependent motive (docs/nested-match-patterns-design.md
§10.2), so `k`'s alias keeps the unrefined type `Resp(c)` while the arm's
elaboration believes it was refined to `Nat`.

Found while testing tier 2 (`docs/inductive-tier2-w-lowering.md` §12 item
9): an interaction tree's `Vis(Ask, k)` is exactly this shape, so the tree
library will hit it first. It is not tier-2 specific; tier 0 does the same.

Two acceptable outcomes: refine — generalize the later fields that depend on
the matched field into the nested `match`'s motive, as a convoy — or refuse
at elaboration with a message naming the dependent field and suggesting the
nested `match` written out. A kernel rejection is neither.

## Done when

The `Box` example either computes (`h(Mk(Ask, λ n => n)) = 3` by `refl`) or
is refused by the elaborator with a message naming `k`'s dependency on `c`.
