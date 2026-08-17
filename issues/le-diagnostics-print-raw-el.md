---
title: A diagnostic about `Le` at open arguments prints the raw `El` code
status: open
labels: [frontend,diagnostics,ergonomics]
created: 2026-08-17
updated: 2026-08-17
---

Found while probing negative controls for [[nat-arithmetic-kit]] (2026-08-17).
Supplying `trivial` where a comparison is wanted says:

```
error: `trivial` proves `True`, but
`El[0](app(app(u55^{·^2}; [0,(0 ⊔ 1)] Nat → Π[0,1](Nat). Ty 0; x1); [0,1] Nat → Ty 0; x0))`
is expected here
  --> probe.hthr:4:68
  |
4 | theorem t(n, m: Nat): add(sub(m)(n), n) = m { sub_add_cancel(n, m, trivial) }
```

The type it means is `Le(n, m)`.

This is **not** the bug [[goal-display-decodes]] fixed, and the difference is
the interesting part. That round gave the display sites a bounded reader that
δ-steps a wrapped type and prints the first non-`El` head. It works whenever a
head exists. Here none does: `Le` is a `fn … -> Type`, so at *open* arguments
`El(Le(n)(m))` is stuck as an `El` — irreducibly, not for want of budget — and
the reader correctly gives up and falls back to `{ty:?}`. The fallback is the
right behaviour for a type nothing can say anything about; it is the wrong
behaviour for one whose code is a readable application of a named global.

So the missing capability is the other direction: **print the code back as
surface** (`Le(n, m)`, `app` spine → call syntax, `xN` → the binder's name from
`Γ`) rather than only unfolding until the wrapper disappears. `unspell_ty_deep`
and the respelling machinery already know the code↔type correspondence.

## Why it matters more now than when the reader landed

Every propositional relation the library states is a `fn … -> Type`
(`docs/nat-order-design.md` §1 chose that over `= True` deliberately, and §6
notes this as the residue). So the *entire* order and everything built on it —
`Le`, `Lt`, `Mem`, `Sorted` — hits the fallback in any diagnostic at open
arguments, which is exactly the position a proof under construction is in. The
class of affected messages is small and fixed (the `trivial` mismatch, the
non-function lambda, goal statements), but the workload that reaches them is
now the normal one.

## What it assumes from elsewhere

- **[[goal-display-decodes]]** (closed) owns the display reader. Assumed here:
  only that display-decode is bounded, display-only, and falls back to the raw
  `Debug` form — which is the behaviour seen above.

## Acceptance

A `trivial`-mismatch or goal-statement diagnostic whose expected type is
`Le(n, m)` at open `n`, `m` prints something a reader recognizes as that type.
Bounded and display-only, like its predecessor; a code that does *not* respell
(a raw `app` of a meta, say) still falls back rather than guessing.

## Log

- 2026-08-17: Second customer, a different display site (issues/std-list-api.md, 2026-08-17). The L1 wave's `len_append` left an unfilled goal — its `Nil` arm was `{}` where the goal is `len(ys) = add(0, len(ys))`, which is stuck rather than refl — and the GOAL LISTING printed the statement as raw kernel encoding: `?g1 : Id[0](Nat; app(app(u1^{·^9}; …)))`, with each context binder shown as its `Wf[0](Σ…)` lowering. Several hundred columns of it, for a statement the reader wrote as one line. The span was correct and pointed at the `{}`, so the fix needed here is only this issue's — respell the code as surface — but the trigger is worth recording: it is not the `trivial` mismatch, it is the ordinary unfilled-goal report, which is the message a proof under construction sees most often.
