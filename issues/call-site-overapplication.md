---
title: Over-application spills into curried application: nth(t, k)
status: open
labels: [frontend,elaboration,ergonomics]
created: 2026-08-05
updated: 2026-08-05
---

Small round item (2026-08-05 ergonomics round). Surface calls are already
multi-argument (`append(xs, ys)` works); the ugly case is a fn that is
*curried by necessity* — `std/list.hthr`'s `nth<A>(xs: List<A>) -> Nat -> Option<A>`,
curried because the termination checker wants one decreasing argument with the
rest fixed. Callers must write `nth(t)(k)`.

The slice this issue owns: at a call site, when `f(a1, …, an)` supplies more
arguments than `f`'s parameter arity, spill the excess into iterated
application — `nth(t, k)` elaborates as `nth(t)(k)`. Call-site only; no
change to declarations, lowering, or the kernel term produced.

Why it stays worth having even after the definition-site fix: partial
application chains and any fn-returning fn benefit, not just the
termination-shaped ones; and it makes `t.nth(k)` (receiver desugaring plus
spill) read right immediately.

## What it assumes from elsewhere
- **[[ih-generalization]]** owns the definition-site fix (elaborator-computed
  Pi motive so `fn nth(xs, i)` can vary `i` across recursion). Assumed here:
  only that it is not landing this round, so curried std fns persist.
- **[[surface-syntax]]** owns call grammar taste. Assumed here: only that
  over-application is currently an arity error, not already sugar.
