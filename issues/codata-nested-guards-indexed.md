---
title: Nested constructors above a corecursive call, for indexed codata
status: open
labels: [codata,coinduction,elaborator]
area: interaction-trees
created: 2026-11-01
updated: 2026-11-01
---

Nested constructors above a corecursive call are generated for unindexed
codata (`docs/codata-elaborator-design.md` §5.4): the carrier gains one
pending-node layer per extra constructor, `C_{j+1} = X + F(C_j)`. Indexed
codata keeps the one-layer carrier, and a nested call is refused with this
issue:

```
fn bad(s: Stream) → SBisim(s, s) { Same(refl, Same(refl, bad(tl(tl(s))))) }
```

The workaround is the one unindexed codata had: write the pending layer as
a seed state of its own (a phase parameter), or a helper whose step returns
one constructor.

## Shape

- The layers are families over the index: `C_{j+1}(i) = X(i) + F(C_j)(i)`
  with `F(C)(i) = Σ(s : S(i)). Π(p : P(i, s)). C(o(i, s, p)) + ⟦D⟧(o(i, s, p))`.
  `X(i)` already carries the equation `g[v] = i`
  (`docs/codata-indexed-design.md` §6); a pending node needs none, since it
  is built at its child's index.
- A pending node is elaborated at the child's index `o(g, s, p)`, not the
  step's `g`, so the node builder needs an `MParts` at another index
  (`MParts::read` of `d_of(idx)`).
- The step's `J` along the carrier's equation applies to the `inl` arm only;
  the `inr` arm is already at `i`.

## Customer

None pressing: the `Eutt` and `Bisim` proofs in `lib/std/itree/` put every
call under one constructor. A proof that steps two constructors at once
(an up-to-counts argument, a bisimulation that matches two observations
per step) would want it.
