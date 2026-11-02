---
title: Nested constructors above a corecursive call, for indexed codata
status: closed
labels: [codata,coinduction,elaborator]
area: interaction-trees
created: 2026-11-01
updated: 2026-11-02
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

## Log
- 2026-11-02: Done (`docs/codata-elaborator-design.md` §5.4, indexed bullet). The layers are families, `C_{j+1}(i) = X(i) + F(C_j)(i)` with `F` the kernel's `m_step_ty`; a pending node is built from the declaration's parts re-read at its child's index (`MParts::reindexed`), so its payload, its children and a self-call under it are all at that index; `J` moves the step's `inl` arm only; `lift`/`embed` carry the index they work at. The node's index is read as written (`written_index`) so a wrong payload is reported at its `refl`. Probes in `crates/elab/tests/codata_indexed.rs` and `lib/_tests/std/itree/coitree_tests.hthr` (`tick2_self`, `spin_twice`: a `Bisim` matching two observations per step). A wrong payload against a *tuple* index still names the expected type as unspelled (a projection of a literal pair prints raw), with or without nesting: [[display-literal-pair-projection]].
