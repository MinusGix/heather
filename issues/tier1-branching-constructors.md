---
title: Branching finitary inductives: how tier 1 handles 2+ recursive fields
status: open
labels: [frontend,elaboration,inductives,design]
created: 2026-07-24
updated: 2026-07-24
---

Split out of [[inductive-compiler]] tier 1 on 2026-07-24, when the
exact-height scheme was written down and prototyped: it covers the **linear
fragment** (≤ 1 recursive field per constructor — `List`, `Bits`, snoc
lists) and provably does not extend to a constructor with two or more
recursive fields. That includes `Node(Tree, Tree)` and therefore the IR
expression knot, so this decision gates [[ir-simulate-design]].

Full argument: `docs/inductive-tier1-lowering.md` §8.1. In brief:

- Exact height *is* computable for a branching constructor (`S (max h_l
  h_r)`), so the issue's original plan was right about the measure.
- What breaks is the **payload**. At height `m+1` the children's heights are
  `≤ m` with `max = m`, so the branch type is a disjunction of shapes, and
  the natural fix (simultaneous recursion producing both the exact family and
  `D_below h = D_ex 0 + … + D_ex (h-1)`, well-defined and canonical) forces
  the *constructor* to inject the shorter child into `D_below` at a depth
  that is the difference of the two heights.
- So `node l r` is a case-split on a height comparison, not a constructor
  form: with an open child it is stuck, and `match (node l r) { … }` stops
  reducing. That is precisely the property the linear fragment buys
  (`cons a l` β-reduces with `a`, `l` both variables — pinned in
  `crates/elab/tests/tier1_fording.rs`).
- Every other single-`Nat` measure hits the same wall for the same reason
  (total size needs the split point; preorder tokens need concatenation;
  Gödel-coded shapes need pairing arithmetic). The invariant: unless the
  parent's payload type is *literally* a container of the children's payload
  types, assembly takes computation on measures, and that computation gets
  stuck on open terms.

## Routes

- **(a) Branching goes to tier 2** — `W` + `Id` + funext-as-axiom, as
  [[kernel-v1-extensions]] already argues for infinitary types. Cheapest to
  build; loses definitional `match` β on branching data, so the IR's
  equational reasoning becomes propositional.
- **(b) Multi-index fording** — index the family by a *shape* (a pair of
  heights for a binary node) so the parent's payload type is literally the
  children's. Preserves β; the index type wants to be a branching inductive,
  which is circular unless stratified statically. Needs real design work,
  and it is the one route that keeps first-order data definitionally clean.
- **(c) Keep `D_below`, canonicalize the embedding** — emit the concrete
  injection when heights are literals, postpone otherwise. Restores
  computation in the closed case only; cheap, partial, hard to explain.

Recommendation as written up: **(b)**, with **(a)** as the fallback that
unblocks the IR immediately (W is already in the kernel and already argued
sound in [[metatheory-ch07-pass]]'s pass). Needs a decision before the
tier-1 generator grows a branching path.

Related and deferred alongside it: mutual/nested recursion
(`Rose { Node(List<Rose>) }`, §8.2 — same simultaneous-family device, but
the part that works) and indexed families (§8.4 — fording an index means an
`Id` field, and `Id` has no η).

## Log

- 2026-07-24: Opened. Scheme + prototype for the linear fragment landed; the
  branching defect is diagnosed (β on open children), routes (a)/(b)/(c)
  written up, recommendation (b) with (a) as the IR's fallback.
