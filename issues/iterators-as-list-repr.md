---
title: Iterators are a runtime representation of List, not a spec type
status: open
labels: [design,stdlib,runtime,compiler]
area: heather-in-heather
created: 2026-08-13
updated: 2026-08-14
---

Decided in discussion (2026-08-13, the showcase critique): the language does
NOT get a Rust-style iterator as a semantic object. A stateful
`next(&mut self)` iterator is proof-hostile — no induction principle, state
threading in every lemma, equality as bisimulation. Instead:

- **The spec type is `List`.** Programs and proofs speak `List` and get its
  equational theory; "lists of things behave nicely in proofs" is the whole
  point.
- **"Iterator" is a [[datarepr-separation]] story**: a lazy/cursor runtime
  representation of a `List`-typed pipeline, with *certified fusion* — the
  claim that a consumer–producer chain compiles to a loop with no
  materialized list is a refinement certificate, not a trusted rewrite
  (foldr/build fusion, certified). Under this reading "typical iterators are
  always finite" is a theorem, not a restriction.
- **Infinite streams stay out** until a real customer shows up: Rust's
  infinite iterators are almost all `repeat`/`cycle`/`successors` + `take`,
  and `Nat -> A` plus `take` expresses those with no coinduction.

The open half, and the reason this issue stays open rather than being a log
entry on datarepr: **API naturality** (raised in the same discussion). Cost
profiles differ per representation — random indexing is natural on a
Vec-repr `List` and pathological on a lazy chain — so the surface may still
want distinct *API faces* (a wrapper type or role, cheaply convertible,
mathematically the same `List`) so that a signature is honest about what it
is cheap to do, even though the math underneath is shared. Shape TBD: one
`List` with repr-conditioned lint/costs, vs a zero-proof-cost wrapper pair.

Also to check before committing further: the claim "iterators are unwieldy
mathwise" deserves a literature pass (Agda/Coq treatments of colists and
container morphisms) — noted in discussion as something to verify, not
assume.

## Log

- 2026-08-14: docs/datarepr-design.md (§5.2) places iterators as ordinary reprs: pipeline ops are registry Impls, and certified fusion is a via-derived certificate for the fused Impl against the composed stagewise derived Impls — no new mechanism. API naturality stays this issue's open half.
