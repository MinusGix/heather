---
title: Dataflow over regions: checked post-fixpoints and Galois connections
status: open
labels: [lattice,native,analysis]
area: mathematics
milestone: [hih-passes,hih-native-heather]
created: 2026-11-09
updated: 2026-11-10
---

`lib/std/algebra/lattice.hthr` has semilattices but the library has no
monotone maps, fixpoints or Galois connections. Liveness's loop sets are
searched and checked closed (`Homes::closed`, `region_checked` in
`native_alloc`) with a soundness proof for liveness alone; `Ix::hi`
(`lib/lang/facts/in_bounds.hthr`) is half an interval analysis proved for
itself; the segments' `known` facts are a third. Each new analysis that
facts on demand wants (`InBounds`, `Unique`, `Writes`, constants across
loops) would be another global proof. `docs/surveys/native-mathematics-survey.md`
§5; survey rank 5.

## Scope

- Monotone maps on a lattice; Park induction: a checked post-fixpoint
  (`F(X) ⊑ X`, decided) bounds the least one, so solvers stay untrusted and
  proofs never compute a fixpoint.
- A framework over FunctionIR's region tree (structured: no CFG theory):
  abstract values, a monotone transfer per node, checked loop-head
  post-fixpoints, forward and backward; soundness once from local transfer
  soundness against a concretisation (a Galois connection where one exists).
- Liveness restated as the first backward instance; `Ix::hi` as the first
  forward one.

## Done when

Liveness's soundness in `native_alloc`/`native_compile_structured` is the
framework's theorem at the liveness instance, and a second analysis lands
as an instance with only its local lemmas.

## What it assumes from elsewhere

- **[[facts-on-demand]]** owns how facts are requested. Assumed here: only
  that analyses produce them.
- **[[word-abstract-domains]]** supplies numeric domains.

## Log

- 2026-11-10: The general order theory (monotone maps, Galois connections, Park induction, Kleene iteration) is now owned by [[galois-connections-and-checked-fixpoints]] under `math-order-fixpoints`; this issue keeps the region framework and its liveness and `Ix::hi` instances.
