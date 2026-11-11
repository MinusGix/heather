---
title: "Monotone maps, Galois connections, closure operators, and fixed points a predicative library can state"
status: open
labels: [stdlib,mathematics,lattice,order]
area: mathematics
milestone: [math-order-fixpoints]
created: 2026-11-10
updated: 2026-11-11
---

Area 2 of the 2026-11-10 ranking. The general theory under
[[dataflow-checked-fixpoints]] and [[word-abstract-domains]], which stay
the native clients.

The library has orders and lattices pointwise (`order.hthr`,
`lattice.hthr`) and nothing about maps between them. `nucleus.hthr`
states a closure operator for frames only.

## Scope

- Monotone maps as a record, composition, the pointwise order.
- Galois connections (adjoint pairs) with the unit and counit laws, and
  the closure operator one induces; closure operators with their fixed
  points as a meet-closed family; `Nucleus` restated as the instance.
- Fixed points without impredicative Knaster–Tarski: a pre-fixpoint
  bounds every inductively generated point (Park induction against a
  checked `F(x) ≤ x`); Kleene iteration from bottom reaches the least
  fixed point on a carrier whose ascending chains are bounded
  ([[finite-cardinality-and-pigeonhole]]). Solvers stay untrusted and the
  witness is checked (`docs/compilation-vision.md`).
- Soundness of an abstract interpretation once: a Galois connection (or
  a bare concretisation where no best abstraction exists) and a locally
  sound monotone transfer give a sound analysis.

## Done when

[[dataflow-checked-fixpoints]]'s liveness instance cites this module for
everything that is not about regions, and `nucleus.hthr` has no private
closure-operator laws.

## What it assumes from elsewhere

- **[[order-hierarchy-across-universes]]** owns whether frames and
  lattices share these theorems. Assumed here: only that the statements
  are written against the unified classes once they exist, and against
  `lattice.hthr` until then.
- **[[well-founded-order-combinators]]** owns well-foundedness. Assumed
  here: only the chain bound's use of it for Kleene iteration.

## Log

- 2026-11-11: First round. `lib/std/algebra/fixpoint.hthr`, over a
  `PartialOrderRel(≈, ≤)`: `Nat::iterate` and `Nat::orbit`,
  `PartialOrderRel::Monotone`, Park induction against a checked
  pre-fixpoint (`iterate_le_prefix`), the ascending iteration
  (`iterate_ascends`, `iterate_le_later`), an iterate that has stopped
  rising as the least pre-fixpoint above the start and a fixed point
  (`stable_bounds`, `stable_least`, `stable_fixed`), and with a decidable
  order `PartialOrderRel::kleene(f, fuel, x)`, which computes, with
  `kleene_sound`, `kleene_least`, `kleene_fixed`. On a finite carrier
  `Fintype::kleene_total` says the run answers within `card + 1` steps,
  from `Fintype::chain_len_le` (a run with no answer is a strict chain).
  `lib/std/algebra/galois.hthr`: `Galois(LA, LB, l, u)` as the
  adjunction, unit, counit, both monotone, the closure `u ∘ l` monotone
  and idempotent, the two triangle laws, and the analysis theorem with a
  bare concretisation (`concretisation_sound`) and with a connection
  (`analysis_sound`). Probes in
  `lib/_tests/std/algebra/fixpoint_tests.hthr`.

  The sections take both relations as binders (`same as ≈`, `le as <=`):
  a theorem over two orders (every one in `galois.hthr`) cannot name a
  member of a section that leaves them to the carrier's symbols.

  Remaining: monotone maps and closure operators as structures with
  `Nucleus` restated as the instance (structure shapes, and they wait on
  [[order-hierarchy-across-universes]] to be written once),
  the pointwise order on maps, and [[dataflow-checked-fixpoints]]'s
  liveness instance citing `iterate_le_prefix` and `kleene`.
  Met on the way: [[slice-replay-ignores-section-header]].
