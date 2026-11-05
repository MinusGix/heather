---
title: Read casts once for every arithmetic tactic, and state the goal wanted with cast_to(S)
status: open
labels: [tactics,casts,reals]
area: tactics
created: 2026-10-30
updated: 2026-10-30
---

The cast tactics' second half (docs/casting-design.md §6.4, §9): one
reader that builds an expression tree whose nodes record the carrier they
are computed at, with the cast edges (`OrderedRingHom` values,
`lib/std/algebra/morphism.hthr`) between carriers, shared by `ring`,
`linarith`, `mono`, `omega` and a new `cast_to(S)`.

- **The reader** pushes images to the leaves along the edges' fields
  (`add_law`, `mul_law`, `neg_law`, `zero_law`, `one_law`) and lifts a
  comparison of two images of one edge to the source (`le_of_map_law`), and
  emits those laws as part of the tactic's certificate. Slice 1's
  `cast_move` (`lib/std/tactic/cast.hthr`) is one layer of it.
- **`cast_to(S)`** reads the goal and `S` through it, checks they agree
  modulo the laws, and replaces the goal by `S`; a disagreement names the
  first subterm where the two readings differ. `have h: S := cast_from(h0)`
  for a hypothesis.
- **Consumers**: a hypothesis stated at the pushed form then matches an
  unpushed goal (what `mono`'s layer-by-layer reading cannot do), and
  `ring`'s spelling-based cast reading (`RingExpr::of_nat_add`, …) moves
  onto the edges.

Customers left by slice 1: `dyadic.hthr`'s own order lemmas
(`Dyadic::neg_le`, `rat_pos`, …, each a `Rat` lemma between two image
laws), `interval.hthr`'s `widen_has`, and the `rat_add`/`rat_mul` calls in
`lib/std/num/float/arith.hthr`, `round.hthr`, `series.hthr`, `error.hthr`.

## What it assumes from elsewhere

- **[[casting-standard]]** owns the edges and the surface. Assumed here:
  only that an edge is an `OrderedRingHom` value whose fields are its laws.

## Log

- 2026-10-30: Slice 2 (docs/casting-design.md §10): cast_push normal form over a carrier table (Rat, CReal), cast_from(h) (pushed/pulled/lifted one or two edges/≈), cast_to(S, prove), and mono closes a goal from a fact that agrees through casts. Left here: ring/linarith/omega on the same normal form, a located diagnostic for a disagreement, 0/1/sub moves, Nat→Int, and the slice-1 customers listed above.
- 2026-10-30: Slice 3 (docs/casting-design.md §11): ring reads edge images through definition facts (edge fields, no morphism import), linarith substitutes definitions into its forms, omega unchanged by design. Left: cast_from's located diagnostic, 0/1/sub, Nat→Int edge, remaining hand-named image laws in the float library.
- 2026-10-30: Slice 4 (docs/casting-design.md §12): sub/0/1 in ring and cast_push; Nat→Int as an OrderedSemiringHom edge (Int::ofNat_hom), Int as a cast carrier, ring reads Nat images by the edge law as atoms; cast_from/cast_to name the first differing subterm; float arith/round/series image laws by ring/cast_from/linarith. Left: wrappers read as images (Finite::val, Format::grid, CReal::at), Dyadic as a carrier, mono pushing before matching heads, morphism-import degradation, and `↑`/`cast<B>` (casting-standard).
- 2026-10-30: Slice 5 (docs/casting-design.md §13): missing morphism import named; cast_from lowers order goals along an edge out of their carrier (Dyadic goals from Rat facts), Dyadic a cast carrier; ring reads definitions that unfold to edge images (Finite::val, Format::grid); mono reads x - y as x + -y against an unshared side. Left: field-read spellings (CReal::at), ofInt across two edges, constructor-computed negation; the `↑` surface is casting-standard's.
- 2026-11-05: gardener: cites a file it shares with [[cast-from-at-class-carrier]] (`lib/std/tactic/cast.hthr`); [[floating-point-formalization]] (`lib/std/num/float/arith.hthr`).
