---
title: The decreases unfolding walk goes through a convoyed match, on any scrutinee
status: closed
labels: [elaboration,proofs,recursion]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Slice 4 of [[dependent-match-compiler]] (docs/dependent-match-compiler-design.md §8). Needs [[match-equation-in-every-arm]].

The walk (`measure.rs` `match_at_anchor`, docs/decreases-unfolding-design.md §3) refuses an equation binding and a computed scrutinee. A convoy `elim(e, Π(p: e = z). M, λ p. bᵢ)(refl)` is re-matched at a fresh `s` under `λ s => Π(p: e = s). elim₁(s)(p) = elim₂(s)(p)` and applied to `e` and `refl`. Both anchors then step in each arm. Lifted `f#obl_N` telescopes take the arm's equation when the obligation reads it.

## Done when
- `cd_loop_unfold` (probe P5) and PR #316's `count_down_unfold` are generated; `merge`'s negative control in crates/elab/tests/decreases_unfolding.rs flips to positive.
- Closes [[unfolding-computed-scrutinee]]; unblocks R3b of [[pure-imperative-statements]].

## Log

- 2026-10-31: Landed: Respell::convoy_at_anchor walks a computed or equation-bound match by rendering f#body's spelling with a fork of the rewrite; lifted obligations state arm equations about the scrutinee expression (not the __dec_scrut alias) and take any arm equation as a candidate fact. merge_unfold, cd_loop_unfold, count_down_unfold generated (docs/dependent-match-compiler-design.md §8.1).
