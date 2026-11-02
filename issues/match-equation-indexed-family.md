---
title: The match equation on an indexed family is the packed Σ equation
status: closed
labels: [elaboration,match,indexed-families]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Slice 6 of [[dependent-match-compiler]] (docs/dependent-match-compiler-design.md §9).

Replace the refusal in docs/match-equation-split-design.md §4 with `⟨i, s⟩ = ⟨idx(C, x̄), C(x̄)⟩ : Σ(j: I). F(j)`, convoyed through the two-binder family motive `λ j z => Π(p: ⟨i, s⟩ = ⟨j, z⟩). M(j, z)`. It must commute with `iwf_match_motive`'s index inversion (tiers 1–2, [[iwf-inversion-recursive-index]]).

## Done when
- `match h:` on a `Vec`/IWf family checks, and `cong(fst, h)` gives the index equation.
- Inversion tiers still close impossible arms.

## Log

- 2026-10-31: Done on PR #318 (design §9.1): elab_convoy_packed for IWf/W and route-1 families; cong(h) reads the index through Lgg::projection_hole (fst/snd of a pair witness, first components up to conversion in the conversion pass). Tests in match_equation_split.rs and positional_if_let.rs. Left: with h, an IWf family whose index inverts no longer drops impossible arms (the packed motive is the plain generalization); they close by absurd on cong(h). Without h nothing changed.
