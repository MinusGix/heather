---
title: The match equation on an indexed family is the packed Σ equation
status: open
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
