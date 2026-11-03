---
title: Tactics for proofs up to taus: eutt_simp and up-to coinduction
status: open
labels: [tactics,coinduction,itree]
area: tactics
milestone: [nh-effects]
created: 2026-11-03
updated: 2026-11-03
blocked-by: [eutt-iteration-and-io-reading, codata-up-to-friends-round-2, eutt-setoid-rewrite]
---

Tactics for proofs up to taus, once there are targets to prove
(`docs/effects-capabilities-design.md` §4, decided by Minus 2026-11-03;
Minus: "if there's an annoying part, it can be automated away"). Coq's
answers are paco and the ITrees `euttG` tactics (`ecofix`, `ebind`,
`estep`), and Pous's companion for composable up-to techniques.

## Scope

- **`eutt_simp`**: normalise both sides of an `Eutt` goal by the monad laws,
  dropping taus and unfolding one pass of `iter`/`rec`, through
  [[eutt-setoid-rewrite]].
- **A coinduction tactic** (`ecofix`-style): set up the up-to relation from
  [[codata-up-to-friends-round-2]], and leave one goal per observation
  shape (`Ret`, `Tau` on either side, `Vis`), with the coinductive
  hypothesis usable under `bind` and `trans`.
- **Lockstep**: when both sides go round with one `Tau` per pass, prove the
  agreement by induction on depth, without coinduction.

## What it assumes from elsewhere
- **[[eutt-iteration-and-io-reading]]** owns the lemmas and the proofs that
  are the targets. Assumed here: only that they exist as statements to
  re-prove with the tactics.

## Done when

The hand proofs of `reads_bind`, `reads_iter` and one customer's agreement
(`cat` against its source) are re-proved with the tactics, each shorter
than the hand version.
