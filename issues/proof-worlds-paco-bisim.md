---
title: Parameterized coinduction (Paco) and up-to proof world for Bisim and Eutt
status: open
labels: [stdlib,itrees,coinduction,proofs]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-24
updated: 2026-11-24
---

Follow-up to [[proof-worlds-native-wp]] targeting `lib/std/itree/` (`coitree.hthr`,
`coitree_eutt.hthr`, `coitree_rec.hthr`).

## Motivation

Today, every `Bisim` or `Eutt` theorem must be written directly as a
syntactically guarded corecursive `fn`: you cannot compose a coinductive
hypothesis with `Bisim::trans`, `Bisim::sym`, `Eutt::tau_l`, or
`CoTree::bind_cong`, because placing any lemma around a corecursive call fails
the syntactic guardedness check. Proofs like `Bisim::mrec_bind_from`
(`lib/std/itree/coitree_rec.hthr`) therefore introduce bespoke step inductives
(`MrecBindStep`) and manually push `j` / `obs_bind_at` / `mrec_at` proofs under
constructors.

## Sketch

1. **Parameterized coinduction (`Paco`):** define `PacoBisim(r, t, u)` and
   `PacoEutt(r, t, u)` as `codata` greatest fixed points `ν X. F(r ∪ X)` (zero
   kernel changes — uses Heather's existing `codata` / `M`).
2. **Up-to closure (`UpTo(r)`):** close `r` under `refl`, `sym`, `trans`,
   `bind_cong` (and `tau_l`/`tau_r` for `Eutt`) and prove compatibility once
   (`Paco::up_to : UpTo(Paco(r)) → Paco(r)`).
3. **`Setoid` + `within Bisim` / `within Eutt`:** give `UpTo(Paco(r))` a
   `Setoid` instance so `calc { … ≈ … }` works directly inside a coinductive
   proof after taking a single guarded step (`step_tau` / `step_vis`), and exit
   at `r := ∅` to produce an ordinary `Bisim` or `Eutt`.



