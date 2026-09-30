---
title: IWf: finitary inductive families as a former, with no stored index equation
status: open
labels: [kernel,design,delam,metatheory]
created: 2026-09-30
updated: 2026-09-30
---

Owns the `IWf` former round: `docs/iwf-former-design.md` (design sketch,
2026-09-30, not yet reviewed). This is [[indexed-families]]'s route 4,
extended with an output-index function. It is Dybjer's finitary inductive
families in `Wf`'s shape:
- `IWf(I; x:S. n; x. o; x i. c)(m)`;
- `sup_i(a; cs) : IWf(…)(o[a])`;
- children in a dependent tuple `DVec(k; i. F)`.

## Why now

Route 2b stores an index equation in every value, and uses it through
`transp` with the strip. [[sprop-strip-normalization-open]] found two costs
the round had not priced:
- The strip is Werner's rule, open predicatively.
- A computing `transp` into relevant motives gives UIP for `Id`.

A constructor that *is* at its result index stores nothing, so neither
cost arises.

## What the design claims

The full argument is in the doc. Items marked checked have a Coq probe:
`../Lean/delam/probes/IwfProbe.v`.

- β fires on every constructor on open data, including at a computed
  result index. There is no form B. (checked)
- Value equality is equality of the shape and the children, with no
  proof component. Cross-spelling holds by conversion.
- Fording's F1–F3 rejections lift, because child indices are stored, not
  recomputed. (F2, F3 checked)
- `dnth` is derivable in the kernel's first-order style: a fixed family,
  with the motive quantifying over an embedding `Fin k → Fin n`. It
  reduces to projections on a neutral tuple. (checked)
- Inversion at a constructor-headed index is form A's motive device,
  kept. (checked on `vhead`)
- There is no negative premise, conversion premise or strip in
  reduction, and no stored proof.

## Open, before freezing (doc §12)

The family's level (`l ⊔ li` or `l`); whether `transp` is removed or
restricted to strict motives (a `docs/sprop-design.md` revision); a model
argument for no-UIP; and matching without K at non-invertible indices,
which is a new elaborator piece.

## What it assumes from elsewhere

- **[[indexed-families]]** owns the route choice. Assumed here: only that
  route 4 was set aside for its cost, not for a defect.
- **[[sprop-strip-normalization-open]]** owns the findings about `transp`.
  Assumed here: only its two conclusions, UIP and the open normalization
  question.
- **[[wf-former]]** owns `Wf`/`Vec`/`Fin`. Assumed here: their rules as in
  `docs/wf-former-design.md`, which this former extends.

## Log

- 2026-09-30: Decided with the user: (1) `transp` and the strip are removed, with the argument in doc §7; `docs/sprop-design.md` carries a revision note. (2) The family level is `l ⊔ li`, forced by the codes (§1.2). (3) `match` ships tiers 1–2: form A's motive inversion, and index abstraction with no equations. Tier 3, unification without K with deletion only at index types with decidable equality (Hedberg-generated K), comes when an example needs it (§8.3). What remains open before freezing is §12: inversion at wider index types, mutual families, the no-UIP model argument, and migration.
- 2026-09-30: §12.3's no-UIP argument is written: `docs/no-uip-model.md`, on paper and not reviewed. It uses the groupoid model, with `Ty 0` as sets and bijections, so `Id^1(Ty 0; Bool; Bool) = {id, swap}` and `UIP₀` is empty. The strict propositions are unions of connected components of the context; that lemma is proved there. DeLaM's globals and `□` are interpreted in stages over sets of syntactic instantiations, which is argued rather than checked. The same model validates `transp` at strict motives and refutes a relevant `transp`, which confirms the §7 decision.
- 2026-09-30: The components lemma of `docs/no-uip-model.md` §3 is mechanized in `../Lean/delam/probes/NoUipComponents.v`, closed under the global context. Mechanized: strict propositions are transported along context morphisms, strictly stable under substitution, and definitionally irrelevant; `srefl`, `elim_sEmpty` and `ElimSquash`; `transp` at a strict motive exists. In the groupoid of types and bijections: no relevant `transp` (`no_relevant_transp`), and UIP at `Ty 0` fails (`no_uip0`). §4, DeLaM's globals and `□`, remains argued only.
- 2026-09-30: `docs/no-uip-model.md` §4 has been self-reviewed against the Coq formalization's declarative rules. It is right in outline, and three things were fixed. (1) `□`'s discreteness rests on Static Code, which is syntactic only up to level equivalence (`StaticCodeEq.v`), not on `conv.rs`. (2) The interpretation is now three explicit stages, with environments carrying syntax and semantics, plus the semantic global substitution lemma that validates `letbox`'s β. (3) The scope excludes postulated globals. Every layer fact used is a side condition of a cited rule. Still open: an independent review, and the substitution lemma written out case by case.
- 2026-09-30: `docs/no-uip-model.md` §4.2a writes out the semantic global substitution lemma, `⟦t⦃σ⦄⟧ρ ≃ ⟦t⟧(ρ·σ)` for every global substitution `σ`, case by case. It covers globals (substituted and renamed), context globals, boxes, `letbox`, the recursors, `CΠ`/`TΠ` and bodied globals. Its syntactic half cites Coq-checked lemmas: `gsubst_gsubst`, `gsubst_subst`, `gsubst_gren_all`, the `ptm`/`pdef` clauses and `gsubstitution`. Its semantic half uses the standard local substitution lemma and a closing lemma for C/D, proved there. It validates `letbox` β, `CΠ`/`TΠ` β/η and the recursors' β. Still open: an independent review of §4.
