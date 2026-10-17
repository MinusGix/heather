---
title: IWf: finitary inductive families as a former, with no stored index equation
status: open
labels: [kernel,design,delam,metatheory]
created: 2026-09-30
updated: 2026-10-17
---

Owns the `IWf` former round: `docs/iwf-former-design.md` (rule set
frozen 2026-10-13, not implemented). This is [[indexed-families]]'s route 4,
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

## Status (doc §12, §13)

The rule set (doc §1–§6) is frozen, 2026-10-13. Nothing is implemented in
the kernel. The Coq formalization has checked the frozen rules (typing at
every layer but V, computation at D and M), with the code-recursor
branches derived there before `rec.rs` has them (heather-coq
`M17_DESIGN.md`; Log, 2026-10-16). What
is still open is the generator's and changes no typing or reduction rule:
inversion at parameterized or container index types (§12.1), mutual
families (§12.2) and migrating route 2b's declarations (§12.4). An
independent review of `docs/no-uip-model.md` §4 is written
(`docs/no-uip-model-review.md`), and its three local fixes and four
missing steps are applied (§4.4a there). It backs the no-UIP claim and
does not gate the freeze (§12.3). `Vec`/`Wf` stay
separate formers now, with abbreviations as the target (§10).

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
- 2026-10-13: Decided with the user: doc §1–§6 are frozen after a review that changed no rule. Three wording edits came out of it. (1) §1 now says where the formers live: as `Wf`'s, gated out of layer c until the rec.rs round. (2) §1.1 and §10: `Vec`/`DVec(_; _. T)` and `Wf`/`IWf` at `Unit` are translations, not conversions. At a neutral length they are distinct neutral types, and `elim_Wf`'s ih goes through `nth` where `elim_IWf`'s goes through `dnth`. (3) §3: the ih's type is `F[i]` only up to β, which adds a step to the formalization's hardest `Wf` lemma (`V_nth`); its IWf relation probe checks this first. §10 is decided: option 1 now, option 2 (abbreviations) as the target, after the generator, accepting that it may be slower at first. The no-UIP §4 review is decoupled from the freeze (§12.3, §13 step 1). The stale "Open, before freezing" paragraph is replaced by a status paragraph.
- 2026-10-16: The independent review of `docs/no-uip-model.md` §4 is written: `docs/no-uip-model-review.md`. The outline holds and nothing found touches `UIP₀`, but the interpretation as written misses three rules, each with a local fix: `eqtm_ubeta` when code mentions a bound level (box must evaluate levels), `eqtm_capp` and the other D-conversion congruences (`CΠ`/`TΠ` over conversion classes, with a new representative-independence lemma), and a boxed definition (normalize box values by `unf`). It also lists four missing steps: the recursor's D/V binders, the order of (M1) and the renaming lemma, the lemma's hypotheses, and level binders under `σ` (`guwkn_gosubst`).
- 2026-10-16: The frozen rules are machine-checked in the Coq formalization (heather-coq `M17_DESIGN.md`, main @ 16ed0d5), with no admits or axioms and no change to Heather's rules. M17a: `DVec` at D and M, and `dnth`'s index lemma `V_dnth`, which answers the freeze's one open question: the ih's type being `F[i]` only up to β (doc §3) adds one validity step to `V_nth`'s composition and goes through. The neutral-tuple property is checked on doc §3's own instance (`dnth_reds_example`). M17b: `IWf`, `sup_i`, `elim_IWf` and β on open data at D and M, through the relation (`Wf`'s, with the index an index of the families), the fundamental theorem, decidable conversion, type checking and the consequences. M17c: the codes `TmDVec`/`TmIWf`, the lift to every layer but V, and the six code-recursor branches (`ty_dvec`, `tm_dvec`, `ty_iwf`, `tm_iwf`, `tm_sup_i`, `tm_elim_iwf`; there 55–60), their scopes derived from the layer-C typing rules and validated by `rec_code`. Those scopes are the first precise statement of doc §6, so §13 step 4 (the rec.rs round) checks Heather's branches against them, as M15b did for `Wf`'s, rather than the other way round. `dnth`'s de Bruijn transcription is likewise the statement for step 2's materialization.
- 2026-10-17: The review of `docs/no-uip-model.md` §4 is applied (its new §4.4a maps each finding to its fix). Box values are level-closed and unfolded, environments are `(v, ρ̂)` with V-globals, `CΠ`/`TΠ` range over D-conversion classes with a new representative-independence lemma (M3), the recursors recurse on typed code with `t_λ`'s codomain read up to D-conversion, and the lemma gains its layer-correctness hypothesis, its proof order, (S4u) and the semantic universe substitution lemma. The two pieces the review suggested mechanizing are checked in heather-coq: the `□` fibres' invariance under D-conversion (`Typing/BoxFibre.v`) and `unf`'s idempotence (`unf_idem`, `Syntax/Unfold.v`).
