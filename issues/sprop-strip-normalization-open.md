---
title: The sEq strip is Werner's rule: MX §19.2 needs normalization, which is open predicatively
status: open
labels: [kernel,delam,metatheory,sprop]
created: 2026-09-30
updated: 2026-09-30
---

Found by the Coq formalization of DeLaM's extensions
(`~/Kairos/Code/Lean/delam`, `M10_DESIGN.md` S1–S5). M10a (`sEq`,
`srefl`, `sEmpty`, both irrelevance laws, at D and M) is checked through
the whole stack, with no axioms. `transp` is blocked on this issue.

## The gap in MX §19.2

The relation reads terms over `⇝ₛ`. A stuck `transp` is strip-normal
when `Γ ⊬ a ≈ b`. The Kripke quantifier then needs that negation to
survive every weakening `Δ ≤ Γ`, which means strengthening declarative
conversion: from `Δ ⊢ a⟨ρ⟩ ≈ b⟨ρ⟩`, conclude `Γ ⊢ a ≈ b`.

§19.2's proposition covers only an added `sEq` hypothesis. It argues from
the absence of equality reflection, which is a sound intuition but not a
proof. Transitivity lets a derivation pass through middle terms that
mention the new variable. In addition:

- A Kripke weakening may add any type, not just an `sEq` hypothesis.
  This includes empty types, where substituting an inhabitant does not
  help.
- Strengthening for declarative equality is normally a corollary of
  normalization. Here the normalization proof needs it first.

The same assumption carries §20.4's Weakening row ("nothing, *given*
§19.2's proposition") and §21.3's stuck arm. That arm splits classically
on `a ≈ b`.

## Why the gap is not a missing lemma

`transp` with the strip is Werner's rule: the eliminator of his
proof-irrelevant type theory (LMCS 2008), `Eq_rec A P a b x e ⊳ x if
a = b`.

- Abel and Coquand (LMCS 2020, arXiv 1911.08174) show it breaks
  normalization with an impredicative sort of propositions. Open terms
  diverge; consistency and canonicity are not at stake.
- Their open question (3) is our case: does Werner's rule preserve
  normalization in the predicative case?
- `docs/sprop-design.md`'s introduction says that predicativity "keeps us
  clear of the Abel–Coquand failure mode". That is true of their
  counterexample, but no normalization proof is known.
- Any proof of §19.2's proposition for the full theory amounts to such a
  normalization proof.
- Later work avoids the rule. Pujet and Tabareau's CCobs (POPL 2023)
  makes cast along reflexivity propositional (Rule Cast-Refl), and its
  cast computes on type structure. The TYPES 2024 implementation refuses
  the rule.

## Two facts that narrow the choices

These were checked on paper in the formalization (S5 there).

- **The choice of premise does not change the declarative theory.** Take
  a strip rule with any premise that holds reflexively on typed terms.
  With `transp`'s endpoint congruence and conversion, it already derives
  `transp(…; a; b; e; t) ≈ t` from `a ≈ b`. So a context-free premise,
  such as joinability, changes only the operational side, and there it is
  incomplete for Heather's rules. For `x : Unit`,
  `transp(…; x; ⟨⟩; e; t)` must strip.
- **Stratifying the strip premise by derivation depth fails.** In this
  scheme stage `n+1` strips on equality at stage `n`. The endpoint
  congruence lets stage `n+1` strip through its own equations, so the
  stages separate nothing, and the counterexample appears at stage 1.

## The decision (Heather's)

- **Keep Werner's rule and claim less.** A model of closed terms has no
  Kripke quantifier, so the gap does not arise there. It can prove
  consistency and closed canonicity with the rules exactly as frozen. It
  needs a classical case split, and it gives neither normalization of
  open terms nor decidability of conversion. Kernel completeness and
  termination would then rest on an open problem.
- **Change the eliminator towards CCobs.** The cast computes on the
  motive's instances, and the strip is kept only at neutral instances, or
  made propositional. Normalization is known for this in the predicative
  setting (TTobs). The cost is a redesign of `transp`. It has to be
  checked against route 2b's customer: closed programs need the cast to
  compute at data instances, which this design keeps.
- **Treat question (3) as research.** This is unbounded.

## What it assumes from elsewhere

- **[[metatheory-ch07-sprop]]** owned the with-code FT pass over MX
  Part III. Assumed here: only that §19.2 and §20.4 read as quoted above.
- **[[sprop-strict-prop]]** owns the frozen rule set. Assumed here: only
  that `transp`'s strip is a declarative equation with premise
  `Γ ⊢ a ≈ b : I @ l` at every motive type, and that it has an endpoint
  congruence.

## Log

- 2026-09-30: Independent of normalization: `transp` into relevant motives with β at `srefl` (even propositional β), together with `sEq`'s irrelevance, proves UIP for `Id`. `fromS e := transp(z. Id(u; z); e; refl)` and `toS` by J satisfy `fromS (toS p) = p` by J, and `toS p ≡ toS q` by irrelevance. Checked in Coq with an abstract interface (delam `M10_DESIGN.md` S6); this is GCST's "without K" point. The frozen rule set therefore has UIP for `Id`, and so does any CCobs-style variant. Avoiding UIP means `sEq` eliminates only into strict propositions, and route 2b's form-B arm needs another shape.
