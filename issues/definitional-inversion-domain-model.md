---
title: Definitional inversion for Heather's kernel inside Heather, by a domain model
status: open
labels: [metatheory,research,design]
area: mathematics
milestone: [math-metatheory]
created: 2026-10-25
updated: 2026-10-25
---

Research rung, not scheduled. From the definitional inversion survey
(`docs/definitional-inversion-survey.md`, which has the argument), on
Carneiro, Coquand et al., arXiv:2607.13662.

**The idea.** Injectivity and disjointness of type formers, sort
injectivity, subject reduction, progress and uniqueness of types can be
proved without normalisation: a domain model whose compact elements are
finite data, and a logical relation defined by recursion on those finite
witnesses, in an ambient logic with only `Nat` induction. It works for
`𝒰 : 𝒰` with Π-η, so Gödel does not limit it: Heather can prove these
results about a theory at least as strong as itself, including (if the model
extends) its own kernel. The relation lives in `Ty 0`, with no quantification
over relations, so predicativity is no obstacle.

**Rungs.**

1. MLTTη (Π, `𝒰 : 𝒰`) in Heather: de Bruijn syntax, typing as the diagonal of
   one conversion judgement, compact elements `Cₙ` by recursion on `n` with
   step functions as lists (a setoid, no quotient), semantic typing as a
   `Bool`, the relation by recursion on the witness. Theorems:
   Π-injectivity and subject reduction.
2. Heather's negative core: Σ and unit with η, `Nat`, proof-relevant `Id`,
   the level tower with sort injectivity, `sEq`/`sEmpty`.
3. Positive formers (`W`, `Wf`, `IWf`, `M`) and the DeLaM code layer, after
   the heather-coq questions below.

**Questions for heather-coq** (probe-sized):

- Does the domain model extend to `□`, boxed-code syntactic comparison and
  the code recursor? The paper gives no evidence for layers.
- Does `AlgSound.v` use anything from `Validity/Reducible*` beyond
  inversions? Answered on 2026-10-25 (survey §3; port assessment §6): for
  the negative core it uses only injectivity, plus whnf inside
  `red_ty_sound`/`red_tm_sound`, which subject reduction replaces. The rest
  is four layer-M equations, which wait on the code-layer question above.

**Not given by the technique:** normalisation, canonicity, consistency,
decidability of conversion, inversion for neutrals. Those keep the port
assessment's limit and its reflection schema.
