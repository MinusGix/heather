---
title: Give Squash its full ch. 07 normalizing-total metatheory pass
status: closed
labels: [kernel,delam,metatheory]
created: 2026-08-25
updated: 2026-10-16
---

[[sprop-squash]] landed with the metatheory sketch in
`docs/metatheory-ch07-extensions.md` §27: inhabitants are definitionally
irrelevant only after both sides weak-head normalize, because the eliminator
makes normalization operationally observable. This is a new
**normalizing-total** relation, unlike the shape-free total relations for
`Unit`, `sEq`, and `sEmpty`.

Give that sketch the same full fundamental-theorem treatment that
[[metatheory-ch07-sprop]] gave the earlier strict formers. In particular,
walk every shared lemma affected by requiring normalization before forgetting
shape; prove the dependent eliminator case, closed canonical forms, and the
code-layer structural cases rather than relying on the implementation tests.

## Acceptance

- State the Squash type and term relations at every layer and universe.
- Prove normalization of both related inhabitants before irrelevance erases
  their canonical/neutral shape.
- Prove formation, introduction, dependent elimination, beta, conversion
  soundness, and closed canonical forms.
- Cover all four code-recursion branches and the fact that quotation preserves
  witness syntax without adding live readback.
- Recheck the shared substitution/reduction-expansion lemmas against the
  stronger relation; record an abort criterion if they require relevance
  marks or a new sort.

## What it assumes from elsewhere

- **[[sprop-squash]]** owns the frozen implemented rules.
- **[[metatheory-ch07-sprop]]** owns the preceding with-code FT framework for
  `sEq`/`sEmpty`. Assumed here: its layered LR and strip treatment as the
  starting document, not its total irrelevant relation as Squash's answer.

## Log

- 2026-08-25: Filed from the implementation review. The §27 sketch records
  the key new relation and canonical-forms argument; this issue owns the full
  pass through the shared metatheory.
- 2026-10-16: Closed: the full pass is machine-checked in the Coq formalization (heather-coq, `M16_DESIGN.md`; main @ 16ed0d5), with no admits or axioms, every headline theorem closed under the global context. M16a (2026-10-10) is `Squash`/`squash`/`ind_∥∥` at layers D and M. The relation is the probe's clause (`probes/SquashProbe.v`, heather-coq#8): a term is good alone when it reduces to a `squash` whose payload is related to itself, or to a self-related neutral, and two terms are related when each is good, so normalization comes before irrelevance forgets shape. The payload's self-relation is the one refinement of §27, which asks for no relation on payloads: β instantiates the step's validity at the payload, which needs it. Proved: formation, introduction, proof irrelevance, dependent elimination (`V_elimSq`, each scrutinee analysed alone), β, no η, injectivity, preservation, type uniqueness, decidable conversion (`actmnf_sq_irr` relates any two whnfs, `actmne_elimSq` compares no steps, as `conv.rs`) and closed canonicity to a `squash`. M16b (2026-10-13) is the code `∥s∥` (`El ∥s∥ ≡ ∥El s∥`), the lift to every layer but V with β and irrelevance kept at D/M, and the four code-recursor branches 51–54 with Heather's scopes, validated by `rec_code`; their reducts are syntactic, so quotation adds no readback. The shared substitution and reduction-expansion lemmas went through unchanged: no relevance marks and no new sort, so the abort criterion never fired.
