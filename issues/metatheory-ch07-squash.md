---
title: Give Squash its full ch. 07 normalizing-total metatheory pass
status: open
labels: [kernel,delam,metatheory]
created: 2026-08-25
updated: 2026-08-25
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
