---
title: Tactics and lowerings build certificates as terms, never as re-elaborated source
status: open
labels: [design,tactics,elaboration,diagnostics]
area: tactics
created: 2026-10-31
updated: 2026-10-31
---

Item 3, part 1, of the fundamental-improvements memo of 2026-10-31 (Claude Doc, https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s): generated proofs are built as elaborated terms,
never printed as Heather source and re-elaborated.

*Spelling* is the largest single bug class in the tracker: 164 open issues
mention it (2026-10-31). Every generator that prints source and re-elaborates
it can fail where the term itself was fine:

- [[omega-certificate-bare-nil]]: `omega`'s certificate prints a bare `Nil`,
  which no longer infers;
- [[decreases-measure-record-field-unspelled]];
- ring's "generated source must not use `list::Nil`" rule.

## Scope

- Audit: list every generator that spells source and re-elaborates it
  (`omega`, `ring`, `linarith`, `nlinarith`, `norm_num`, `split_all`, the
  `decreases` and `?` lowerings, derive). For each, record what it spells and
  why.
- Build their output as typed terms over handles, the way the `Tac` host
  interface already works with `Expr`. Printing is for display only.
- State which rules in `docs/proof-patterns.md` this retires.

## Done when

No tactic output is re-parsed, the audit's issues are closed or re-pointed,
and a generated certificate that fails can only fail in the kernel, with a
located term.
