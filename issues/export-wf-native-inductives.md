---
title: Realise tier-1 Wf instances as native Lean inductives
status: closed
labels: [translation,export,inductives]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-20
updated: 2026-10-21
---

Lean cannot declare Heather's `Wf` former: the children `Vec(Wf; n[a])` are
not a syntactically positive occurrence, and checked declarations have no
positivity bypass (`crates/export/probes/WfPositivity.lean`). Neither generic
encoding works (`docs/export-fragment-design.md` §5.1). The realisation that
does work is per declaration: one native Lean inductive per lowered `Wf`
instance, with one constructor per summand of the shape, holding its payload
and its children as fields. `sup_f` maps to a case on the tag, and `elim_Wf`
maps to the native recursor with the ih re-tupled.

`crates/export/probes/WfNative.lean` checks this for `List<A>`. The property
`Wf` exists for holds (`sup_f(tag; cs) ≡ node(nth cs 0, …)` at a neutral
`cs`), and so does β at a canonical tag. β at an **open** tag does not, and
neither does comparing two ihs at an open index. Heather's notes say that
generated code does neither (`crates/kernel/DESIGN.md`, the `Wf` paragraph).

The round:

1. Take the correspondence between a `Wf(S; n)` and its declaration from the
   elaborator's inductive table (the tier-1 lowering,
   `docs/inductive-tier1-wf-lowering.md`), not by matching spellings. The
   `elim_Wf` annotations spell `S` and `n` unfolded, so the exporter needs
   the table to recognise them.
2. Print the native inductive, `supf` and `elimWf` per declaration,
   parameterised by the declaration's parameters.
3. Add a negative control: a hand-written kernel term with β at an open tag
   must export, and must be **rejected** by Lean, so the side condition is
   seen to be checked.

Rocq has the other half of the trade: `Wf` is exact there behind
`bypass_check(positivity, guard)` (`crates/export/probes/WfBypass.v`), but
the property above needs unit η, which Rocq lacks (§5.3).

## Log

- 2026-10-21 (PR #87): done, in `crates/export/src/wf.rs` (design §5.1, "As
  implemented"). Item 1 took a different route from the one written above.
  The declaration is identified by the **nominal tag** its shape carries,
  and its type arguments by walking the instance's payload types beside the
  declaration's own, after evaluation. Neither step matches spellings. The
  elaborator's table supplies only the constructor names
  (`Elaborator::constructor_names`). Items 2 and 3 are as written: the
  library sweep's `List` and every lemma over it pass Lean's kernel, and the
  open-tag control is rejected (`scripts/export-recheck` fails otherwise).
  Still refused by name: arities that depend on the payload, and `IWf`.
  Rocq has no realisation.
