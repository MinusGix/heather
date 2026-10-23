---
title: Export codata (the kernel's M former) to Lean and Rocq
status: open
labels: [translation,export,codata]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-23
updated: 2026-10-23
---

The exporter refuses the kernel's codata former `M` (`corec`, `out`;
`crates/kernel/tests/m.rs`) by name, so every declaration of `coitree` and
`coitree_eutt` is refused: 86 bindings in the whole-library sweep of
2026-10-23 (design §7), the first sweep since codata landed (PR #131,
PR #139, PR #143). The sweep's known causes now list it, so it no longer
fails the opt-in `--wide` run.

Neither target has a native coinductive that matches. Lean has none in
its kernel. Rocq's `CoInductive` comes with a guard checker and no
`corec` of this shape. So the question is which of these the export should
be:

- **A prelude realisation over functions.** Build `M` as the limit of its
  finite approximations, as Mathlib's `PFunctor.M` does, and prove `out`/
  `corec` and their β in the prelude. Then nothing is assumed, but the
  prelude carries real proofs, and `corec`'s β may hold only
  propositionally, which the kernel route would reject at every use that
  needs it definitionally.
- **Axioms in the prelude.** Declare `M`, `out`, `corec` and the β rule as
  axioms. Then everything checks, but `#print axioms` stops being empty for
  codata, and the β rule is an equation, not a conversion, so the same
  definitional uses fail.
- **Exported forms that differ from the source** (Minus, 2026-10-21: export
  need not match Heather feature for feature). For example, `M` at a
  bounded depth through `CoTree::approx`, which the library already relates
  to the coinductive tree.

The first thing to find out is which uses in `coitree` need `corec`'s β
definitionally, since that decides between the first two options.
