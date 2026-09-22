---
title: Code payloads have no sharing: a tower-typed value inside a quote is spelled as its reduct
status: open
labels: [kernel,metaprogramming,design,performance]
created: 2026-09-22
updated: 2026-09-22
---

Filed from intro-by-type stage 2 (2026-09-22, `docs/intro-by-type-design.md` §2.3). The checked spellings (`pair@`/`inl@`/`inr@`/`fst@`/`snd@`) fix the ≈3.5ⁿ reduct at the computing layers, but **not inside a `box`**: a quotation payload is written with the component forms, whose annotations spell a tower type's whnf. That was already true before stage 2, and stage 2 does not make it worse. It becomes a real cost once compilation and tactics put tower-typed values into code, which is the direction the project is heading.

## Why the checked spellings cannot simply be admitted into code (decided 2026-09-22)

- **Code equality is syntactic.** Ch. 05's Static Code lemma says equivalence at layers v/c is equality, up to levels. With both `pair` and `pair@` in the code grammar, one term has two unequal codes, and every `code_eq`, `match code` and compiler pass would have to identify them. The readers are user-written metaprograms, so there is no bound on how many would have to see through the second spelling.
- **The recursor branch cannot be stated.** `tm_pair`'s telescope (`crates/kernel/src/rec.rs`) types `u_a`/`u_b` through `U_S`/`U_T`. An unannotated `pair@` offers no type for its children. An annotated one offers a `U : Typ_c` whose Σ-ness no branch can observe, because code variables do not reduce (`docs/ch05-06-lemma-audit.md` §2). A branch would need the components or evidence of the reduction, which is the reduct again.

## The open question

What does a **code-native** sharing construct look like: one whose recursor branch can state its sub-structures' types? One candidate is a code-level binder (branch: `A`, `a : A`, a body under `x : A`, all statable). Decide it against the first real compile or tactic workload whose payloads carry tower-typed values, not before.

## What it assumes from elsewhere
- **[[elab-emits-normal-form-of-matched-type-argument]]** owns the computing-layer fix. Assumed here: only that payloads keep the component forms, with the quote-boundary translation ⌊·⌋ (design §2.3, amended) as the single place that produces them from pasted-in checked spellings. A code-sharing former would be what that translator targets.
