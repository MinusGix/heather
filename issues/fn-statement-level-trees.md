---
title: A fn statement's Π levels are raw ⊔ trees, copied into every App annotation read off it
status: open
labels: [elaboration,representation,performance]
created: 2026-09-15
updated: 2026-09-15
---

Found by the 2026-09-15 spelling design pass (docs/closed-argument-and-parameter-domain-spelling-design.md §5.3). `crates/elab/src/lib.rs`'s statement closing loop ("Close over the telescope", ~3396) accumulates `Level::max(dom_lvl, stmt_lvl)` raw, where `lower_shape`, `wrap_tel` and `register_ty_code_fn` all end with `.normalize().canonical()` and `Level::join` exists as the smart constructor. Every fn statement's Π therefore carries a quadratic `⊔` tree (`(1 ⊔ ((0 ⊔ 0) ⊔ (0 ⊔ (0 ⊔ (0 ⊔ (0 ⊔ 1))))))` in the close_body trace) that is copied into every App annotation read off the statement. The trace says it is not what makes those comparisons miss (both sides carry the same tree) but it is a large fraction of what the kernel renders and copies; `docs/annotation-component-respell-design.md` §6 item 2 found the same defect at the inductive lowering's joins and it was worth as much as the respell there. Two-line fix at the closing loop, equiv-preserving by construction; lands as its own commit with its own before/after, never smuggled into a spelling round. Related: [[elaborator-canonical-type-spelling]].
