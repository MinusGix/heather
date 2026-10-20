---
title: A fn statement's Π levels are raw ⊔ trees, copied into every App annotation read off it
status: open
labels: [elaboration,representation,performance]
area: language
created: 2026-09-15
updated: 2026-09-15
---

Found by the 2026-09-15 spelling design pass (docs/closed-argument-and-parameter-domain-spelling-design.md §5.3). `crates/elab/src/lib.rs`'s statement closing loop ("Close over the telescope", ~3396) accumulates `Level::max(dom_lvl, stmt_lvl)` raw, where `lower_shape`, `wrap_tel` and `register_ty_code_fn` all end with `.normalize().canonical()` and `Level::join` exists as the smart constructor. Every fn statement's Π therefore carries a quadratic `⊔` tree (`(1 ⊔ ((0 ⊔ 0) ⊔ (0 ⊔ (0 ⊔ (0 ⊔ (0 ⊔ 1))))))` in the close_body trace) that is copied into every App annotation read off the statement. The trace says it is not what makes those comparisons miss (both sides carry the same tree) but it is a large fraction of what the kernel renders and copies; `docs/annotation-component-respell-design.md` §6 item 2 found the same defect at the inductive lowering's joins and it was worth as much as the respell there. Two-line fix at the closing loop, equiv-preserving by construction; lands as its own commit with its own before/after, never smuggled into a spelling round. Related: [[elaborator-canonical-type-spelling]].

## Log

- 2026-09-15: 2026-09-15, measured and NOT landed: canonicalizing the join and the seed at lib.rs's closing loop alone (two lines, part B of the spelling round) against the part-A binary on one box, W=1, calc_parser.hthr: whole-file 77.74 → 77.08 s and maxrss flat (noise), but close_body's misses 7 318 → 15 255 and the Pi/Pi row 8 421 / 0.72 s → 21 070 / 1.30 s. The other side of those comparisons (a callee's codomain instantiated by the kernel, or a Π built by another emitter) still carries the raw tree, so pairs that were syntactically equal now differ in level spelling and fall to the value domain — spell both sides alike or neither. The fix is canonical levels at every Π/λ level-slot emitter in the elaborator (and the kernel's instantiation preserving canonicity), landed as one slice with the level profile of every emitter audited, not at one site. Reverted; the issue stays open with this as its datum.
