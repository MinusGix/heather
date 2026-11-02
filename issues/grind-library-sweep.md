---
title: Sweep the library's hand trans/cong chains with grind, and record what blocks it
status: open
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

Try grind_report on the library's hand equational chains; record per proof whether it closes, what blocks it (premises, constructors, case splits, arithmetic, cost), and replace the proofs it closes cleanly. Feeds [[grind-lemma-premises]], [[grind-constructor-facts]], [[grind-splits-and-theories]] ([[grind-port]]).

## Log

- 2026-11-02: First pass done (docs/grind-design.md §10): eight proofs sampled across memory, int, float, native, parser and bitvec. Blockers in order: premises ([[grind-lemma-premises]]), definitional equalities ([[grind-definitional-equalities]]), conjunction locals ([[grind-read-conjunctions]]) and constructor facts ([[grind-constructor-facts]]), case splits ([[grind-splits-and-theories]]). Fixed in grind: a round outgrew the host's per-evaluation fuel (each lemma's matching now its own evaluation), and the report's class listing was cubic. No proof was replaced: what closes today needs its instances written out. Rerun the sweep after premises land.
- 2026-11-02: Premises landed ([[grind-lemma-premises]], docs/grind-design.md §11.4). The two proofs the first pass found blocked on premises now close and are replaced: `Memory::set_set_comm`'s three non-absurd branches are each `by grind_using(["Memory::get_set_hit", "Memory::get_set_other"], [])` (premises are the branch locals, matched up to `Defeq` over another memory with the same space), and `commit_chain`'s three branches are each a `grind_using` of the three `commit_*` lemmas with the one derived order fact as a hint. memory.hthr and parser_diagnostics.hthr now import grind. The rest of the sample stays blocked as before (definitional equalities, conjunctions, constructor facts, case splits).
