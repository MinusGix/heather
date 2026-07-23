---
title: Implement algorithmic convertibility checking (ch. 06)
status: closed
labels: [kernel, delam]
blocked-by: [kernel-reduction]
created: 2026-07-22
updated: 2026-07-22
---

The ch. 06 convertibility judgments, rule for rule: reduce both sides to
WHNF, compare structurally; mutual functions for types / normal types /
neutral types / contexts / terms / normal terms / neutral terms / local
substitutions.

Key shapes to preserve:

- Neutral comparison is an *inference* step returning a type (left-biased;
  ch. 08 shows why that's sound).
- η-directed comparison at all four function types (Pi, UPi, CtxPi, TyPi):
  compare applications to a fresh variable.
- Boxed types/terms compare by syntactic equality (α-equality is free
  under de Bruijn).
- Universe levels compare via level.rs normalization at every annotation
  the rules check.
- Neutral recursors: compare motives + all 13 branches + indices (the
  `C_A` group).
- Layer index restricts types, not terms — conversion at layer p can
  relate layer-m terms at MLTT types (critical property, ch. 06 intro).

Termination is justified by the decidability development (ch. 07/08); the
implementation should take a fuel parameter anyway so the checker is
total-by-construction and a fuel-exhaustion is a distinguishable error.

## Log

- 2026-07-22: Ready to start: reduction landed. Pointers: use reduce::whnf_type/whnf_term (fuel-bounded) then compare structurally per ch. 06; classification predicates (is_whnf_*/is_neutral_*) are in reduce.rs. Neutral comparison is an inference step returning a type; eta for all four function-type flavors compares applications to a fresh variable (extend Gamma / push a universe var / push a global binding per flavor); boxed types/terms compare by syntactic equality; recursor-neutral comparison needs the C_A premise bundle (motives, all 13 branches, indices). Level equivalence is Level::equiv. Reduction needs the ambient Gamma shape - conversion will thread the real contexts anyway.
- 2026-07-22: Implemented in crates/kernel/src/conv.rs: the nine ch. 06 judgments as mutual fns on a fuel-carrying checker (shared budget across reduction steps and comparison nodes; OutOfFuel distinguishable from NotConvertible). Neutral comparison infers left-biased (type+level); eta at all four function types; boxes syntactic; C_A compares motives + all 13 branches at instantiated motive types (ch. 04 G_A telescopes, cross-checked against subst.rs map_branches and reduce.rs beta payloads). Two new subst helpers shift_univ_above/shift_global_above view a motive under a branch telescope. Judgment-level inputs are threaded but inert (all checked levels are annotations, via Level::equiv). Two tex typos not followed (noted in module docs): elim^Trm neutral conclusion at l2 not l1; t_app branch substitutes u_s^id not u_t^id. Layer-m term arms bump the layer locally so layer-p conversion relates m-terms (ch. 06 critical property; tested). Golden tests in tests/conv.rs incl. a probe that branch types really use the motive (eta accepted iff motive is a Pi). Handoff to kernel-typing: conv_type/conv_term/conv_local_ctx take (Psi, Gamma, layer, ..., fuel); levels are compared only via annotations so the checker supplies whatever level it has.
