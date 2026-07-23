---
title: Implement the typing judgments / type checker (ch. 04)
status: closed
labels: [kernel, delam]
blocked-by: [kernel-conversion]
created: 2026-07-22
updated: 2026-07-22
---

Syntax-directed checking of fully explicit core terms, mirroring the
ch. 04 judgments: global-context formation, local-context formation and
equivalence, type well-formedness `⊢_i T @ l`, term typing
`⊢_i t : T @ l`, and local-substitution typing — all indexed by layer,
with `typeof(i)` applied where the rules demand it (contexts and types of
layer-v/c/p terms live at layer p).

The heavy corners:

- Layer side-conditions: which rules admit layer v (variables, global
  variables, conversion only); `i' ≤ i` on global-variable use; layer-m
  gating of ULam/box/letbox/recursors/meta-functions.
- The recursor rules: build the branch telescopes (G_M, G_Typ, G_Trm)
  programmatically — 13 branches × (extended Ψ, Γ, L, expected motive
  instantiation). This is the single most error-prone rule; test against
  hand-elaborated instances.
- Non-cumulativity: level equality (via normalization) everywhere, plus
  the explicit level-conversion rule.
- ω discipline: ω appears only as the type level of UPi; reject it in all
  programmer-facing positions.

Endpoint: the milestone in [[end-to-end-compile-instance]] needs this
checker to verify hand-elaborated terms; a nearer smoke test is checking
small MLTT programs at layer p and a tiny letbox/recursor program at
layer m.

## Log

- 2026-07-22: Conversion landed (conv.rs); handoff notes: (1) call conv only on already-checked inputs - it presupposes well-typedness (see DESIGN.md trust-boundary note); (2) API is conv_type/conv_term/conv_local_ctx(Psi, Gamma, layer, ..., fuel) - the judgment-level argument is inert, pass whatever the rule gives you; (3) the checker owns the fuel policy - pick a default and thread it, OutOfFuel should surface as its own type-checking error, not 'not equal'; (4) neutral inference inside conv is left-biased and returns (Type, Level) but the public API discards it - the bidirectional checker computes its own types and only asks yes/no.
- 2026-07-22: Implemented in crates/kernel/src/typing.rs (tests: crates/kernel/tests/typing.rs). Handoff notes: (1) refactor: the 13 branch telescopes + 2 motive scopes moved from conv.rs into src/rec.rs (motive_specs/branch_specs), shared by conversion and typing - edit them in ONE place only; (2) API is check_global_ctx / check_local_ctx / check_type / infer_type / check_term / infer_term / check_local_subst, all taking (psi, univs=|L|, layer, gamma, ..., fuel); inference returns the canonical type/level, checking = infer + conv at typeof(i) + level equiv; (3) box is checking-only; checking descends through Lam/ULam/CtxLam/TyLam, but box in an immediately-beta-reduced meta-function body is NotInferable (documented incompleteness, see DESIGN.md); (4) fuel is per-conversion/per-whnf, not a shared budget; OutOfFuel is its own TypeError; (5) two new tex errata recorded in docs/delam/README.md (letbox scrutinee levels are 0, UPi wf premise layer '1' means m); (6) the identity-recursor tests in tests/typing.rs re-elaborate all 13 telescopes by hand - keep them in sync with rec.rs if the tables ever change.
