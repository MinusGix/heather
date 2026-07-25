---
title: Wf former: finitary branching inductives in the kernel
status: open
labels: [kernel,inductives,metatheory]
created: 2026-07-25
updated: 2026-07-25
---



The kernel round for route C of [[tier1-branching-constructors]]: three new
formers (`Vec`, `Fin`, `Wf`) giving finitary branching inductives with
Σ-tuple children and a `Fin`-indexed ih. Design: `docs/wf-former-design.md`
(rules frozen there before code, per repo discipline); decision record:
`docs/branching-inductives-choice.md` §15.

Acceptance: replay `crates/elab/tests/branching_route_c.rs` and
`branching_route_c_nary.rs` against the real formers — every β-marker
deletes to `refl` — plus conversion tests pinning open-subterm β,
canonical-form uniqueness, and neutral-arity behaviour.
`branching_route_a.rs` stays unchanged as the record of the road not taken.

Phases (each its own unit, per the design doc §9):

1. `Vec` + `Fin` formers (two type-reductions each, own conv tests).
2. `Wf`/`sup_f`/`elim_Wf` typing + β, with the `nth` schema materialized.
3. rec.rs round: 8 code-recursor branches (37 → 45), five parallel
   transcriptions; `tm_elim_wf` telescope ≈ `tm_elim_w`'s.
4. ch. 07 LR round — carries the decision's ONLY remaining falsifier: if
   `Wf`'s LR case needs a new idea rather than a finitary restriction of
   `W`'s, reopen [[tier1-branching-constructors]] with route A as fallback.
5. Generator round (one regime: tier 0/1 fold in, fording retires to a
   stress suite) — then [[tier1-branching-constructors]] closes.

Also in scope, decision-independent: `Empty`-η in conv.rs (cheap, plainly
sound, improves the tier-2 `Acc` story regardless).

## Log

- 2026-07-25: 2026-07-25: Phase 1 landed — Type::Vec and Type::Fin in the kernel. Reductions on the length (Vec(T;0)⇝Unit, Vec(T;S k)⇝Σ(_:T).Vec(T;k), Fin(0)⇝Empty, Fin(S k)⇝Unit+Fin(k)), neutral at a neutral length with structural congruence there; formation rules (Vec at its element's level, Fin at 0, length checked at Nat); no introduction/elimination forms — all eta is inherited through the reductions, which is the design's whole premise. Sites touched: term.rs (enum), subst.rs (length at same depth, no binder), reduce.rs (step_type + is_whnf_type/is_neutral_type keyed on whether the length is stuck + explicit beta_elim_ty block), typing.rs (formation + not_code_layer gate), conv.rs (neutral-length congruence + tm_nf neutral-type arm), fmt.rs. GATE: Vec/Fin are rejected at layer c until phase 3 gives them code formers and rec.rs branches, so boxed code stays exhaustively recursable; beta_elim_ty returns None (stuck) rather than mis-firing as belt-and-braces. Tests: crates/kernel/tests/vec_fin.rs (12), including sigma_eta_reaches_through_vec — for a NEUTRAL tuple cs : Vec(Nat;2), cs is convertible with its own projections repackaged, i.e. the equation route A needs funext for, discharged here by existing Sigma-eta + Unit-irrelevance. Also added Vec/Fin to the property-test type generator (common/mod.rs arms 16/17, >20/300 hit rate verified by test), so subst_laws/conv_properties/reduce now exercise them; full suite 289 passing.
