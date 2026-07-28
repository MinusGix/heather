---
title: Design and build the elaborator (surface -> kernel core)
status: closed
labels: [frontend,elaboration,design]
created: 2026-07-23
updated: 2026-07-27
---

The frontend-first route (decided 2026-07-23, superseding "milestone next"):
build the elaborator, gate it on [[stress-proof-suite]], then reopen
[[ir-simulate-design]] in-language. Rationale: the inductive-encoding
translation ([[inductive-compiler]]) is on the critical path of *every*
other direction (the IR is an inductive), and hand-elaboration in the
maximally-explicit core is the wrong way to develop it. Requirements
tracker: [[front-end-sugar]]; syntax: [[surface-syntax]].

## Architecture decisions

- **Untrusted, kernel-as-oracle.** The elaborator calls the kernel's whnf,
  level normalization, and substitution operations directly (same
  workspace); it never reimplements the theory. Final output is re-checked
  from scratch by `typing.rs`, so elaborator bugs are rejections, not
  unsoundness. Exception: it cannot call kernel *conversion* on meta-headed
  terms (conversion treats neutral globals as rigid) — the unifier is its
  own comparison loop mirroring `conv.rs` structure, producing constraints
  where conv.rs would say NotConvertible, using kernel whnf for reduction.

- **Metavariables are Ψ-globals.** The load-bearing idea: DeLaM's global
  context *is* a contextual metavariable context (the theory is a CMTT).
  A hole = fresh `u : Trm(Γ ⊢ T @ l)` binding; occurrences are `u^δ` with
  the kernel's delayed substitutions; solving = global substitution σ
  (already implemented + property-tested); the Miller pattern condition is
  syntactically visible as "δ is a variable renaming". Terms-with-metas are
  genuinely well-typed in the extended Ψ, so the kernel's
  well-typed-inputs trust boundary is respected. Scope/occurs safety rides
  the three-namespace de Bruijn split and the subst laws.

- **Level metas are L-variables**, solved by universe substitution φ.
  Non-cumulativity means *no ≤ constraints exist* — level inference is pure
  unification over count/adjust normal forms (max-plus expressions), not
  semilattice-inequality solving. Solve the pattern cases; residual free
  level vars: generalize into `ΠΠ ℓ⃗` **only at layer m** (universe
  polymorphism is layer-m only — must check), otherwise demand annotation.
  Predictably incomplete over magically flaky.

- **Bidirectional**, leaning on the kernel's own design: every core form
  but `box` synthesizes, so elaboration is mostly annotation-filling;
  checking positions carry motives/contextual types downward (`match`,
  `code { }`).

- **Definition story (split by whether it computes):**
  - `def` (must compute — simulate, arithmetic): **inline at elaboration**,
    β-substituted away; `Rc` sharing keeps cost sane.
  - `theorem`/`lemma` (never computes): **bind as a Ψ-global**
    `u : Trm(· ⊢ Stmt @ l)`. Kernel has no δ-unfolding, so globals are
    opaque — which is the *right* semantics: modular per-theorem checking,
    proofs invisible to clients, referenced as neutrals (proofs are
    transported, never evaluated). VERIFY when implementing: the ch. 04
    layer side conditions for referencing a layer-v/c `Trm` global from
    layer-p/m proof terms (believed fine via v < c < p, but it is a book
    check, not an assumption).

## Emission invariants (inherited from decided issues)

- Output is **meta-layer β-normal; code composition via letbox**
  ([[box-synthesis-gap]], decided). `NotInferable` from the kernel is an
  elaborator-bug detector. The `${expr}` ANF-hoisting desugaring
  ([[surface-syntax]]) makes this hold by construction.
- Eliminators stay inferable, intros checkable — every sugar lowering
  preserves checking-descent ([[front-end-sugar]] constraints).
- Auditable lowering: each surface construct has a documented mechanical
  desugaring; load-bearing for [[inductive-compiler]] especially.

## Testing

Golden surface→core files; pretty-print/reparse round-trip; and the cheap
high-value property: **every elaborator test's output goes through the real
kernel check**, so soundness is enforced by construction. Acceptance gate =
[[stress-proof-suite]].

## Order of attack

1. Surface AST + name resolution (names → the three de Bruijn namespaces) +
   bidirectional annotation-synthesis, no metas, explicit levels — enough to
   push the Nat theorems through the kernel.
2. Metas-as-Ψ-globals unification + level inference; Nat suite loses its
   annotations.
3. [[inductive-compiler]] tier 0, then hand-prototyped List fording, then
   the tier-1 generator + no-confusion.
4. `Acc` by hand (tier 2), closing [[stress-proof-suite]].
5. Reopen [[ir-simulate-design]] in-language; IR is just another
   `inductive`, simulate just another `def`.

Standing earmark carried from [[kernel-v1-extensions]]: the ch. 07
pen-and-paper pass (Id-at-□, Σ-η, positive sums, W) should happen before
the frontend generates serious term volume on those formers.

## Log

- 2026-07-23: Opened after the frontend-first route discussion; captures
  the metas-as-globals architecture, level-unification story, definition
  split, emission invariants, and staged order of attack.
- 2026-07-23: Stage 1 LANDED. Layer check resolved first (the flagged assumption): ch. 04 global-term-variable rule (04 tex l. 1079) requires only i' <= i with the binding invariant i' in {v,c}; kernel already enforces it (typing.rs:674) — theorems-as-Trm_c-globals is sound, with one refinement: Ψ-bindings are declarations, so the flow is check-proof-then-bind (the binding justified by the checked inhabitant); layer-m proofs can't be Ψ-bound and will fall back to inlining (irrelevant in stage 1). Implementation: crates/syntax (AST/lexer/parser for the stage-1 subset: fn/theorem, Nat, ==, numerals, calls, match-on-Nat with explicit-ih arms + optional 'as z -> M' motive, refl, j) and crates/elab (name resolution into the three namespaces; bidirectional annotation-filling, no metas, all levels 0 but tracked honestly; defs inlined with global-index shifting; theorems pushed as Trm_c globals; kernel-as-oracle via whnf_type/apply_local/LocalSubst::id; kernel check_type+check_term gates every declaration). elab_check is structural only where the expected type is load-bearing (refl, motive-less match) — everything else infers and the kernel's premise-level conversion catches mismatches. Prelude: sym/trans/cong_succ monomorphic at Nat via j. Acceptance test passing: crates/elab/tests/nat_suite.rs. Next: stage 2 (metas-as-Ψ-globals + level inference) when annotation pain justifies it.
- 2026-07-27: Closing per README rule 3: every stage of the order of attack landed or has an owner — stage 1 here, stage 2 [[elab-stage2-metas]], stage 3 [[inductive-compiler]] (tier-2 remainder owned there), stage 4 closed [[stress-proof-suite]], stage 5 is [[ir-simulate-design]] (roadmap item 16). Residue homes: level-meta generalization → [[elab-unifier-completeness]]; ch. 07 earmark → [[metatheory-ch07-pass]] (closed); the def/theorem layer VERIFY was resolved in the stage-1 entry. Body remains the architecture design record.
