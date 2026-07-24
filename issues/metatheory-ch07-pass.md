---
title: "Metatheory: ch. 07 pen-and-paper pass for the five extensions"
status: closed
labels: [kernel,delam,metatheory]
created: 2026-07-23
updated: 2026-07-24
---

The standing earmark from [[kernel-v1-extensions]], promoted to its own
issue so it can be picked up independently. Five extensions landed with
their logical-relations obligations *earmarked but never sketch-checked*;
the debt compounds and should be paid before [[inductive-compiler]] tier 1
starts generating serious term volume over these formers
([[frontend-roadmap]] slots it at position 2).

The pass (pen and paper, not Coq — a day, not a month): walk the recursor
cases of the ch. 07 Kripke logical relations for each extension's arms and
convince ourselves the fundamental theorem still goes through. Per-former
worry list, from the kernel-v1-extensions earmarks:

- **Id at □ types** (the original earmark): Id makes code conversion
  propositionally observable at `□(Δ ⊢ T)` while the recursor is
  intensional; the recursor cases of the LR are where it could bite.
  `tm_refl`/`tm_j` join the constructor/neutral cases.
- **Σ (negative/η)**: the LR at `□(Δ ⊢ Σ … @ l)` must be closed under
  surjective pairing (η is definitional); `fst`/`snd` are new neutral
  heads for the neutral cases.
- **Sums (positive/finitary)**: closure under the two injections and
  `case`'s reductions; its own line, not foldable under Σ.
- **W (positive/infinitary — heaviest)**: the `sup` case quantifies over
  all subtree functions in the layered/□ setting; the synthesized-ih β
  (`elim_W (sup a f) ⇝ s[a, f, λy. elim_W …]`) is the novel reduction
  shape the fundamental theorem's `elim_W` arm must absorb.
- **Funext leak audit** (grep-level, do alongside): confirm no rule
  anywhere derives □-level equality from term-level `Id` — funext must
  stay propositional-only, never a □-congruence
  (kernel-v1-extensions' "no unbox congruence, ever").

Output: a short note per former appended here (or a docs/ note if it
grows) + any kernel-rule consequence filed as its own issue. Nothing is
*expected* to break; the point is to know.

## Log

- 2026-07-23: Opened, promoting the kernel-v1-extensions earmark to a
  jumpable work item.
- 2026-07-24: Pass done; written up in docs/metatheory-ch07-extensions.md. Verdict: nothing breaks, no kernel-rule change. Per-former: Sum/Empty are Nat-shaped positives (Empty additionally gives ch. 08 consistency directly); Sigma must take the *negative* (projection) LR case to match conv.rs's type-directed eta, and its contravariant premise needs the iff-strengthened layering-restriction IH like Pi; Unit is the irrelevant case — escape depends on an eta law rather than on term structure; Id gets a refl/neutral NfEq with no K. W is the heaviest: NfEqW is an infinitary Kripke-quantified inductive definition (new shape here — Nat recurses finitarily, Pi's quantification lives in the type relation), and the elim_W arm works precisely because of the forall-psi premise: the synthesized 'lambda y. elim_W(f y)' is related at Pi by weak-head expansion onto the inner NfEqW IH. Id-at-box earmark resolved: refl synthesizes Id(S;t;t) so its endpoints go through conversion, and conversion at code types is syntactic '=='; therefore Id over box is inhabited exactly at syntactic code equality — the same equality the recursor observes, so the recursor arms are untouched. Promoted that to a DESIGN.md invariant. Funext leak audit: clean — every box-relating path is the '==' arm, letbox substitutes a global variable rather than unboxing, and conversion is never invoked at layer c at all. Also verified the code-recursor branch bundle is exhaustive over layer-c syntax (10 type + 27 term formers = the 37 branches), which the 07b recursor arms depend on. Two obligations recorded, not filed: the declarative (ch. 04) equivalence owes Sigma-eta (surjective pairing) and Unit-eta as actual rules — the only new *rules* the extension pass adds; without them escape from those two LR cases has nothing to land on.
- 2026-07-24: Follow-up filed: [[delam-extensions-writeup]] for the declarative ch. 04 rules (standalone doc, paper-shaped, Σ-η and Unit-η the non-mechanical parts).
