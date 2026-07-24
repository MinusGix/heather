---
title: Elaborator unifier: postponement, general pattern inversion, level inference
status: open
labels: [frontend,elaboration]
created: 2026-07-24
updated: 2026-07-24
---

Follow-ups deferred from [[elab-stage2-metas]] (stage 2 shipped a deliberately minimal, best-effort unifier — acceptance was the level-0 Nat suite). None of these are correctness holes: the kernel re-checks every zonked term, so today's gaps surface as elaboration *errors* or kernel *rejections*, never unsoundness. Pick up when a program actually needs them.

## Deferred pieces

- **Constraint postponement.** The unifier (crates/elab/src/lib.rs `unify_ty`/`unify_tm`) never blocks: it solves what it can in one structural pass and moves on. A meta that needs a *later* argument to be solved first is simply left unsolved -> `could not infer an implicit argument` error. Real pattern unification keeps a constraint queue and re-tries on progress. Needed once implicit args depend on each other out of left-to-right order.

- **General pattern (Miller) inversion.** Meta solve assumes the delayed substitution delta is the identity on Gamma (true for every meta stage 2 generates, since occurrences are `?m^{id_G}` at the point of use). The solution is taken as the subject verbatim (`sols[i] = subject`). A non-identity variable renaming would need `subject.apply_local(delta^{-1})` (invert the renaming, a kernel `apply_local`); a non-pattern delta (non-var terms) should postpone/fail. The `is_pattern` guard already detects the non-var case and declines; add the inversion for the permuted-renaming case.

- **Level-meta inference.** Stage 2 does no level unification (every Nat-suite level is 0). This is *correctly* sequenced late, not merely skipped: non-cumulativity means no <= constraints exist, and universe polymorphism is layer-m only, so level inference is unification over count/adjust normal forms (Level::normalize is the oracle) that only bites once layer-m / modal programs appear. See [[elaborator-design]] (level-metas-as-L-vars) and [[frontend-roadmap]].

## Trigger

Whichever comes first: (a) a surface program whose implicit args cross-depend or use a non-identity scope, or (b) the layer-m / universe-polymorphic work where level metas become load-bearing. Until then the best-effort unifier is sufficient and kernel-gated.
