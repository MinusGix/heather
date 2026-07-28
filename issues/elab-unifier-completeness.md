---
title: Elaborator unifier: postponement, general pattern inversion, level inference
status: open
labels: [frontend,elaboration]
created: 2026-07-24
updated: 2026-07-27
---

Follow-ups deferred from [[elab-stage2-metas]] (stage 2 shipped a deliberately minimal, best-effort unifier — acceptance was the level-0 Nat suite). None of these are correctness holes: the kernel re-checks every zonked term, so today's gaps surface as elaboration *errors* or kernel *rejections*, never unsoundness. Pick up when a program actually needs them.

## Deferred pieces

- **Constraint postponement.** The unifier (crates/elab/src/lib.rs `unify_ty`/`unify_tm`) never blocks: it solves what it can in one structural pass and moves on. A meta that needs a *later* argument to be solved first is simply left unsolved -> `could not infer an implicit argument` error. Real pattern unification keeps a constraint queue and re-tries on progress. Needed once implicit args depend on each other out of left-to-right order.

- **General pattern (Miller) inversion.** Meta solve assumes the delayed substitution delta is the identity on Gamma (true for every meta stage 2 generates, since occurrences are `?m^{id_G}` at the point of use). The solution is taken as the subject verbatim (`sols[i] = subject`). A non-identity variable renaming would need `subject.apply_local(delta^{-1})` (invert the renaming, a kernel `apply_local`); a non-pattern delta (non-var terms) should postpone/fail. The `is_pattern` guard already detects the non-var case and declines; add the inversion for the permuted-renaming case.

- **Level-meta inference.** Stage 2 does no level unification (every Nat-suite level is 0). This is *correctly* sequenced late, not merely skipped: non-cumulativity means no <= constraints exist, and universe polymorphism is layer-m only, so level inference is unification over count/adjust normal forms (Level::normalize is the oracle) that only bites once layer-m / modal programs appear. See [[elaborator-design]] (level-metas-as-L-vars) and [[frontend-roadmap]].

## Trigger

Whichever comes first: (a) a surface program whose implicit args cross-depend or use a non-identity scope, or (b) the layer-m / universe-polymorphic work where level metas become load-bearing. Until then the best-effort unifier is sufficient and kernel-gated.

## Log

- 2026-07-24: Second motivation for postponement, from [[goal-holes]]: holes are checking-only, and `apply_implicit` elaborates a callee's *explicit* arguments in inference mode (it needs their inferred types to drive unification). So `sym(?p)` is refused today and the user must write `@sym(a, b, ?p)` — a visible ergonomic dent on the most natural spelling. Postponement fixes it directly: with the argument's elaboration deferred until the domain's metas are solved, the hole gets a meta-free expected type and becomes an ordinary goal. A cheaper partial fix exists if postponement stays out of reach — check the hole against the parameter domain whenever that domain contains no meta occurrence — but it needs an occurs-style traversal over kernel Type/Term that the elaborator does not have and should probably not grow on its own.
- 2026-07-26: surface-polymorphism grew unify_ty from Id-congruence-only to full structural congruence over the formers the lowerings build, with binder-depth tracking, a strengthening test on candidate solutions, and the El rule (El ?A vs T solves ?A := code_of T). Contract unchanged: it never fails, it only learns. The concrete limit it leaves is an implicit FUNCTION parameter -- 'theorem cong_at<A, B>({f: A -> B}, {a: A}, {b: A}, p: a = b): f(a) = f(b)' declares and kernel-checks, but cong_at(p) cannot solve f, since p's type mentions a and b and not f. That is higher-order pattern unification and is this issue's, not that round's.
- 2026-07-27: The cong-with-implicit-f item recorded in the 2026-07-26 log is MISFILED and moves to [[congruence-by-anti-unification]]. That log called it 'higher-order pattern unification and is this issue's'; it is neither. '?f a =? X' is flex-rigid with 'a' an arbitrary TERM rather than a distinct bound variable, so it is outside the Miller fragment by construction and genuinely ambiguous ('?f 0 =? Succ(0)' is solved by both 'lambda z. Succ(z)' and the constant 'lambda z. Succ(0)') -- finishing this issue's pattern-inversion bullet does not approach it. The stated reason was also beside the point: nobody expected the PROOF to carry f, and in checking position the information is in the EXPECTED TYPE, recovered by anti-unification (least general generalization) rather than unification. This issue keeps postponement, general pattern inversion and level-meta inference, all of which remain correctly scoped.
