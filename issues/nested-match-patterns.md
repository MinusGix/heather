---
title: Nested patterns and a default arm in match
status: open
labels: [frontend,syntax,elaboration]
created: 2026-07-31
updated: 2026-07-31
---

Two sugarings, one round, both straight from lib/ir_v1.hthr
([[ir-simulate-design]]):

1. **Deep patterns.** `step_letmatch` and `step_loopiter` are towers of
   single-level matches; what they mean is one decision tree:

       match lookup(env)(scrut) {
           NoneV => Stuck,
           SomeV(VCon(tag, fields)) => ...,
           SomeV(other) => Stuck,
       }

   Elaboration is the classic pattern-matrix compilation into the nested
   single-level matches written by hand today — elaborator-only, no
   kernel change, motives synthesized per level exactly as now. The
   interaction to watch: patterns on a RECURSIVE argument position must
   keep the self-call guard's view of the binder (the guard matches
   syntactically — [[guard-matches-self-calls-by-term]]), so v1 can
   simply reject deep patterns in the decreasing position.

2. **A default arm.** `pick_arm` in ir_v1 writes seven identical
   `... => NoArm` arms because every constructor must appear. A `_ =>`
   arm (no binders, appears last, expands to the missing constructors'
   arms with the body duplicated) removes the worst of it. Notable: the
   duplication is per-arm term copies, and [[simulate-conversion-cost]]
   says term size is billed at conversion — so expansion should reuse
   one shared body where the motive allows rather than eight copies.

Lean-style equation definitions (`| Ret(rs) => ...` at the fn head) are
the same machinery worn as declaration syntax; fine, but it is sugar on
sugar — record here, do not gate on it. The more radical end of that
thought is [[case-algebra-definitions]].
