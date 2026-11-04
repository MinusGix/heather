---
title: A deep pattern on an indexed family's recursive field: the elaborator accepts, the kernel refuses
status: closed
labels: [elaboration,match,patterns,defect]
area: language
created: 2026-11-01
updated: 2026-11-01
---

Found while doing slice 5 of [[dependent-match-compiler]] (2026-11-01). A deep pattern on an indexed family's recursive field is accepted by the elaborator and rejected by the kernel:

```heather
import nat;
inductive V : (n: Nat) -> Type { VNil: V(0), VCons(n: Nat, x: Nat, xs: V(n)): V(Succ(n)) }
theorem vv(P: (m: Nat) -> V(m) -> Type): (m: Nat) -> (v: V(m)) -> P(m, v) -> Nat {
    λ m => λ v => λ p => match v {
        VCons(k, x, VCons(j, y, ys)) => { let q: P(Succ(Succ(j)), VCons(Succ(j), x, VCons(j, y, ys))) = p; y },
        _ => 1
    }
}
```

The kernel says "the kernel rejected `vv`: NotConvertible ... the kernel refused `#payload`, which has type `V` where a type that displays the same is expected".

The inner generated match is on a field of the arm's value local. Its synthesized motive takes the tier-0 `field_rewrap` route. That route abstracts the value but leaves the index (`S(j)` in the goal `P(S(j), v')`) un-generalized. An indexed scrutinee needs a motive over the index and the value together, which the plain-family child rewrap (design §7.1) does not cover. Expect the fix to generalize the index alongside the value, as the convoy on indexed families does (§9.1). The same applies to IWf families.

## Done when
- The repro checks with no written motive, and a negative control (a wrong index in the annotation) is refused by the elaborator, not the kernel.

## Log

- 2026-11-01: Fixed (design §7.1, indexed paragraph). The cause was not a missing index generalization: generalize_index already generalized the field's index variable, but it also rewrote the outer value's projection annotations, so fst x claimed a type at the new index. When the route generalizes an index, the rebuild uses the unannotated pair@/fst@/snd@ spelling with only the root annotated. Tests: nested_match_patterns.rs (deep pattern, hand-written nested match, a wrong goal refused at the annotation). Remaining display gap: the rebuilt value has no surface spelling, so a wrong annotation's refusal is located but reported as the kernel's. The IWf route has no such refusal, because the stored index needs match h:.
