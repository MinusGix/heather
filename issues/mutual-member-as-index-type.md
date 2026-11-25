---
title: A mutual group member as an index type is refused with a generic message
status: open
labels: [elaboration,inductives,diagnostics]
area: language
milestone: [none]
created: 2026-11-25
updated: 2026-11-25
---

Found by [[reflected-languages-typed-by-construction]] (2026-11-25). A member of a mutual group cannot be an index type, and the refusal does not say so:

```heather
inductive Shape { SWord, SSeq(a: Shape), SRec(fs: Shapes) }
inductive Shapes { SNil, SCons(h: Shape, t: Shapes) }

fn decode(c: Shape) → Nat { 0 }   // ends the run

inductive Mem(t: Shape) : (fs: Shapes) → Type {
    MHere(r: Shapes) : Mem(t)(SCons(t, r)),
    MThere(h: Shape, r: Shapes, m: Mem(t)(r)) : Mem(t)(SCons(h, r)),
}
```

is refused with "`Shapes` cannot be used here": `Inductives::index_type` (`crates/elab/src/inductive.rs`) looks the name up with `lookup_inductive`, which does not find a group member (it has no declaration of its own, `lookup_member` in `crates/elab/src/lib.rs`), and `name_miss` falls through to the generic message. Pinned in `lib/_tests/lang/ownership/typed_steps_tests.hthr` (`Mem`).

Two levels of fix:

1. **The message**: name the reason (a member of a mutual group is not an index type this round) and the design note that would own it.
2. **The lift**: an index type is consumed by recursion on it (route 1's family by large elimination, or the `IWf` route at an open index); a group member's eliminator is the group's one `elim_IWf` at the member's index (`docs/inductives/mutual-inductive-design.md` §6). Whether a family can be built by recursion on one member, or must go through the `IWf` route with the member as an open index type, is the design question.

A code universe whose records hold a list of shapes needs this for a typed field position (`Mem`) and falls back to a `Nat` position with a computed target (`Shapes::at`) without it.
