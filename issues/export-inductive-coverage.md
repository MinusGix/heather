---
title: Realise tier-2 inductives and level-polymorphic uses natively
status: open
labels: [translation,export,inductives]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-21
updated: 2026-10-21
---

Found by the whole-library sweep (design §7): two kinds of inductive the
native-inductive realisation (`crates/export/src/wf.rs`) does not cover yet.

- **Tier-2 inductives** (recursive function-typed fields, `ITree`'s `Vis`)
  lower to `W` plus a leaf predicate (PR #88), not to `Wf`, so their
  declarations are never registered and every use is refused as "a Wf
  instance the exporter has not met": 23 bindings of `itree_trace` and
  `itree_state`. Both targets have native inductives with function-typed
  recursive fields, so the realisation is the same idea over a different
  lowering: recognise the `W` + predicate pair by its tag and realise it
  as one native inductive.
- **A tier-1 inductive used at another level.** The native inductive is
  realised once, at its declaration's level, but Heather uses `List` at
  any level (`relation::AnyOf` takes `List<A → B → Type>`). The exporter
  refused nothing there until 2026-10-21, and Lean rejected the
  application; it now refuses the use. The fix is a realisation per level
  used (Lean's inductives can be universe-polymorphic, so one
  `List.{u}` would do; Rocq's too, with `Polymorphic Inductive`).
