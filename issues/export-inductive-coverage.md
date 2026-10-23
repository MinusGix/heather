---
title: Realise tier-2 inductives and level-polymorphic uses natively
status: closed
labels: [translation,export,inductives]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-21
updated: 2026-10-23
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

## Log

- 2026-10-23: Closed. Of the two kinds this issue named, one was
  misdiagnosed:

  - **The "tier-2" refusals were a value parameter.** Every refusal in
    `itree_trace` and `itree_state` came from `Trace<R>(E: Events)`, a
    *tier-1* inductive whose parameter `E` is a value. `register_wf` took
    only `Ty l` binders, so the declaration was never registered. Tier-2
    `ITree` itself needs nothing: it lowers to `W` and its leaf predicate,
    both ordinary formers, and has exported through the prelude's `W` all
    along. Native inductives now take value parameters, read off an instance
    where the declaration's spelling has the variable, as spelled before
    evaluation (evaluation takes `E.Cmd` apart at a closed `E`).
  - **Another level profile is its own native inductive.** A use at a
    profile other than the registered all-`Ty 0` one (`List<A → B → Type>`)
    names `list::List::at#1`, lowered by the elaborator at that profile
    (`Elaborator::tycode_fn_at`), declared with its `supf#` before the
    binding that first needs it. One copy per profile used, not one
    level-polymorphic inductive: the library is level-monomorphic, and the
    copies work the same in Rocq.
  - **Found on the way:** a recursive declaration with no code binding
    (in `tactic`, 70 refusals that the 2026-10-22 sweep predates) is
    realised from the elaborator's lowering the same way, named as the
    declaration.

  Design §5.1 records the rules; `crates/export/tests/nat_fragment.rs`
  exports both new kinds and Lean's kernel accepts them. A refused
  binding's realisations and eliminators are now forgotten with it, so a
  later binding declares them again rather than naming an unprinted one.

  What is left is not inductive coverage: codata's `M`
  ([[export-codata-m]]), and `itree_state::ITree::returned_of_trace`, which
  now exports and is the one Lean rejection in `itree_*`, the eta-long gap
  of [[export-typed-translation]] at a Σ with an `sEq` component.
