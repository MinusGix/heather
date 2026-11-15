---
title: A type parameter instantiated at a context-dependent type is mis-scoped
status: closed
labels: [elaboration,inductives,soundness]
created: 2026-07-26
updated: 2026-07-26
---



**A wrong-type bug, in the tier's own hazard class**, found 2026-07-26 while
auditing the shift arithmetic after [[wf-former]] phase 5. It is *not* new
with that round: it is tier 0's, reachable from the surface today, and it
fails **silently** — the emitted declaration typechecks and states something
the user did not write. `docs/inductives/inductive-tier0-lowering.md`'s opening names
exactly this: "a bug here does not produce a rejected term, it produces a
*checked proof about a type the user did not mean*. The kernel cannot catch
that."

## The witness

```
inductive Box2<A> { Mk(x: Nat, y: A) }
fn mk(n: Nat) -> Box2<n = n> { Mk(3, refl) }     // accepted today
```

Reading the goal at the second field (`Mk(3, ?p)`) shows its type is

```
?p : Id[0](Nat; S(S(S(0))); S(S(S(0))))          // 3 = 3
```

The user wrote `Box2<n = n>`; the encoding says `x = x`, instantiated at this
constructor's own first field. `Mk(3, refl)` is then accepted, and `mk` is a
checked function into a type nobody asked for.

The one-field version fails *loudly* instead, which is why this was not
noticed earlier:

```
inductive Box<A> { Mk(A) }
fn mk(n: Nat) -> Box<n = n> { Mk(?p) }
?p : Id[0](Nat; ⟨⟩0; ⟨⟩0)                        // the nominal TAG's ⟨⟩
```

`⟨⟩ : Unit` is not a `Nat`, so the kernel rejects. Whether you get a
rejection or a wrong theorem depends only on **what the preceding field's
type happens to be** — a `Nat` field before the parameter field makes the
collision type-correct, and the bug goes quiet.

## Cause

`crates/elab/src/inductive.rs`:

- `lower_ctor` builds `fcx` with `fcx.tyvars` set from `args`, which are
  lowered in the *ambient* `Γ`, and then **pushes binders**: the nominal tag
  first (§3.3), then one per payload field, so that a named field is in scope
  in the types after it.
- `lower_named`'s type-parameter path returns the stored type **unshifted**:

  ```rust
  if let Some((_, ty, lvl)) = cx.tyvars.iter().rev().find(|(n, _, _)| n == name) {
      return Ok((ty.clone(), lvl.clone()));      // <- no weakening
  }
  ```

So a parameter used in field `j` is under-shifted by `1 + j`, and its free
variables silently re-point at the tag and the earlier fields.

`Cx` already has the right pattern one field over: an `Alias` records the
`depth` it was bound at and every use is shifted by `names.len() - depth`
(`lib.rs`, `Elaborator::resolve`). `tyvars` wants the same treatment — a
depth alongside the type, and a shift at the lookup — which is the fix, but
it should be written as the *rule* (§2's "field types see the type
parameters and the earlier named fields") rather than as a patch.

## Why it survived, and the class it belongs to

The same shape as the `Vec^l(T;0)` defect of [[unit-level-and-vec-preservation]]:
**the witness was never rare, the observer was missing.** Every lowered
declaration in the suite instantiates its parameters at *closed* types
(`Nat`, another monomorphic declaration), so every shift in the lowering is a
no-op and nothing distinguishes a correct one from a missing one. The
surface's type grammar has exactly one context-dependent form — `=`, whose
endpoints are terms — and no test used it in a type-argument position.

The class is wider than this bug, and fixing this bug is what creates its
observer:

- **Tier 0**: `lower_ctor`'s field spine, `build_fields`' `apply_local`, and
  `projection`'s walk all assume the parameter types are scoped correctly.
- **Tier 1** ([[wf-former]] phase 5): `⟦D⟧` is closed for every monomorphic
  declaration, so `d_ty.shift_local(d_body)` in `wf.rs`, the `snd_ty` shift in
  `build_children`, and the spine shifts in `inject` are *all* no-ops in all
  13 of `inductive_tier1.rs`'s tests. They are written to be correct and are
  currently unobserved. A `Tree<n = n>` — once the fix makes it lowerable —
  exercises every one of them at once.

## What to do

1. Give `Cx::tyvars` a binding depth and weaken at the lookup site, matching
   `Alias`. State it in `docs/inductives/inductive-tier0-lowering.md` §3.1 as part of
   the rule, since the document currently says "no shifting is needed", which
   is true of the *entries* and false of the *parameters*.
2. Regression, at both failure modes: the silent one (`Box2<n = n>` must
   reject `Mk(3, q)` for `q : 3 = 3`, and accept a proof of `n = n`) and the
   loud one (`Box<n = n>` must lower at all).
3. Then the tier-1 observer the fix unlocks: declare `Tree<A>` with a
   recursive constructor, instantiate at `n = n`, and run the
   `inductive_tier1.rs` acceptance over it — `mirror(mirror(t)) = t` at a
   context-dependent parameter puts a free local inside `⟦D⟧` and makes every
   shift in `wf.rs` load-bearing.
4. Consider whether the generators should reach here at all. There is no
   property test over *surface* declarations; this was found by hand. A
   generator that instantiates parameters at `=` types is the systematic
   version of step 2.

## Log

- 2026-07-26: FIXED. `Cx::tyvars` now carries a binding depth and `lower_named` weakens by `names.len() - depth`, the same device `Alias` already used; `lower_ctor` records the depth as the ambient context, which is where the instantiation was lowered. One-line rule, and it is now stated as part of docs/inductives/inductive-tier0-lowering.md §3.1 rather than left implicit — the section previously said 'no shifting is needed', which is true of the field ENTRIES and false of the PARAMETERS. Three tests, each verified to fail against the pre-fix elaborator: (1) tier 0 a_parameter_at_a_dependent_type_keeps_its_scope — the loud face, where the collision is with the nominal tag's Unit and the kernel rejects; (2) tier 0 a_parameter_at_a_dependent_type_is_not_captured_by_an_earlier_field — the SILENT face, where a Nat field before the parameter makes the collision type-correct, so the encoding stays well-formed and quietly means `x = x`; it is pinned by rejecting a proof of `3 = 3` where `n = n` was written, and by projecting the field back out. (3) tier 1 the_lowering_shifts_are_exercised_by_a_dependent_parameter — the observer for the wider class, per this issue's step 3: `Tree<A> { Leaf(A), Node(A, Tree<A>, Tree<A>) }` instantiated at `n = n`, run through the full mirror(mirror t) = t acceptance. That puts a free local inside the Wf and makes wf.rs's d_ty shifts, build_children's snd_ty shift and inject's spine shifts all load-bearing at once; it too fails pre-fix. Two incidental findings while writing (3), neither a defect: a constructor inside an `=` type is in INFERENCE position, so a parametric declaration needs a field whose type is the bare parameter for infer_ctor to recover it (Node(A, Tree<A>, Tree<A>) does, Node(Tree<A>, Tree<A>) does not); and a theorem parameter mentioning another parameter must follow it, since the telescope is elaborated in order. Step 4 of this issue — a generator over SURFACE declarations that instantiates parameters at `=` types, the systematic version of these tests — is NOT done and is split out as [[surface-declaration-generator]], with the sharpest oracle named there (instantiation commutes with lowering, which is precisely what this bug violated). Suite 344 -> 347.
