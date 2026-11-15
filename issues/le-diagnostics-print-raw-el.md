---
title: A diagnostic about `Le` at open arguments prints the raw `El` code
status: closed
labels: [frontend,diagnostics,ergonomics]
created: 2026-08-17
updated: 2026-08-17
---

Found while probing negative controls for [[nat-arithmetic-kit]] (2026-08-17).
Supplying `trivial` where a comparison is wanted says:

```
error: `trivial` proves `True`, but
`El[0](app(app(u55^{·^2}; [0,(0 ⊔ 1)] Nat → Π[0,1](Nat). Ty 0; x1); [0,1] Nat → Ty 0; x0))`
is expected here
  --> probe.hthr:4:68
  |
4 | theorem t(n, m: Nat): add(sub(m)(n), n) = m { sub_add_cancel(n, m, trivial) }
```

The type it means is `Le(n, m)`.

This is **not** the bug [[goal-display-decodes]] fixed, and the difference is
the interesting part. That round gave the display sites a bounded reader that
δ-steps a wrapped type and prints the first non-`El` head. It works whenever a
head exists. Here none does: `Le` is a `fn … -> Type`, so at *open* arguments
`El(Le(n)(m))` is stuck as an `El` — irreducibly, not for want of budget — and
the reader correctly gives up and falls back to `{ty:?}`. The fallback is the
right behaviour for a type nothing can say anything about; it is the wrong
behaviour for one whose code is a readable application of a named global.

So the missing capability is the other direction: **print the code back as
surface** (`Le(n, m)`, `app` spine → call syntax, `xN` → the binder's name from
`Γ`) rather than only unfolding until the wrapper disappears. `unspell_ty_deep`
and the respelling machinery already know the code↔type correspondence.

## Why it matters more now than when the reader landed

Every propositional relation the library states is a `fn … -> Type`
(`docs/library/nat-order-design.md` §1 chose that over `= True` deliberately, and §6
notes this as the residue). So the *entire* order and everything built on it —
`Le`, `Lt`, `Mem`, `Sorted` — hits the fallback in any diagnostic at open
arguments, which is exactly the position a proof under construction is in. The
class of affected messages is small and fixed (the `trivial` mismatch, the
non-function lambda, goal statements), but the workload that reaches them is
now the normal one.

## What it assumes from elsewhere

- **[[goal-display-decodes]]** (closed) owns the display reader. Assumed here:
  only that display-decode is bounded, display-only, and falls back to the raw
  `Debug` form — which is the behaviour seen above.

## Acceptance

A `trivial`-mismatch or goal-statement diagnostic whose expected type is
`Le(n, m)` at open `n`, `m` prints something a reader recognizes as that type.
Bounded and display-only, like its predecessor; a code that does *not* respell
(a raw `app` of a meta, say) still falls back rather than guessing.

## Log

- 2026-08-17: Second customer, a different display site (issues/std-list-api.md, 2026-08-17). The L1 wave's `len_append` left an unfilled goal — its `Nil` arm was `{}` where the goal is `len(ys) = add(0, len(ys))`, which is stuck rather than refl — and the GOAL LISTING printed the statement as raw kernel encoding: `?g1 : Id[0](Nat; app(app(u1^{·^9}; …)))`, with each context binder shown as its `Wf[0](Σ…)` lowering. Several hundred columns of it, for a statement the reader wrote as one line. The span was correct and pointed at the `{}`, so the fix needed here is only this issue's — respell the code as surface — but the trigger is worth recording: it is not the `trivial` mismatch, it is the ordinary unfilled-goal report, which is the message a proof under construction sees most often.
- 2026-08-17: Third customer (waves L2'/L3, 2026-08-17). One real mistake in the round — zip_map_snd's Nil arm, where take(ys, 0) is stuck until its list is split — reported as an unsolved goal printed as several hundred columns of Wf/Sigma/El encoding, with the two list binders' types printed the same way. The statement it could not display is `Nil = take(ys, 0)`. Cost here was minutes rather than hours only because the failure was predicted before the run; the datum for this issue is that the round's ONLY genuine mistake was also the one place the message would have had to be read.
- 2026-08-17: LANDED, design in docs/elaborator/surface-type-display-design.md. A new module (crates/elab/src/display.rs) spells a kernel Type/Term back as surface, and display_type became three stages: the [[goal-display-decodes]] reader unchanged, then the speller on whatever the reader left, then the raw bounded Debug. The reader keeps precedence deliberately (where a head exists it is the better answer: N(v) still prints Nat), and the speller now also runs for types that were never El-headed, which is what fixes the Id statement the reader declined in its first line. WHAT SPELLS: Nat/True/False/Type<l>; Id as a = b; Pi as A -> B or (x: A) -> B by a strengthen_ty dependence check; Vec as [t; n]; Fin; an inductive lowering as its declaration's name via tag_of; El(code) as the code's spelling; numerals as decimals; Var as the binder's name from Γ; an App spine as a call with the head's IMPLICIT arguments dropped, so len<A>(xs) prints len(xs); Lam, Refl, Triv, Pair; the type-code formers by delegating to the type they encode; and constructor values by walking the injection path (the canonical half of read_ctor, re-derived rather than called, since that method can elaborate projections and fail). MEASURED EFFECT: the filed trivial-mismatch prints 'Le(n, m)'. The log's second customer -- len_append's unfilled goals -- went from ~2400 characters per goal (statement plus three Wf(Σ…) context binders) to 'len(append(Nil, ys)) = add(len(Nil), len(ys))' with 'xs : List<…>'. BOUNDS: no δ, no β, no whnf, no fuel -- the one registry consultation is unspell_here, a lookup; per-node fallback to the bounded Debug truncated to 96 columns; node/depth budgets; and above 4 fallbacks the whole attempt is abandoned for the honest raw form, because a half-spelled monster looks like surface syntax while being neither. A second entry point, spell_type_clean, admits no raw node at all -- for a caller that CLAIMS something about a type rather than displaying one (see [[check-fallback-discards-expected-type]]). TWO THINGS FOUND: (a) a Π dependence check that substitutes into the codomain must use a Wk tail under a context-variable base -- an Empty tail there is a kernel invariant violation the kernel reports by PANICKING, which a display path must never do (caught by the fast suite, twice, before this was gated); (b) the type ARGUMENTS of an inductive instance are not recoverable from its lowering, which monomorphizes -- so a parameterized instance prints 'List<…>' with a literal ellipsis, re-homed as [[display-inductive-type-arguments]] with both candidate fixes costed. Tests: crates/elab/tests/display_surface.rs (6, all pinning rendered text; the open-argument and parameterized-inductive axes of docs/testing-generated-terms.md) plus two negative controls inline in display.rs -- a type with no surface form is refused rather than guessed, and more refusals than the budget abandons the spelling. Those two are inline because the surface language makes an unspellable type hard to WRITE, which is itself evidence the coverage is not thin. Four existing pins moved, each because its message improved: two goal-holes statements now read as equations, the reader-exhaustion control now prints T40(v) (the design states this consequence), and nat_arith's refuted comparison now says False instead of Empty.
- 2026-08-17: Third customer, and this round it was diagnostic rather than cosmetic: the Int round (2026-08-17) found [[nested-match-on-field-binder-motive]] by putting a goal hole in a match arm, and the raw El dump was the ONLY evidence that the arm goal had not specialized -- the giveaway was the scrutinee still appearing as a variable in a Zero arm. So the display cost time and then saved it, which is an argument for the fix rather than against: what the reader needed was 'isucc(ipred(n)) = n with n free', and what printed was several hundred columns of Sigma/inl encoding in which that fact is present but has to be decoded by hand.
