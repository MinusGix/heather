---
title: Infer cong's function by anti-unification, in a goal-solver metaprogram
status: open
labels: [frontend,elaboration,metaprogramming,design]
created: 2026-07-27
updated: 2026-08-05
---

A general `cong` cannot have its function argument implicit today, so the
prelude ships the Nat-specific `cong_succ` and a general `cong` must be written
`cong(λ (x: Nat) => Succ(x), p)`.

This issue is the route to inferring it — and, first, a **correction to why it
is not inferred**, because the recorded reason has sent the work to the wrong
place.

## 1. The recorded reason is beside the point

Three places say the same thing:

- `crates/elab/src/prelude.hthr` — "an implicit one is not inferable from the
  proof … the proof's type mentions the endpoints and not the function".
- [[at-and-type-arguments]] — "`cong` cannot generalize with `f` implicit".
- [[elab-unifier-completeness]]'s 2026-07-26 log — "`cong_at(p)` cannot solve
  `f`, since `p`'s type mentions `a` and `b` and not `f`. That is higher-order
  pattern unification and is this issue's".

All true, and all beside the point: nobody expects the *proof* to carry `f`. In
a **checking** position the information is in the **expected type**. From
`X = Y` together with `p : a = b`, `f` is exactly what generalizes `X` and `Y`
at the positions where `a` and `b` differ.

## 2. It is not unification, so the unifier cannot grow into it

`?f a ≟ X` is flex-rigid with `a` an **arbitrary term**, not a distinct bound
variable, so it is outside the Miller pattern fragment by construction — and
genuinely ambiguous: `?f 0 ≟ Succ(0)` is solved by `λz. Succ(z)` *and* by the
constant `λz. Succ(0)`.

So this is **misfiled**. It currently sits under
[[elab-unifier-completeness]]'s "general pattern (Miller) inversion" bullet,
and finishing that bullet — inverting a permuted renaming — does not approach
it. That issue should keep postponement, inversion and level inference, and
drop this.

## 3. The algorithm: anti-unification (least general generalization)

Not unification, its dual. Given the expected `X = Y` and `p : a = b`:

1. Compute `LGG(X, Y)` — the least general generalization, a first-order term
   with holes at the positions where `X` and `Y` differ.
2. Require **every** hole's witness pair to be exactly `(a, b)`.
3. Abstract them: `f := λ z => LGG[holes ↦ z]`.

```
X = Succ(0), Y = Succ(1),  p : 0 = 1
LGG = Succ(□),  □ ↦ (0, 1)   ⟹   f := λ z => Succ(z)
```

Linear, first-order, and terminating.

## 4. Why this is safe under [[elaboration-determinism]]

The property that matters: **the LGG is unique.** It does not *choose* among
candidate solutions — it computes the most specific one — and a hole whose
witness pair is not `(a, b)` is a loud failure rather than a fallback.

That is the difference between "tactic-like" as a hazard and as a technique. A
heuristic that picked among the infinitely many solutions of the flex-rigid
problem would threaten the determinism guarantee; anti-unification can be
*specified and tested*, which is the bar this project holds elaboration to.

## 5. Where it lives: a metaprogram, not an elaborator case

**Not** a special case for `cong` in the elaborator. That is exactly the
"special feature in the elaborator" that round two exists to remove
([[frontend-roadmap]]), and it would not even be one case, because the same
solver is what `subst` and `rewrite` want.

It belongs in a **goal-solver metaprogram at layer m** — what `□` is for, and
what the roadmap already gestures at with "goal-solver meta-functions". Wants
[[generators-in-the-language]] and the modal surface.

The division of labour, which is the point:

> `cong` stays an ordinary function with an explicit `f`. The tactic
> *constructs the application*. They are not alternatives — the tactic's output
> is a call to the innocent function, which is what leaves the kernel's job
> completely unchanged.

## 6. Why it is bigger than `cong`, and why that argues for the same home

- LGG abstracts **all** differing positions. From `p : a = b`, the goal
  `add(a, a) = add(b, b)` yields `λz. add(z, z)` — correct, but a *different*
  theorem from congruence in one argument.
- When only *some* occurrences should be abstracted (rewrite at the third
  occurrence), LGG cannot express it at all. Occurrence selection is a real
  `rewrite` feature.

Both say the same thing: the general shape is a rewriting tactic, of which
congruence inference is one instance. Patching `cong` would buy the instance
and none of the shape.

## 7. Sequencing

Not next. It wants the modal/layer-m surface and
[[generators-in-the-language]], neither of which is scheduled. Until then the
explicit spelling works and `cong_succ` covers the Nat suite.

Cheap interim option, if it is ever wanted before the tactic layer: implement
the LGG in the elaborator behind the *existing* explicit-`f` declaration, as a
solver for one named implicit. It buys the ergonomics at the cost of the thing
this issue argues against, so it should be taken only with that trade named
out loud.

Related: [[surface-proof-automation]] (auto-refl and `apply` — the same
"lightweight automation" line), [[nested-goal-discharge]].

## Interim round design (2026-08-05)

The interim option is being taken, with the trade named: this is a special
elaborator behavior of the kind round two exists to remove. Two things make
it cheaper than §7 feared, discovered by reading the code rather than the
issue:

- **The throwaway part is thin.** The LGG algorithm is home-independent; it
  lands as its own module with its own spec and tests, and the eventual
  layer-m tactic wraps or reimplements it against the same suite. Only the
  elaborator hook is discarded.
- **It joins an existing family.** `refl`, `absurd`, `FZ`/`FS` and numerals
  already consult the expected type in checking position, all tracked for
  demotion under [[special-forms-as-declarations]]. This is one more
  resident of a house scheduled for renovation, not a new category.

Decisions:

1. **Trigger: structural, not name-keyed.** No string-matching `cong`. The
   rule fires when an implicit-inserting call in *checking* position would
   otherwise fail with "could not infer", its zonked result type is `Id`
   with both endpoints the **same unsolved meta applied to one argument**
   (`?f(s) = ?f(t)`, `s`/`t` meta-free), and the expected type whnf's to an
   `Id`. Then `f := λz. LGG(X, Y)` with every hole's witness pair required
   to be exactly `(s, t)`. Nothing else can fire it, and any declaration of
   that shape benefits, not only `cong`.
2. **"Exactly `(s, t)`" is syntactic α-equality** — structural `==` on
   de Bruijn kernel terms. No conversion call: keeps the solver linear and
   terminating as advertised, keeps failure loud, and keeps an unbounded
   conversion out of every `cong` elaboration (the known memory-superlinear
   hazard). A defeq-tolerant version would be a later, deliberate loosening.
3. **Under binders: shift or fail.** A hole under `k` binders matches only
   if the differing subterms are `s`/`t` shifted by `k`; the abstracted `z`
   lands at the right index. No capture, no cleverness — a witness that
   cannot be strengthened out is a loud failure.
4. **Metas in the expected type: a non-question.** In checking position the
   expected type is committed-world and meta-free by construction (the
   `zonked` guard in `apply_implicit` already ensures checking mode only
   runs against fully-solved domains). No postponement policy needed.
5. **Zero holes is fine** (`X ≡ Y` gives the constant function); a
   difference whose witness is not `(s, t)` names the mismatching position
   in the error. `s ≡ t` with `X ≢ Y` fails by the same check.
6. The prelude gains the general
   `theorem cong<A, B>({f: A -> B}, {a: A}, {b: A}, p: a = b): f(a) = f(b)`;
   `cong_succ` stays (it is a different lemma by name and the Nat suite's).
7. Plumbing: thread the expected type from `elab_check_hinted`'s fallback
   (`crates/elab/src/lib.rs` ~1786, where it is currently discarded) into
   the application path, so `apply_implicit` (~4301) can first harvest
   first-order solutions by unifying expected against the zonked result
   type (this is what solves `B`), then attempt the LGG rule for the
   remaining `?f`-shaped meta before failing.
8. Tests along `docs/testing-generated-terms.md`: neutral endpoints, an
   open element type, checking-only trigger (inference position must still
   fail with the existing message), and negative controls (witness not
   `(s, t)`; capture under a binder; expected not an `Id`).

## Log

- 2026-08-05 (later): Interim round **landed**. `crates/elab/src/lgg.rs`
  (the surviving half) + the `solve_by_lgg` hook in `apply_implicit` (the
  throwaway half, marked as such in its doc comment); general `cong` in the
  prelude; 16 integration + 11 unit tests, suite green at 1035. Two
  implementation findings recorded in the code: the first-order harvest must
  run *after* the trigger and with `?f` withheld (`unify_ty`'s App-congruence
  otherwise "solves" `?f(s) ≟ add(a,a)` by peeling an argument), and the
  witness pair is tested outermost-first (so `p : Succ(0) = Succ(1)` against
  the identical goal answers `λz. z`, which the textbook inside-out LGG
  would refuse). Issue stays open for the real home: the layer-m goal
  solver, occurrence selection, and `rewrite`.
- 2026-08-05: Interim option taken, trade named (see design section above).
  §7's "not next" was about the tactic-layer home, which is still not
  scheduled; what changed is the assessment of the interim slice's cost —
  the LGG module survives the migration, only the hook is throwaway, and
  the hook joins the existing checking-position special-form family rather
  than founding a new one. Trigger made structural (`?f(s) = ?f(t)` against
  an expected `Id`) rather than keyed to `cong`'s name.
- 2026-07-27: Filed out of a question about the prelude's `cong_succ` — whether
  `cong` should be able to infer its function. It should, and the reason it
  does not is not the one recorded: the information was never expected to be in
  the proof, it is in the expected type, and recovering it is anti-unification
  rather than unification. That reclassification is the substance here — it
  moves the work off [[elab-unifier-completeness]], where finishing the filed
  bullets could never have reached it, and onto the tactic layer, where the
  same solver also serves `subst` and `rewrite`.
