---
title: Infer cong's function by anti-unification, in a goal-solver metaprogram
status: open
labels: [frontend,elaboration,metaprogramming,design]
created: 2026-07-27
updated: 2026-08-18
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

That option was taken (2026-08-05) and then measured (2026-08-18): it buys
**7 of the library's 84 sites**, and the 71 it does not buy are blocked on
conversion rather than on anything an anti-unifier can be extended with. The
trade was named; what was not known then is how little was on the other side
of it.

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
- 2026-08-17: Third round running as a ranked item (waves L2'/L3, [[std-list-l2-prime-laws]], 2026-08-17), three new sites, and one of them is a shape this issue has not recorded before: filter_filter rewrites under a MATCH context, not a function application — j with a hand-written motive that restates filter's own body around the hole — so anti-unification would have to find a context that is a case tree. The other two are ordinary one-place contexts written as lambdas that the expected type already determines: cong_fn(λ (n: Nat) => or_pick(eq_dec(a, h), n, Succ(n)), …) in count_insert and count_isort, the same context twice. Direction datum for the same site: [[match-with-equation]] binds scrutinee = pattern, and rewriting the GOAL wants pattern = scrutinee, so the round's only sym is there.
- 2026-08-17: Fourth consecutive round ranks this, and the Int round (2026-08-17, [[std-int-encoding]]) is its largest customer by a wide margin: lib/std/int.hthr declares FOUR congruence lemmas (cong_int at Int -> Int, cong_int_of at Nat -> Int, cong_ofnat, cong_negsucc) and applies them 58 times, every one of them naming a one-place context that the expected type already determines. Two shape notes for whoever takes this. (1) The Nat -> Int arrow is new: a congruence is needed per ARROW, not per type, so a two-type file needs two even before the constructors get theirs. (2) 23 of the 58 sites additionally have to spell BOTH endpoints (@cong_int(f, x, y, p)) because the proof they rewrite by is an induction hypothesis whose type is a motive application ([[motive-application-hides-hypothesis-type]]) -- so at those sites anti-unification would have to recover the context from a goal AND the endpoints from a reducible hypothesis type. The two issues compound and the second is the cheaper fix.
- 2026-08-17: Correction to the 2026-08-17 count above, from the round that removed them ([[motive-application-hides-hypothesis-type]], landed): `lib/std/int.hthr` had 22 endpoint-spelled sites, not 23, and only EIGHT of them were the motive-application ones. The other fourteen rewrote by an ordinary lemma call at a real `Id` and check terse on the *old* elaborator (verified with the new reduction disabled) — they were spelled for consistency with the arms that had to be. The file now has no `@` call in it at all, so this issue's customer count at `Int` is 58 sites naming a one-place context, with no endpoint tax left underneath it.
- 2026-08-18: Fifth round: the FIRST empirical diagnosis of why the library does not write cong(p), and it changes what this issue should build next. Every one of the 84 library sites was rewritten to cong(p) one at a time and the failure classified. At lib/std/int.hthr (54 sites): 38 fail with 'could not infer' -- the trigger never fires, because the site is an argument of trans/sym at a domain whose metas are unsolved, i.e. inference position; 16 fail with 'cannot generalize' -- the trigger DOES fire, the expected type is in hand, and anti-unification still refuses. The second bucket is the one nobody had costed, and it is the wall. Its cause is not position: the congruence context is a fact about how the goal's two sides COMPUTE, not how they are spelled. addNat_zero_l's Succ arm wants f := isucc, and isucc occurs in neither side of 'addNat(OfNat(0), Succ(k)) = OfNat(Succ(k))' -- it appears on the left after one delta-iota step and relates to the right only by FOLDING isucc(OfNat(k)) back into OfNat(Succ(k)). The lowering compounds it: a match arm binds a constructor payload as one variable, so the goal side reads inr(...; v) where the reduced side reads inr(...; <a,b>) (Sigma-eta, not equality), and one level below that a Wf node's children are functions out of Fin, where the two sides differ by a beta-redex against a projection. An anti-unifier with untyped Sigma-eta and Unit-eta was written and measured: it moved ZERO sites, because by the time the mismatch is reached it has already sunk below eta. Reverted. Two consequences. (1) [[calc-equational-chains]] is NOT this issue's fix: a calc block clears the 38 in full and leaves the 16 untouched, because a calc step still states its sides in the reader's unreduced terms -- calc has to be justified by readability, not by this site count. (2) What the library actually needs is occurrence selection against a REDUCT plus a conversion check that the abstracted context reproduces the other endpoint. That is rewrite, and it is not an anti-unifier -- which is section 6's argument, now with evidence instead of assertion. What landed (docs/congruence-in-inference-position-design.md): a call whose callee declares a RESULT-ONLY implicit -- one no explicit parameter's domain mentions -- joins is_checking_only, so it is deferred and elaborated after its siblings at the domain they determined. Structural, not keyed to cong; an occurrence check on the KERNEL telescope, because the surface reading would have deferred every sym in the library (Id carries its type, so sym's A is not result-only); and strictly additive -- a result-only deferral that the fixpoint cannot unblock falls back to inference, so every program that elaborated before takes the old path and gets the old message. Plus a bounded loosening of decision 2: a SECOND attempt at the LGG with the goal's two endpoints in whnf, after the syntactic attempt has failed, with s and t deliberately NOT reduced. Yield, honestly: at int.hthr the buckets went from (38 could-not-infer, 16 cannot-generalize, 0 accepted) to (23, 27, 4) -- trigger reach 16 -> 31 sites, accepted 0 -> 4; 7 of 84 across the library. Count correction while here: the 2026-08-17 entry and int.hthr's own comment both said 58 sites at Int; the real number is 54 (the earlier count double-counted paren-less mentions in comments), and the library total is 84, not the 78 a first pass reports -- a scan that skips over a matched call misses the six congruences NESTED inside another one, all of which are refused. The library was deliberately NOT migrated -- 7 of 84 leaves every file mixing two spellings, leaves all eight monomorphic lemmas load-bearing, and falsifies the files' own comments about why they spell it by hand. Six tests added to crates/elab/tests/congruence_lgg.rs cover the shapes that flipped (both trans argument positions, an open element type, the reduction-only goal) and the two that must not (a nested chain keeps the old message; a witness mismatch inside a chain stays loud). Residue: [[lgg-diagnostic-dumps-kernel-terms]]. Issue stays open for the same reason as before, now better evidenced: the layer-m goal solver, occurrence selection, and rewrite.
- 2026-08-18: Datum from the calc round (docs/calc-equational-chains-design.md): the terse cong fails on a cross-type context through a constructor -- cong(nat::mul_assoc(...)) at expected neg(OfNat(X)) = neg(OfNat(Y)) in lib/std/int.hthr's mul_assoc -- because the two sides' elaborated OfNat annotations spell the inductive's type differently (raw Sigma-code vs El(code)), convertible but unequal, so the LGG sees a spurious differing position at the annotation. Same wall family as section 1.2: the comparison is syntactic and the mismatch is below it. The sites keep cong_ofnat/cong_int; noted here because this issue owns cong's inference.
