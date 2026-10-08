---
title: Empty-eta in conv.rs
status: closed
labels: [kernel,conversion,metatheory]
created: 2026-07-26
updated: 2026-10-07
---



Carried out of [[wf-former]], where it sat as "also in scope,
decision-independent" through all five phases and was never needed. Split
out rather than done as a drive-by, because it is a change to **conversion**,
and that is the one part of the kernel the `Wf` round deliberately did not
touch.

## What it is

Proof irrelevance at `Empty^l`: any two terms of type `Empty^l` are
convertible. Vacuous for closed terms — `Empty` has no canonical inhabitant —
but *not* vacuous under a false hypothesis, where neutral inhabitants exist
and today are only convertible when structurally equal.

`Unit` already has exactly this rule in `conv.rs`, and the tag discipline of
`docs/inductive-tier0-lowering.md` §3.3 leans on it hard. `Empty`'s is its
mirror image.

## Why it is not blocking, and why it was not just done

- **Not blocking.** The `Wf` round's nullary arm was the case it was expected
  to be needed for, and it was not: arity 0 is `Vec^l(child; 0) ⇝ Unit^l`, so
  `Unit`'s irrelevance already collapses every nullary constructor form,
  including the `u : Unit` payload in the tag (`docs/wf-former-design.md`
  §9.4). Route A's round is where the expectation came from, and route A is
  not the path taken.
- **Where it would pay.** Tier-2 `Acc` under `W`: the route-A prototype's
  negative test (`crates/elab/tests/branching_route_a.rs`) shows a `refl` in
  the leaf arm being rejected, and `Empty`-η is what would erase that funext
  obligation. That is the concrete customer, and it belongs to whatever round
  does tier 2.
- **Why not a drive-by.** `docs/wf-former-design.md` §5 states the discipline
  the whole round kept: "no change to the Π arm, no change to the existing η
  rules — the *ch. 06 verbatim* discipline stays intact where it matters." A
  *new* η rule is not in ch. 06, so it owes an argument at ch. 07 — an
  irrelevance clause in the logical relation, of the kind
  `docs/metatheory-ch07-extensions.md` already writes for `Unit`. Small, very
  likely fine, and still an argument rather than a patch.

## What it would take

1. The ch. 07 clause, by analogy with `Unit`'s, in
   `docs/metatheory-ch07-extensions.md`.
2. One arm in `conv.rs`'s `tm_nf`, next to `Unit`'s.
3. Negatives: it must not make two *types* convertible, and it must not
   disturb `conv_pair_properties`' "η is not blind" test — which already
   moved once, to `Σ(S, Nat)`, when generated proof-irrelevant types started
   appearing in the well-typed generator (`crates/kernel/tests/common/wt.rs`).
4. The property suite reaches `Empty` through the generators already, so
   `conv_properties` and `ch05_06_lemmas` cover it for free once the arm
   exists.

## Log

- 2026-07-26: The named customer does not want it. This issue records tier-2 Acc under W as 'the concrete customer' for Empty-eta, from route A's negative test where a refl in the leaf arm is rejected. Acc is now built (docs/acc-via-w.md, crates/kernel/tests/acc.rs) and needs it nowhere: Psi is empty, and the leaf arms -- the positions under a numeral, where R reduces to Empty -- are discharged by elim_Empty because they are children functions being BUILT, not two children functions being COMPARED. Comparison is what route A's leaf arm was doing and what needs funext/Empty-eta; the fording's Acc never states an equation between trees. So the issue keeps its case (proof irrelevance at Empty is still the mirror of Unit's, still owes a ch. 07 clause, and is still right) but loses its customer: nothing open now wants it. The customer it would have is the direction Acc does not need -- proving Acc(a) a proposition, i.e. that wfrec is independent of the accessibility proof supplied. Re-file that as the motivating case if this is picked up.
- 2026-10-07: Done, and closed. The heather-coq formalization added Empty η
  as proof irrelevance and carried it through the logical relation, the
  fundamental theorem, the algorithm and decidability with no admits
  (heather-coq PR #7). The ch. 07 clause asked for in step 1 is
  `docs/metatheory-ch07-extensions.md` §28. Step 2 needed two changes, not
  one: the `tm_nf` arm (`TyView::Empty => Ok(())`), and the `elim_Empty`
  congruence in `tm_ne` skipping its scrutinees as `elim_sEmpty`'s does,
  since otherwise conversion rejects pairs the rule equates. The arm is
  dispatched on the type's whnf, so `Fin(0)` reaches it. Step 3's
  negatives hold: no two types become convertible, and the "η is not
  blind" test at `Σ(S, Nat)` is unaffected.
  The full suite then caught an elaborator consumer: motive synthesis
  compared the goal's stuck subterms with the scrutinee at the scrutinee's
  type, whatever their own type, so at `Empty` a `Nat` subterm "converted"
  and was abstracted. `motive_candidate_converts` now confirms a hit by
  checking the candidate's type too (§28).
