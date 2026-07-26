---
title: Empty-eta in conv.rs
status: open
labels: [kernel,conversion,metatheory]
created: 2026-07-26
updated: 2026-07-26
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
