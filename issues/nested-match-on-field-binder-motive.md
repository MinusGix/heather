---
title: A motive-less nested match on a constructor field binder gets a non-dependent motive
status: closed
labels: [frontend,elaborator,proofs,ergonomics]
created: 2026-08-17
updated: 2026-08-17
---

Filed by the `Int` round ([[std-int-encoding]]), where it is the **most
expensive** thing the language did — fourteen written motives in one file, none of
which says anything a reader wants to know.

A `match` in checking position with no `as` motive synthesizes one by abstracting
the scrutinee out of the expected type (`Elaborator::synth_motive`,
`crates/elab/src/lib.rs`). It does that **only when the scrutinee elaborates to a
`Term::Var`**; otherwise it falls back to the expected type weakened under `z` —
the non-dependent motive — and the arm goals never specialize.

A tier-0 arm's field binders are *not* variables. They are aliases for
projections out of the constructor value ("The binders are *aliases*, not kernel
binders: the kernel has no `let`, so each use is the projection term",
`crates/elab/src/inductive.rs`, `elab_arm`). So the moment a proof case-splits on
a *payload* of the constructor it just split on, the inner `match` silently
becomes non-dependent and the goal is unprovable.

## The repro, which is four lines

```heather
inductive Box { Wrap(n: Nat) }

fn ddb(b: Box) -> Box {
    match b { Wrap(n) => match n { Zero => Wrap(0), Succ(k) => Wrap(Succ(k)) } }
}

theorem ddb_id(b: Box): ddb(b) = b {
    match b { Wrap(n) => match n { Zero => refl, Succ(k) => refl } }   // NotConvertible
}
```

The same shape at a `Nat` outer scrutinee **works** (`std/nat`'s `half_le`,
`even_or_odd`, `half_add_half` are all motive-less two-level splits), which is
why no round before this one met it: `Nat`'s arm binder *is* a variable. The fix
is writing the inner motive by hand, at which point both spellings check:

```heather
    match b { Wrap(n) => match n as λ y => ddb(Wrap(y)) = Wrap(y) { … } }
```

## Why it is the round's top item

`Int`'s constructors *are* `Nat`-payload wrappers, so "case on the integer, then
on its payload" is not a corner — it is how `isucc`, `ipred`, `neg`, `negOfNat`
and everything proved about them is written. `lib/std/int.hthr` writes 51 explicit
`match … as` motives, and **26** of them are over a payload `Nat` reached from an
`Int` arm. Fourteen of those 26 are *purely* this defect — `neg_neg`,
`isucc_ipred`, `ipred_isucc`, `neg_isucc` ×2, `neg_ipred`, `add_isucc`,
`add_ipred`, `add_neg`, `mul_neg_r` ×2, `mul_isucc`, `lt_irrefl` and `le_of_lt` —
nothing else in those proofs needs a motive, and each one is a
restatement of the arm's own goal with the constructor put back around the binder.
The other twelve are in the order kit, which needs a written motive anyway to
convoy its hypotheses (`std/nat`'s order pays the same), so they are not charged
here.

Two further costs worth recording, both about the *shape* of the failure:

- It fails at the **kernel**, as `NotConvertible` with the declaration's span,
  not at the site of the mis-synthesized motive. The first hour of the round went
  into localizing it, and an unfilled goal hole was the tool that found it — via
  several hundred columns of raw `El` ([[le-diagnostics-print-raw-el]], another
  customer).
- The synthesized non-dependent motive is *silently* weaker. Nothing warns; the
  arm simply cannot be closed, including by `{}`.

## The fix, and its relation to the neighbouring issue

`synth_motive` should abstract syntactic occurrences of the **scrutinee term**,
not only of a variable. For a field binder the scrutinee is a projection whose
occurrences in the expected type are syntactically identical, so the same
"clear-and-generalize" substitution applies with the pattern being a term rather
than a `Var(i)`; the eliminator's obligation `M[scrut/z] = expected` is
discharged the same way.

This is very likely the **same fix** as `goal-motive-by-scrutinee-abstraction`
(ranked #1 by the list/`std` round that closed 2026-08-17 at ten sites: motive
synthesis abstracts only *syntactic* occurrences and never whnfs the goal). That
issue is not in this round's worktree, so the sites above could not be added to
its count as [[std-api-waves]] asked — **coordinator: merge this into it if it is
the same defect, keeping the `Box` repro and the 14-site count**, which is a
strictly larger customer than the ten it already has.

## What it assumes from elsewhere

- **[[std-int-encoding]]** owns the round that found it. Assumed here: only that
  `Int`'s constructors carry `Nat` payloads, which is the encoding it settled.
- **[[le-diagnostics-print-raw-el]]** owns goal display. Assumed here: nothing —
  it is named as a cost, not a dependency.

## Log

- 2026-08-17: Filed by the `Int` round, with the four-line `Box` repro and the mechanism read off `synth_motive` + `elab_arm` (field binders are projection aliases, so the `Term::Var` guard never fires). 14 sites in `lib/std/int.hthr`; ranked #1 of that round's six.
- 2026-08-17: Verified after the diagnostics pair landed and all three of the day's rounds were merged (2026-08-17): this class is NOT localized by [[check-fallback-discards-expected-type]]'s fix. The four-line Box repro still reports exactly `the kernel rejected 'ddb_id': NotConvertible` at the declaration's span, because the arm's proof is `refl`, which has its own checking arm and is one of that round's own deliberate controls (a `refl` at a false equation stays a kernel rejection). So the control quotes in this issue remain accurate, and the diagnostics round did not reduce the cost of finding this defect — only the cost of reading a goal hole once you suspect it ([[le-diagnostics-print-raw-el]] is what both rounds actually used to localize it). Bearing on scheduling: the two motive issues are now the strongest-evidenced open items and nothing that landed today weakens the case.
- 2026-08-17: Fixed 2026-08-17 together with issues/goal-motive-by-scrutinee-abstraction.md, in one function (Elaborator::synth_motive) — coordinator: merging them is right, but the shared sentence in both issues is only half the fix, and this is the half it gets wrong. 'Abstract syntactic occurrences of the scrutinee TERM rather than of a Var' does NOT fix this defect: the field binder does not occur in the goal at all, before or after reduction. The arm's goal is the outer motive at the arm's VALUE v (ddb(v) = v), while the binder is fst(snd v). Measured: with term-abstraction and goal reduction both in place the four-line Box repro still failed. The fix is the opposite move — replace occurrences of v by the constructor value rebuilt around z, ⟨tag, z, ⟨⟩⟩, with the other fields still projected out of v, which is exactly what the hand-written 'λ y => ddb(Wrap(y)) = Wrap(y)' said. Single-constructor: the arm's value IS the scrutinee term. Multi-constructor: it is the case binder under an injection, and abstracting the binder rewrites inside the injection. The obligation rep[field/z] = v is Sigma-eta plus Unit-eta, which the kernel has and which the fourteen written motives were already relying on. Collected: 13 of the 14 sites in lib/std/int.hthr lose their motives (neg_neg, isucc_ipred, ipred_isucc, neg_isucc x2, neg_ipred, add_isucc, add_ipred, add_neg, mul_neg_r x2, mul_isucc, lt_irrefl). The fourteenth, le_of_lt's inner split on m, is NOT this defect: it is APPLIED to its hypothesis, so it is an inference position convoying p past the split — the same shape as the twelve order-kit motives this issue already excluded, and it keeps its motive with a comment. So the honest count for this defect is 13. Box repro is a test (crates/elab/tests/motive_synth.rs), with the Succ-depth nesting, an open element type, a literal scrutinee, and a sibling-field mutation control that pins the field that must NOT be abstracted.
- 2026-08-17: Coordinator, at merge: the merge-if-same-defect condition is NOT met — one function, two mechanisms, neither subsuming the other (the round's measured verdict) — so this issue stays its own record rather than folding into goal-motive-by-scrutinee-abstraction. Both close together with the round.
