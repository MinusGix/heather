---
title: Type application spines and identity context references without quadratic substitution
status: open
labels: [kernel,elaborator,performance]
created: 2026-09-26
updated: 2026-09-26
---

Typing an application spine `f(a₁, …, aₖ)` instantiates the head's Π one
argument at a time: each node returns `cod[aᵢ/x]` (`Tc::tm_infer_inner`'s
`App` rule, `AppAt`'s fast path; the elaborator's `apply_explicit` likewise).
Each step copies the *whole remaining* telescope, and after the first steps
that telescope carries copies of the earlier arguments, once per mention. A
lemma with many arguments that are themselves sizeable terms therefore costs
O(k · |telescope with arguments|) in allocation and substitution, not
O(|telescope| + Σ|aᵢ|).

A second cost of the same kind: every reference to a global in context
(`GlobalTm { subst }`, which each lifted `bv_omega` proof and each named
`omega` atom list is) runs `Tc::subst_ck`, which instantiates every context
entry's type by the prefix of the substitution, cloning that prefix per
entry. For an identity substitution in a deep context this is quadratic in
the context and checks nothing a syntactic comparison of the two contexts
would not.

## Where it showed

`bv_omega`'s word lemmas (`add_form`, `sub_form`, `bound_*`) take up to 15
explicit arguments, most of them spelled forms, each mentioned several times
in the lemma's type. After [[bv-omega-check-cost]]'s rounds cut
`bv_place_step` to its necessary `omega` calls, a frame-pointer profile of
that one declaration (library replayed) put substitution at about a third of
its time, split between the gate and elaboration's `apply_explicit`, and
`subst_ck` alone near a tenth — more than any one `omega` call.

## Shape of a fix

Both are strategy changes with no semantic content:

- **Spines**: infer the head once, walk the Π telescope collecting a
  simultaneous substitution, check each argument against its *domain* under
  the substitution so far, and instantiate the final codomain once. Only
  domains are substituted per argument. The checked-spelling recorder
  (`Spelled::Pi` per node) needs each node's Π; that is the interaction to
  cost first.
- **`subst_ck` on an identity substitution**: when `delta` is the identity on
  Γ and the target context is Γ itself (pointer or syntactic equality after
  the global shift), the judgement holds without per-entry checks.

Measure with `scripts/perf ab` on `perf/fixtures/bv_omega/` and on the
corpus: hand proofs pay the same rule, with smaller arguments.
