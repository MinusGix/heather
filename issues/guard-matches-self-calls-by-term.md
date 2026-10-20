---
title: The Wf guard matches self-call arguments syntactically
status: open
labels: [elaboration,inductives]
area: language
created: 2026-07-26
updated: 2026-07-26
---



Noted while landing [[wf-former]] phase 5. Not a bug today; a brittleness
worth a comment and a decision before someone touches alias construction.

## What it is

`issues/match-recursion.md`'s rule is that a structurally guarded self-call
*is* the induction hypothesis. For `Nat` the analysis compares the call's
decreasing argument against a **binder position** (`Guard`'s `pred_pos`),
which is robust: positions are absolute and shadowing cannot fake one.

For a `Wf` arm there is no position to compare. An arm binder is an *alias*
(tier 0 §5.1) — the kernel has no `let`, so each use is the projection term
itself — so `GuardKind::Wf` carries the children's **terms** and
`elab_self_call` matches with `==` after shifting
(`crates/elab/src/lib.rs`, and `docs/inductive-tier1-wf-lowering.md` §6.4).

That preserves the property that matters: the comparison is on what the
argument *elaborated to*, so a shadowing binder cannot pass itself off as a
child. What it gives up is stability under any change to how the child term
is built.

## The failure mode

Syntactic. If the child alias is ever constructed differently at the two
sites — the guard table in `wf_branch` and the argument's own elaboration —
a **legitimate** self-call stops matching and is rejected with
"recursive call to `f` must descend: argument `t` has to be one of the
recursive fields bound by the enclosing `match`", which is a confusing thing
to read when you did exactly that.

The direction is safe (`Nat`'s positional check has no such mode, but this
one only ever *rejects*; a bogus call cannot be accepted). It is a
diagnosability and maintenance cost, not a soundness one — the kernel
re-checks whatever gets through either way.

Concretely, the term is `nth^l(⟦D⟧; mᵢ; cs'; ι_t)`, built by
`wf::nth_child`. It is stable as long as both sides go through that one
function and `⟦D⟧` is built identically at both — which is true now because
`lower_instance` is deterministic, and would stop being obviously true if the
lowering ever cached, interned, or normalized types.

## Options

- **Leave it, document it.** A comment at `nth_child` and at the `==` saying
  both sides must go through this function. Cheapest, and honest.
- **Compare up to conversion.** `conv_term` at `⟦D⟧` instead of `==`. Robust
  against representation drift, but it makes an untrusted *analysis* depend
  on the conversion checker, and it would accept a call on a term merely
  convertible with a child — which is arguably right and arguably a
  termination hole worth thinking about before allowing.
- **Give arm binders a real identity.** Tag the `Alias` with which child it
  is, and match on that rather than on the term. Most robust, and it is
  really a question about whether `Alias` should carry provenance generally —
  which would also improve the goal listing, where `#`-prefixed elaborator
  binders are currently filtered out as unspellable.

Cross-cutting note: option 3 touches the same structure as
[[nested-goal-discharge]]'s view of what a goal's context should show.
