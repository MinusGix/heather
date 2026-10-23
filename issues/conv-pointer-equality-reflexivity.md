---
title: Conversion never short-circuits on pointer-equal subterms
status: closed
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-08-10
---

Conversion used to re-normalize literally shared inputs and compare them
structurally like strangers. Pointer-identical syntax is reflexive, so it can
settle before whnf; a shared persistent context can likewise settle before the
entrywise judgmental walk.

The type-child slice first landed through [[class-lemma-instantiation-fuel]].
The completed round extends the same scoped identity invariant to term
children, adds borrowed root-type identity and syntactically identical
contexts, and leaves raw root terms alone because the measured workloads had
no hits there.

This compounds with the sharing rounds: [[subst-rebuilds-unchanged-subterms]]
and [[subst-visits-closed-subtrees]] mean conversion increasingly receives
the same `Rc` on both sides (unchanged annotations of two reduction
results of one term, schema pieces instantiated from one skeleton), and
every future round that increases sharing (notably schema caching,
[[schema-construction-caching]]) raises the hit rate further.

## Why it needs deciding, not just doing

- DESIGN.md commits conversion to "ch. 06 verbatim"; a reflexivity
  short-circuit is an extra rule, sound but a deliberate divergence to
  record there.
- Soundness argument to write down: `ptr_eq ⇒` identical syntax `⇒`
  equal in the level-equivalence quotient and equal-as-code, so neither
  the □-syntactic-equality invariant nor the Id-at-□ coincidence
  (DESIGN.md §Algorithms) is disturbed.
- Fuel: a hit spends O(1) instead of the structural cost — that is a
  fuel-*policy* visible change; decide whether a hit still pays `spend()`.
- Pin with a bench (a family whose two sides share, e.g. conv of a term
  against itself post-reduction) so the fast path cannot silently rot.

**Not in scope here:** whnf-result memoization. It is the riskier cousin
(env-dependence, fuel accounting per cached entry) and most of its win on
shared inputs is captured by this check; if a profile ever demands it, it
gets its own issue.

## What it assumes from elsewhere

- **[[subst-visits-closed-subtrees]]** (closed) owns the sharing-preserving
  skip machinery. Assumed here: only that substitution outputs share
  unchanged subtrees, which is what makes hits common.

## Log

- 2026-07-31: Denominator note after the Psi-clone and level-fast-path rounds (release heather check lib/certgen/ir_v1.hthr: 2.1s -> 1.305s). Conversion is now the top block in its own right -- Conv::ty 6.6% self, whnf_ty 3.6%, whnf_ty_opaque 2.9%, plus Rc<Term>::drop_slow at 6.9% and Type drop glue 3.8% just behind, which is the shape of a walk that re-descends structure it could have recognized. Nothing here was measured directly and the trigger is unchanged; recorded only so the percentages in this file are not read against the old 2.1s run. Adjacent evidence in favour: the same reflexivity shortcut taken for levels this round ([[level-normalization-allocation]]) was worth 11% of the whole run on its own.
- 2026-07-31: Scoping datapoint from the deep-path investigation ([[whnf-sharing-term-growth]]): reflexivity short-circuits cannot help the add(2,3)-through-LetCall path. Its whole cost (~56% substitution + allocate/free/drop, the rest bounds probes) is PRODUCING the normal form; by the time two terms are compared the work is already spent, and the sides are never pointer-equal. Noted so this issue is not reached for as a deep-path lever.
- 2026-08-06: A new short-circuit site from the Γ-spine round ([[context-representation-clones]], closed): `CtxEntries` is now a persistent snoc spine whose `PartialEq` already ptr-eq-shortcuts, but `Conv::ctx` still runs the full per-entry judgmental walk even when `a.entries == b.entries` — a syntactic-equality (or spine-ptr-eq) fast path there is sound (syntactic equality implies convertibility) and would be near-free, since derived scopes now share spines by construction. Deliberately left out of that round to keep it representation-only (it changes fuel spend, and the golden-hash argument stayed airtight because behavior was untouched). Same trigger discipline as the rest of this issue.
- 2026-08-10: Type-child slice landed from [[class-lemma-instantiation-fuel]]: its failing conversion entered `Conv::ty` 474,701 times on shared type children before exhausting `2^20` fuel; scope-aware closure identity makes the real class/Wf theorem pass and cuts the capped release check from ~0.37s to ~0.14s. A term-child shortcut was prototyped first and had no effect, locating the win specifically at types. The hit spends one comparison unit; `home`/`sat` equality is required because one closure opened under different pending binders need not denote one type. Kernel DESIGN records the soundness boundary and a unit control pins it.
- 2026-08-10: CLOSED after measuring the remaining four candidates separately. A release `lib/certgen/ir_v1.hthr` check saw 1,465 scope-safe term-child identities and 88 identical root types, but zero raw root-term and context hits; the generated `conv/perturbed-pairs` corpus exercised term children, root types, and contexts, while root terms again stayed at zero. Landed the three demonstrated paths: general term children require equal closure pointer plus equal `home`/`sat`; borrowed root types use object identity; contexts use syntactic equality, whose persistent `CtxEntries` comparison stops in O(1) on a shared spine. Raw root terms remain unchanged. Every hit spends one fuel unit. One-unit fuel tests pin root-type and context behavior; the term unit uses the same closure under matching and mismatching scopes to pin both the shortcut and its load-bearing metadata. The full differential/workspace suite is green, and `scripts/bench --check --filter conv` passes all four scaling comparisons. No new synthetic benchmark was added: the existing generated-pair family is the representative corpus that exposed and continues to exercise all three paths.
