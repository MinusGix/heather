---
title: Fold site facts into the one checker: residuals as propositions over the final state, preconditions over parameters, Pre at the lent window
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`lib/lang/ownership/site_facts.hthr` added, beside `call_check.hthr` and without touching it, what a source proof needed to reach a residual ([[ownership-residuals-from-source-proofs]]). Each belongs in the checker when it is next reshaped, not in a second module over it.

## Scope

- **Residuals as propositions over the final state.** `Fact::Holds(pres, s: Sem)`, not `Owed::Holds(pres, words)`: a bound reads a version's length, which no word holds. Each open residual stated as the proposition the source writes (a bound as a squashed `<`), so the source's proof is the discharge by conversion. Apartness: a residual naming its side (the window before the element, or after) instead of the Boolean verdict over the disjunction, which today needs `omega` because the verdict spells `0 + k <= j` against the source's `k <= j`.
- **Bounds emitted by the checker** (`bounds`, one per element read), and through a view (`Read`), which `site_facts` does not bound.
- **Preconditions over the parameters' values** (`FnSafeAt`): `pick(xs, i, inside: ∥i < xs.len()∥)`, the arena's `read`, has a precondition that reads its list.
- **`Pre` at the lent window's value**: `Pre(g, args)` holds `pres(g, vals(args, words))`, over the call's words only, so a callee whose precondition reads its parameter (the arena's `read` called from a caller) cannot be called. And a call of a reader that answers a word (no `CallMut` or `CallView` shape is one).
- **The branch over any bound word**: `Branch` tests only the words given, because its run and its meaning must agree on the test and `FnSafe` does not export `Sim.words`. A test over a word the body bound is the checker's own branch.

## What it assumes from elsewhere

- **[[ownership-checker-loans-and-joins]]** owns the checker's branch and join. Assumed here: residuals under a branch carry its test as a hypothesis the discharge can name (`decide_true` of the convoy's equation), as `branch_sound` does.
- **[[ownership-residual-discharge-restated]]** owns the form the discharge is asked in.

## Done when

`check_sound` itself states residuals over the final state in the source's vocabulary, with preconditions over parameters and `Pre` at the lent window, and `site_facts_tests` passes against it without `site_facts`.

## Log

- 2026-11-25: `site_facts.hthr` and its probes are removed from the tree. They were written against `call_check.hthr` as the second experiment left it; the fourth experiment restructured that module into one checker (a tree body, places for versions, views opened to read or write), and the two had never been combined: merged, `site_facts.hthr` has eleven errors (`Sem` has no `objs`, `Get`'s arity, `Safe`'s arguments). They are not kept beside a checker they do not fit. The module and probes are at commit 87ff7d6 and on branch `claude/ownership-residual-discharge`; this issue's work is to re-express them in the one checker, and its done-when ("`site_facts_tests` passes against it without `site_facts`") is unchanged. Until it lands, the fifth experiment's result stands on that branch's own green suite, not on this tree.
