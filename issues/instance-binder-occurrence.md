---
title: Every instance binder should have to occur in the head, type parameters included
status: closed
labels: [frontend,elaboration,traits,diagnostics]
created: 2026-08-17
updated: 2026-08-31
---

A **value** binder must occur in the instance head
([[value-generic-instances]], `docs/value-generic-instances-design.md` §4): it
is determined by unifying the head against the goal and by nothing else, so one
the head omits is a metavariable nothing can ever solve. A **type** parameter
carries no such rule, and `instance<A> Dec<Bot>` declares happily.

The asymmetry was not reasoned about when the value rule landed — §4 claims it
is deliberate, and it was only unexamined. This issue is the examination.

## What the loophole actually does today

Measured 2026-08-17, not assumed:

| | |
|---|---|
| `instance<A> Dec<Bot>` declares | **yes** |
| a goal resolves through it | **no** — "cannot infer the type argument `A`" |
| `Bot::Dec<Nat>.d` by hand | **yes**, it works |
| the same for a value binder (`@Bot::Dec(3).d`, check lifted) | **yes**, symmetric |

So it is not broken, and the use-site diagnostic is good — it names the
candidate, the reason, and the escape. What it is, is a registry entry that
**no goal can ever use and every goal must still try**: selection walks every
candidate of a class in sorted order, so a never-resolvable instance is a
permanent per-goal cost ([[resolution-candidate-fan-out]]) with no possible
payoff. Naming the value by hand is better served by a `fn`, which is not in
the registry.

The deeper reason to refuse: a head-absent binder is the syntactic signature of
*"resolution, please guess"* —

```heather
instance<A> Serialize<Nat> requires enc: Encoder<A>   // find me any Encoder
```

— and this resolver is selection-by-trial per candidate with no
metavariable-driven search, deliberately. Refusing at the declaration says so
once rather than at every use site.

## The rule is NOT "occurs in the class arguments"

The two binder kinds differ in *where a goal can determine them from*, and the
rule has to follow that rather than be uniform for tidiness:

- A **type parameter** may occur in an **index**, and does so usefully:
  `instance<A> Mag<Bool2>(pick<A>)` declares AND resolves (verified). An index
  argument may be a global reference at the instance own type parameters, and
  the index is part of the class type, so the goal determines it. Its rule
  counts **arguments and index**.
- A **value binder** may now occur in an index too. Resolution recovers it by
  candidate-head unification, while the registry uses an alpha-stable binder
  position rather than the local spelling. Its rule therefore counts
  **arguments and index**.

`head_var_count` and `index_var_count` in `crates/elab/src/traits.rs` already
split along exactly this line.

## Cost

Zero in-repo: no declaration in `lib/` and no test in the suite uses the
loophole — measured by adding the check and running the full suite, which gave
1762 passed / 0 failed with it on.

## What it does not claim

That the current failure mode is bad. It is early-and-coherent versus
late-and-well-explained, plus the fan-out cost. That is the whole of it.

## Acceptance

`instance<A> Dec<Bot>` is refused at the declaration, with a message routing the
three intents a reader might have had (a class **index**, a plain `fn`, or the
guess that is deliberately unavailable); `instance<A> Mag<Bool2>(pick<A>)` still
declares and still resolves; and `docs/value-generic-instances-design.md` §4 no
longer claims a justification the round did not have.

## Log

- 2026-08-17: Landed. The rule now covers both binder kinds, and the examination changed what the rule IS rather than just widening it: it is genuinely asymmetric, but not where the asymmetry had been sitting. A type parameter counts the class arguments AND the index; a value binder counts the arguments only. The reason is that the two differ in where a goal can determine them from — an index argument may be a global reference at the instance's own type parameters and the index is part of the class type, so `instance<A> Mag<Bool2>(pick<A>)` both declares and RESOLVES (tested in both directions, because an exception protecting a declaration nobody can use would be exactly what this rule exists to refuse). A value binder cannot reach an index at all, since an index joins the key as a spelling and must be a global reference; that case keeps its own message. The args-only rule I first experimented with would have refused the Mag case, which is why the test exists. Cost measured rather than estimated: the check was turned on and the full suite run before any of this was written — 1762 passed, 0 failed, and zero declarations in lib/ use the loophole. What it buys, stated at its honest size: earliness, one rule instead of two, and one fewer registry entry that no goal can use and every goal must still try ([[resolution-candidate-fan-out]]). What it does NOT buy is a rescue — `instance<A> Dec<Bot>` was not broken, its use-site diagnostic already named the candidate, the reason and the escape, and `Bot::Dec<Nat>.d` worked by hand. The new message routes the three wishes a head-absent binder expresses: a class index (which joins the key, so the alternatives coexist), a plain `fn` (a value with no registry entry), and resolution guessing — the one reading that is unavailable on purpose, because search selects among candidates and never guesses an argument. docs/value-generic-instances-design.md §4 is rewritten: §4.1 states the asymmetry and why, §4.2 records the cost and refuses to overclaim. §5 gains the one place the two measures deliberately diverge — Paterson's head measure stays args-only for type parameters too, which is narrower than the recovery rule and refuses programs rather than admitting bad ones; no instance of an indexed class in lib/ has a `requires`, so there is no customer for loosening it.
- 2026-08-31: [[collection-literal-protocol]] supplied the first concrete need
  for a value binder determined only by a class index. Generic index binders
  now use alpha-stable `#binderN` registry keys and are recovered by ordinary
  candidate unification. The absent-from-both rule remains; tests pin both
  successful resolution and alpha-renamed duplicate rejection. Replacing the
  bounded spelling-based overlap check if index forms widen belongs to
  [[structural-instance-index-overlap]].
