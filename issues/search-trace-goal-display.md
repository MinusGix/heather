---
title: Spell a failed search's goals as the goals they are
status: closed
labels: [diagnostics]
area: language
created: 2026-11-06
updated: 2026-11-06
---

A failed `:= infer` search prints its trace with each goal's *display*
string, which is the parameter type's spelling with its arguments dropped
and the rule's own binder names in place:

```
error: no instance for `Apart(add(sub(c, b), abs(e)), ofInt(OfNat(0)))` — the search:
  goal: b.Apart
  rules: Rat::Apart (5 rule(s))
  candidate: rat::Rat::apart_of_negative
      goal: x.Negative
```

`b.Apart` is `Rat::div`'s `h: b.Apart(0)` (the divisor here is
`(c - b) + e.abs()`), and `x.Negative` is `apart_of_negative`'s premise
before its `x` was solved. The header line spells the real goal, but in
the internal form (`add(sub(c, b), …)`, `ofInt(OfNat(0))`).

Wanted: each `goal:` line spelled from the instantiated goal in source
form (`((c - b) + e.abs()).Apart(0)`, `((c - b) + e.abs()).Negative()`),
falling back to the display string only when it does not spell. The
display is pushed at `crates/elab/src/resolve.rs`'s `resolve_goal_from`.

## Log

- 2026-11-06: Done: an obligation's refusal writes its spelled goal into its trace's first `goal:` line too, so each nested search's goal is spelled once, where its refusal is made (no cost on success). The spelling is the function-call one (`Apart(mul(b, b), ofInt(OfNat(0)))`); operator resugaring is issues/diagnostic-operator-resugaring.md's.
