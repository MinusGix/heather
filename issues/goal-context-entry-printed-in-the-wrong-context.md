---
title: A goal hole's context entry is displayed against the whole of Γ, so its type names the wrong binders
status: open
labels: [frontend,diagnostics,display]
created: 2026-08-17
updated: 2026-08-17
---

Found while designing [[motive-application-hides-hypothesis-type]] (2026-08-17), by
probing what a hole in an induction step arm shows.

An `UnsolvedGoals` report lists the hole's context by zipping `cx.names` with
`cx.gamma.entries` and rendering each entry's type with `display_type(&g.cx,
&e.ty)` (`crates/elab/src/lib.rs`, the `GoalReport` construction). The context
passed is the **whole** of Γ, but an entry's type is scoped in the *prefix* of Γ
that precedes it, so every de Bruijn index in it is read one (or more) name too
late:

```heather
theorem q(a: Nat, p: add(a, 0) = a): a = a { ?g }
// context printed:  a : Nat,  p : add(p, 0) = p
```

`p`'s type mentions `a`, and the listing calls it `p` — the entry names itself.
The goal's own *statement* is right (it is scoped in the full Γ, which is what
`display_type` is being told); only the entries are wrong, and only those whose
type mentions an earlier binder — which is every hypothesis worth having.

Not a soundness matter and not a kernel matter: the elaborated term is
unaffected, and `on ?g := …` discharges against the real type. It is a
diagnostic that misleads exactly when it is being read, which is when someone is
stuck.

## The fix

Render an entry against the context prefix it belongs to, i.e. walk the entries
with a growing `Cx` (names and `gamma` truncated to `i`) rather than reusing
`g.cx` for all of them. The aliases chained on after the entries need the same
question asked of them.

## What it assumes from elsewhere

- **[[goal-holes]]** owns the report and its shape. Assumed here: only that the
  context listing is `(name, rendered type)` pairs built at report time.
- **[[motive-application-hides-hypothesis-type]]** found it and owns nothing of
  it: the redex in that issue was a red herring here — the same misprint happens
  for an ordinary annotated parameter, which is the repro above.
