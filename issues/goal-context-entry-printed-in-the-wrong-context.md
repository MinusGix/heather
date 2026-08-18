---
title: A goal hole's context entry is displayed against the whole of Γ, so its type names the wrong binders
status: closed
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

## Log

- 2026-08-17: Fixed as sketched. `Cx::prefix(n)` (crates/elab/src/lib.rs) cuts a context back to its first `n` binders — names, `gamma.entries` (via the kernel `CtxEntries::prefix`, which shares the spine) and `skels`, keeping the base and everything that is not positional — and the `GoalReport` construction renders entry `i` against `prefix(i)`. The entry walk is `enumerate`d *before* the `#`-binder filter, so a hidden ih still occupies its index. The goal `statement` still renders against the whole of `g.cx`: it really is scoped there, and a test now pins that alongside the entries so neither can be traded for the other. **The aliases: same fix, and the field-binder half turns out to be invisible today.** An `Alias` stores `ty` scoped at the `depth` it was bound at — already the invariant its *uses* depend on, since both `infer` and `resolve`s scope search shift an alias by `names.len() - depth` before touching its type — so the listing renders one against `prefix(a.depth)`. Whether that changes printed text splits by where the alias came from. (a) A `let` alias: yes, observably — its type is written in the surface, so it spells and can name an ordinary binder; `let e: (add(a, 0) = a) = …;` read from inside a `Succ(k)` arm printed `e : add(k, 0) = k` before the fix, the arm having pushed `k` and the hidden ih on top of the alias depth. (b) A constructor field binder in a tier-0 arm: no, not today — `elab_arm` aliases field `j` to `fst(snd^j v)`, so a *dependent* field type mentions projections of the scrutinee, which the speller declines and the listing prints as raw budget-bounded `Debug`, de Bruijn and naming nobody, hence the same string in any context; and a field type mentioning no earlier field is closed and reads the same in any prefix. So a field alias cannot currently misname anything, and becomes able to the day projections spell. That is pinned rather than assumed: `an_arm_field_alias_is_rendered_at_the_depth_it_was_bound` asserts the alias is listed and that its type names no binder pushed after it. No other diagnostic renders a stored type against a context it is not scoped in — `display_type`s only other callers (the `trivial` and lambda-domain messages, and `display_type_clean`s got/expected pair) are handed a type scoped at the current point, and `resolve`s trace lines carry names, never types. The goal report was the one site of the pattern in the tree. Tests, crates/elab/tests/goal_holes.rs: the repro above; a five-binder chain where `p`, `q`, `r` sit at three different depths and each names binders further out (a fix using one fixed prefix would pass the repro and fail this); the two alias cases. Reverting either half of the fix fails three of the four with exactly the misprint reported here — `add(p, 0) = p`, `add(q, p) = q`, `add(k, 0) = k`. No existing assertion had to be corrected: the old goal-display tests asserted entry *names* and `k : Nat`, which is closed and so reads the same either way — which is also how this survived. Display-only throughout; nothing on the elaboration or discharge path was touched.
