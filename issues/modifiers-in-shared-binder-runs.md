---
title: Allow per-name modifiers inside a shared-annotation run: `g as ∙, h: T` and `self x, y: T`
status: open
labels: [frontend,ergonomics,parser]
created: 2026-08-11
updated: 2026-08-11
---

**Decided on user review (2026-08-11): allow.** Not urgent; filed so the two
refusals are lifted together when someone is in the parser anyway.

The multi-binder round refused a modifier anywhere in a shared run — `self x,
y: A` and, following its precedent, the op-as round refused `g as ∙, h: A ->
A -> A` — under the sentence "a modifier prefixes exactly one name." The user
review read that sentence the other way, and the other way is right: the
modifier *does* prefix exactly one name — the one it is written on — and the
annotation is the only thing the run shares. `g as ∙, h: A -> A -> A` is
unambiguously "`g` carries `∙`; `g` and `h` are both `A -> A -> A`", and
`fn List::concat<A>(self x, y: List<A>)` is structurally sensible the same
way. Nothing downstream cares: the symbol's scope already starts at its own
binder, `check_symbol_free` runs per spelling not per group, and `self` is a
per-parameter flag.

What lifting costs: the two parser refusal sites (both in the fn/theorem
parameter loop; the `as` one also guards nothing else), reading the modifier
per-name inside the run instead of erroring at the comma, and rewording the
design-doc sentence to what it now means — a modifier attaches to the name it
prefixes, per-name, not per-group. Tests: the two refusal tests become
positive pins (symbol on the first name of a run, `self` likewise), plus a
control that the *second* name of a run may carry its own `as` and that two
symbols in one run still hit the uniqueness rule.

## What it assumes from elsewhere

- **[[binder-symbol-as-notation]]** (closed) owns the as-device. Assumed here:
  only that a binder's symbol scope starts at the binder itself.
- **[[multi-binder-function-types]]** (closed) owns the shared run. Assumed
  here: only that the run desugars to the curried chain per-name, so a
  per-name flag has an obvious binder to land on.
