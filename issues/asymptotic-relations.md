---
title: Approaches and Landau relations with their witnesses as data
status: open
labels: [stdlib,mathematics,analysis,reals,design]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-10-27
---

Layer C of `docs/analysis-foundations-design.md` (§5): countable nested
neighbourhood bases ("approaches") and Landau relations whose constants and
moduli are data, instead of filters.

Scope:

- `Approach<A> { near: Nat → A → Type, mono }` and `Eventually` with the
  threshold as data; instances `n → ∞` on `Nat`, `y → x` (within a set, from
  the right) and `y → ∞` on `CReal`;
- `BigO` (rational constant), `LittleO` (a modulus `Nat → Nat`), `Asym`
  (`f - g = o(g)`, no division), `Tendsto`, continuity at a point;
- the closure algebra proved once: `+`, scalars, `O·O`, `o·O`, transitivity,
  `o ⊆ O`, `~` an equivalence, and composition along a map that tends;
- the bridge: `CReal::Same` and `CReal::Limit` restated as `Eventually` /
  `Tendsto` at `n → ∞` (theorems relating the forms; definitions unchanged).

Acceptance: probes at sequences `Nat → Rat` (e.g. `1/(n+1) = o(1)`,
`n = O(n²)`, a composed `o` through the closure lemmas), and the `CReal`
bridge theorems.

## What it assumes from elsewhere
- **[[real-completeness-interfaces]]** owns completeness; nothing here needs
  more than `CReal::lim`.
