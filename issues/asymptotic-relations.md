---
title: Approaches and Landau relations with their witnesses as data
status: open
labels: [stdlib,mathematics,analysis,reals,design]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-11-08
---

Layer C of `docs/analysis-foundations-design.md` (§6): countable nested
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

The carrier of the Landau relations is **germs modulo eventual agreement**,
not functions modulo pointwise `≈`. `f ≼ 0` only says that `f` is eventually
zero, so the dominance axiom `f ≼ 0 → f ≈ 0` (`valued-rings-and-newton`)
needs the germ setoid. The germ setoid is also the semantics of an
Ω-calculus surface (design note §3.6), if one is ever wanted.

Acceptance: probes at sequences `Nat → Rat` (e.g. `1/(n+1) = o(1)`,
`n = O(n²)`, a composed `o` through the closure lemmas), and the `CReal`
bridge theorems.

## What it assumes from elsewhere
- **[[real-completeness-interfaces]]** owns completeness; nothing here needs
  more than `CReal::lim`.

## Log

- 2026-11-08: Stdlib awkwardness survey (docs/stdlib-math-awkwardness-survey.md §8): demand for the `Eventually` slice, counted 2026-11-08: `OrderedField::half`/`half_pos`/`half_add` 135 uses, `below_both`/`shrink` 34, and `le_max_*` threshold plumbing 75 in analysis and creal. Pulling `Eventually` with its `and`/`mono` lemmas ahead of the Landau relations would serve sequence.hthr and real_fn_limit.hthr now; [[omega-reads-min-max]] removes the threshold half by itself.
