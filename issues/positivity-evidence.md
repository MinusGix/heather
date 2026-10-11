---
title: Replace the shifted Pos with Pos<A> binder sugar over a smarter infer
status: open
labels: [stdlib,elaboration,traits,design,ergonomics]
created: 2026-10-10
updated: 2026-10-11
---

Decide whether `lib/std/pos.hthr`'s shifted `Pos { pred }` stays, and how
positivity is spelled and discharged. The options, the probes of what
`:= infer` does today, and a costed recommendation are in
`docs/positivity-evidence-design.md`.

The recommendation: grow `:= infer` at proposition goals (computation to
`True`, then registered evidence rules keyed by the positive term's head),
make `Pos<A>` binder sugar for `x: A, x_pos: 0 < x := infer` rather than a
type, migrate `Rat`, and delete the shifted representation. A real
refinement type for function domains and containers waits for
[[regular-cauchy-reals]].

## Decided (2026-10-10, design note §7)

Sugar over search, spelled `n: Pos<Nat>`; no `Fact`-style class; parameter
defaults such as `h: 0 < n := omega` should parse; a positivity tactic
eventually; result facts named under the function (`ten_pow::pos`), which
needs function-owned members.

Rules live in `infer` (Minus) and are spelled `evidence theorem` (round 1).
Open: `∧` projections in `infer`. The rounds are
listed in the note's §8; this issue closes when they are filed.

## What it assumes from elsewhere

- **[[implicit-logical-assumptions]]** owns `infer`'s precedence across
  `assuming`/`using` scopes. Assumed here: new sources slot after locals and
  derivations and do not reorder them.
- **[[field-defaults-under-locals]]** owns stored-goal defaults. Assumed
  here: parameter defaults, if ever wanted for positivity, share it.
- **[[subtype-transfer-and-evidence]]** owns evidence policies for real
  subtypes, which the deferred refinement type would use.
- **[[positive-naturals-and-rationals]]** landed the current `Pos`.

## Log

- 2026-10-10: Filed with the design note, from Minus's question whether
  `Pos` should exist at all.
- 2026-10-10: Minus chose sugar over search, spelled `n: Pos<Nat>`, no `Fact`, `h := omega` parameter defaults, and function-owned result facts (`ten_pow::pos`). Note §7–§8 updated; title changed to match.
- 2026-10-10: Rounds filed: [[infer-proposition-evidence]], [[named-arguments]] (parameter defaults), [[function-owned-members]], [[pos-binder-sugar]], [[retire-shifted-pos]], [[positivity-tactic]], [[positive-refinement-type]].
- 2026-10-10: Round 1 implemented ([[infer-proposition-evidence]]): Minus chose rules in `infer`; hand-written rules are spelled `evidence theorem`.
- 2026-10-11: Round 3 landed: [[function-owned-members]] (`theorem f::name`).
