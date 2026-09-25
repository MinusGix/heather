---
title: A Nat division kit, so digit and place-value proofs stop paying omega
status: open
labels: [stdlib,arithmetic,proofs,performance]
created: 2026-09-25
updated: 2026-09-25
---

`lib/std/nat.hthr` has five facts about Nat division: `divmod_spec`,
`div_mul_add_mod`, `mod_lt`, `div_zero` and `mod_zero`. Every other fact about
`/` and `%` goes to `omega`, and in `lib/decimal_line.hthr` (the certified
`wc -l` formatter) that is where the time goes. Its four digit lemmas and four
`*_arith` group lemmas lead the module's check. Each is a one-line textbook
fact that `omega` proves in seconds by expanding every `div`/`mod` atom into a
quotient and remainder with bounds ([[omega-div-mod-goal-cost]]).

When the round replaced the `*_arith` lemmas' division laws with
`div_mul_add_mod` and `mod_lt` calls (`step_parts`, `step_rem`), a third of
their cost went away. The rest needs lemmas that do not exist yet.

## Scope

A Nat division kit in `lib/std/nat.hthr`, proved once, structurally or from
`divmod_spec`:

- uniqueness: `n = q*d + r` and `r < d` give `n / d = q` and `n % d = r`, the
  lemma most of the rest follow from;
- small cases: `div_one`, `mod_one`, `div_of_lt`, `mod_of_lt`, `div_self`;
- nesting: `div_div` (`n / a / b = n / (a*b)`), `mod_mod_of_dvd`
  (`n % (a*b) % a = n % a`), `div_mod_eq_mod_div`
  (`n / a % b = n % (a*b) / a`);
- shifting: `add_mul_div`, `add_mul_mod`, `mul_div_cancel`, `mod_add_mod`;
- order: `div_le_self`, `mod_le`, `div_mul_le`, `div_lt_iff_lt_mul`,
  `div_le_div` (monotone in the dividend).

Names follow the library's existing `Nat::` conventions. Choose the set by
what the customer below uses, not by symmetry. Anything nothing uses can wait.

## Acceptance

- `decimal_line`'s `thousands_digit`/`hundreds_digit`/`tens_digit`/
  `units_digit` and the `*_arith` step facts close without `omega`, or with
  `omega` only on bounds that have no `div`/`mod` atom. Their item times drop
  and are recorded through `scripts/perf ab --source-patch`.
- The stale comment above `digits_agree` goes. It says `omega`'s certificate
  for a division of a division is refused, but the padding fix in
  [[omega-respells-atoms-without-implicits]]'s log made that pass.
  `n / 10 / 10 = n / 100` now closes by `omega` (probe 2026-09-25). So the
  over-variables detour (`a`, `b` for `n/10`, `n/100`) can go too.
- Each lemma is stated over open Nat, never at literals, so later customers
  (itoa at other widths, hex, fixed-point) reuse it.

## What it assumes from elsewhere

- **[[certifying-arithmetic-proof-automation]]** owns automation. This issue
  is the lemma kit that automation, or a person, cites. Assumed there: only
  that a named lemma is cheaper for the kernel than a re-derived one.
