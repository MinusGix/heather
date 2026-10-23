---
title: A Nat division kit, so digit and place-value proofs stop paying omega
status: closed
labels: [stdlib,arithmetic,proofs,performance]
created: 2026-09-25
updated: 2026-09-25
---

`lib/std/num/nat.hthr` has five facts about Nat division: `divmod_spec`,
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

A Nat division kit in `lib/std/num/nat.hthr`, proved once, structurally or from
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

## Log

- 2026-09-25: Landed. The kit is in `lib/std/num/nat.hthr` after `scaled_le`, proved structurally in milliseconds per lemma. Its core is `div_mod_unique` (a larger or smaller quotient puts `n` strictly on one side of itself, by `scaled_lt`) and `div_mul_parts` (dividing by `a` then `b`, as one decomposition). `div_div`, `mod_mul_mod`, `div_mod_eq_mod_div` and `div_split` (place value: `n / c = n / (c*k) * k + n % (c*k) / c`) are each that pair read once. Also `div_of_lt`, `mod_of_lt`, `div_one`, `mod_one`, `div_lt_of_lt_mul`, `le_div_of_mul_le`, `add_mul_distr` and `add_left_cancel`. Deviations from Scope, each chosen by the customer: `mod_mod_of_dvd` is `mod_mul_mod`, because the statement has no divisibility premise. `div_lt_iff_lt_mul` is the two directions that are used, as two lemmas. The nesting laws take `0 < a` and `0 < b` (true unconditionally, but the zero cases would cost case splits no customer needs). Not built because nothing uses them yet: `div_self`, `add_mul_div`, `add_mul_mod`, `mul_div_cancel`, `mod_add_mod`, `div_le_self`, `mod_le`, `div_mul_le`, `div_le_div`.

  `decimal_line`: the four digit lemmas are kit calls over `n` alone. The `a`/`b` detour and its stale comment are gone. The four `*_arith` records are one generic `group_facts(r, h, c, w)` over open place value and byte weight, with the literal group lemmas supplying only bounds. The low/fits bounds, the `rest` chain and the `sum` identity (`div_split` three times, then `weigh`) are by the order kit, with no `omega`. `line_prereqs`, `digit_bounds`, `decimal_two/three/four`'s quotient bounds and the `line_*` cases' digit identities moved to the kit too, and `low_part` is by hand. What `omega` still proves in the module has no `div`/`mod` atom. `scripts/perf ab --source-patch` over `decimal_line` (fixed binary, width one, three interleaved cold samples): wall 107/98/106 s → 28/38/33 s (−69%, samples separate), kernel gate −62.5%, max RSS 650 → 373 MB. Counters: `conv_misses` 1.22M → 0.40M, `eval_steps` 20.9M → 7.7M. Per item at width eight (`scripts/timings --diff`): `*_arith` 9–11 s → 15 ms, digit lemmas 4–9 s → 1 ms, `line_prereqs` 6.3 s → 34 ms, `group_facts` 0.1 s. Counts of untouched items did not move. In the full suite `wc_l_prints_what_the_read_returned` went 283 s → 170 s ([[native-print-test-cpu-margin]]).

  Found on the way: a first `step_fits` spelled `rest * 2^40` with `rest` open, which unfolds `mul` once per unit of the literal. At width eight it aborted the checker with a worker stack overflow instead of `OutOfFuel`, filed as [[kernel-worker-stack-below-depth-budget]]. Landed spellings keep big literals on the left of `*`.
