---
title: Nat's arithmetic tail: min/max, the sub kit, and the order-interaction lemmas
status: closed
labels: [stdlib,proofs,arithmetic]
created: 2026-08-17
updated: 2026-08-17
---

The half of [[nat-order-kit]]'s round that was deferred by charter rather than
by any obstacle, given an owner of its own so that the order issue can close.

`lib/std/num/nat.hthr` states the order in full and proves its kit. What it does
not have is the *arithmetic* that reads the order:

- **`min`/`max` at `Nat`** — plain structural recursions, no decider needed.
  (`std/algebra`'s `max_of` is a different thing: a `Cmp`-generic pick.)
- **The `sub` kit beyond `sub_zero`** — `add_sub_cancel`, `sub_add_cancel`
  under `n <= m`, `sub_self`, `sub_le`. `sub` and `sub_zero` are there;
  `le_add` already does the one `sub` fact the order needed and does it inline.
- **The order-interaction lemmas** — `add_le_mono`, `mul_le_mono`,
  `le_of_add_le_add_l`, and cancellation.

## Why it is separate rather than a line in the order issue

Two issues each named the other as the owner: [[std-api-waves]]'s wave-1 row
said the `sub` kit and `min`/`max` were deferred to [[nat-order-kit]], and
[[nat-order-kit]]'s "what is left" said wave 3 was the other half of the same
list. Circular ownership is how work becomes unfindable (README rule 1), and it
kept the order issue open long after its own scope had landed in full (rule 3).
This issue is the answer to "who owns it": here.

## What it assumes from elsewhere

- **[[nat-order-kit]]** owns the order. Assumed here: only that `Le`, `Lt` and
  their kit exist and are stated propositionally, which is what makes
  `sub_add_cancel` statable under a hypothesis `n <= m` at all.
- **[[std-api-waves]]** owns sequencing. Assumed here: nothing — this is a
  wave-3 item whenever wave 3 runs.

## Acceptance

The names above exist in `lib/std/num/nat.hthr` with proofs, and `min`/`max`
**reduce** at closed arguments (`max(2, 5)` is `refl`-provably `5`), which is
the property every recursion in that file is written to keep.

## Log

- 2026-08-17: LANDED, in one pass and with nothing refuted. `lib/std/num/nat.hthr` gained three
sections at the end, all after the order kit because all of them read it:

- **the `sub` kit** — `sub_self`, `add_sub_cancel`, `sub_add_cancel`,
  `sub_le`. The two cancellations are asymmetric and truncation is why:
  `(n + m) - m = n` is unconditional and each arm is the bare recursive call
  (`add(n, Succ k)` reduces to `Succ(add(n, k))` and `sub(Succ x)(Succ y)` to
  `sub(x)(y)`, so there is nothing between the arms), while `(m - n) + n = m`
  needs `n <= m` and turned out to be `le_add` commuted rather than a second
  induction — a one-line `trans(add_comm(…), le_add(n)(m, h))`.
- **monotonicity and cancellation** — `add_le_mono_r`/`_l`/`add_le_mono`,
  `le_of_add_le_add_r`/`_l`, `mul_le_mono_r`/`_l`/`mul_le_mono`. Every one of
  the `_r` halves inducts on the operand being *added on* rather than on either
  compared value, and that is the whole economy: a step of the induction is a
  step of `add` and a step of `Le` cancelling, so the arm is the IH applied
  unchanged. Monotonicity and cancellation are therefore literally the same
  recursion with the implication turned round. The `_l` halves are the `_r`
  halves transported through commutativity with `j` — `add` descends on its
  second argument, so a left-hand induction would pay
  `add_left_zero`/`add_succ_left` at every step to reach a shape the `_r` proof
  already has. `mul_le_mono_r` is the only body that *uses* the section above
  it: `mul(n, Succ j)` is `add(mul(n, j), n)`, so its step compares two sums and
  is exactly `add_le_mono` of the IH and the hypothesis.
- **`min`/`max`** — plain structural recursions mentioning no decider, which is
  the prediction `docs/library/nat-order-design.md` §6 made and it held exactly. Both
  descend on both arguments and so are curried for `Le`'s and `sub`'s reason
  ([[ih-generalization]]); both reduce, so `max(2, 5) = 5` is `refl`. Beyond the
  four bounds, the kit got the two *universal* properties (`max_le`, `le_min`)
  and the two order-decided equations (`max_eq_r`, `min_eq_l`) — the bounds
  alone are half a lattice and a caller who has a comparison in hand wants the
  other half.

**Not here, and each for a stated reason.** `mul` cancellation is false at
`k = 0` and wants a `0 < k` hypothesis — a different lemma, not this one's
mirror, and the file says so where a reader would look for it. No bridge lemma
between `Nat`'s `min`/`max` and `std/algebra`'s `Cmp`-generic `max_of`: they are
different things, and `algebra` imports `nat`, so such a lemma cannot be stated
in this file at all. The rest of wave 3 (`pow`, `half`/`even`/`odd`, `fact`) was
never this issue's scope and stays unowned.

**Tests**: `crates/elab/tests/nat_arith.rs`, 12 tests over the four axes of
`docs/testing-generated-terms.md`, five of them negative controls. Two earn
their place beyond the usual: the **asymmetry** control (`max(0, n)` reduces at
open `n`, `max(n, 0)` is refused — the currying is a claim about which argument
moves, and the fact it is stuck on is *true*, just not definitional), and the
**round trip** (monotonicity composed with cancellation at open arguments in
both orders, which is what would catch a pair of lemmas each individually
provable but stated about different sides). `clamp` is the checking-position
axis: `max(lo, min(hi, x))` as a `fn`, with both a bound proof about the
composite and closed values above, inside and below the band.

**One thing the probing found and did not fix**: a diagnostic whose expected
type is `Le(n, m)` at open arguments prints the raw `El(app(app(u55…)))` code,
because the display reader added by [[goal-display-decodes]] unfolds until the
`El` wrapper disappears and at open arguments it never does. Filed as
[[le-diagnostics-print-raw-el]]; it is the residue `docs/library/nat-order-design.md`
§6 predicted, now that every propositional relation in the library is a
`fn … -> Type`.
