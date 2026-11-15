---
title: `if h:` and `match g: decide_bit<…>` in a theorem whose goal mentions a measured mut self fn give arms the kernel refuses
status: open
labels: [elaborator, proofs]
area: tactics
created: 2026-11-15
updated: 2026-11-15
---

In the sort example (`examples/sort/sort.hthr`), the outer loop's invariant
`sort_from_sorts` was first written as a `decreases (n - i).toNat()` theorem
that branched with `if h: i < n { … } else { … }` (and, in a second attempt,
`match g: decide_bit<i < n>() { … }`) on a goal mentioning
`List::sort_from(s, n, i).after`. The elaborator accepted the arms, and the
kernel refused them (NotConvertible; the diagnostic printed "no surface
spelling" for the motive). The same branch on a goal over the
non-`mut self` `lower_bound_in` (`examples/binary-search/search.hthr`,
`lower_bound_in_splits`) is accepted.

The example works around it: structural induction on a `Nat` `left` with
`(n - i).toNat() = left`, a case on `i.toNat().lt_or_ge(n.toNat())`, and the
step as a lemma (`sort_from_step`) taking the induction hypothesis as a
function. That is longer than the binary search's proof for no reason a
reader can see. The suspicion is that the motive abstracts the proposition
inside the `Mutated` projection `.after` of a measured `mut self` call, whose
unfolding then differs between the arm and the goal.

To retire: reproduce in `lib/_tests` with a two-line measured `mut self`
fn, find whether the motive or the kernel's check is wrong, and rewrite
`sort_from_sorts` as the direct `decreases` proof.

Probably the same defect as [[match-arm-accepted-against-unspecialised-goal]]:
the elaborator accepts an arm the kernel then refuses, with the same "no
surface spelling" diagnostic. Here the scrutinee is a word comparison and the
goal is stuck on a measured call's `.after`.
