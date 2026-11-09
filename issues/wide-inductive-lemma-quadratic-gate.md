---
title: A lemma by cases over an n-constructor recursive inductive costs about n² kernel steps
status: open
labels: [kernel,elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-11-09
updated: 2026-11-09
---

A lemma by structural recursion over a recursive inductive with `n`
constructors costs the gate about `n²` kernel steps, though the definitions
it is about stay linear. Measured for the heather-coq port assessment (PR
#158, whose §4.4 asks for the measurement before a 90-constructor syntax is
built on).

The family is `lib/kernel_model/kernel_reduction.hthr` scaled up: `Tm` with
`Bv`, `Fv` and `n` formers of arity 0 to 3, a few of them binding a
variable; `Tm::open_at` and `Tm::Lc` with one arm per constructor; a
congruence lemma per former; and

```heather
theorem Tm::open_lc(self t: Tm): (d, k: Nat) → t.Lc(d) → d <= k → (u: Tm) → t.open_at(k, u) = t
```

with one arm per constructor, each a congruence applied to recursive calls.
`heather check --timings`, release, master `8a593b6`, counters only (they
are exact):

| n | `open_lc` steps | conversion queries | misses | `open_at` steps |
|---|---|---|---|---|
| 10 | 24,629 | | | 979 |
| 30 | 222,938 | 50,108 | 8,479 | 3,302 |
| 90 | 2,274,118 | 422,546 | 89,700 | 11,770 |

Tripling `n` multiplies the lemma's steps by nine to ten and its queries by
about eight, so each arm pays work linear in the number of *other*
constructors. `open_at`, a definition with the same arms, is linear. The
declaration itself is flat. About half the lemma's wall time is outside the
gate, so elaboration has a share of its own.

`docs/mutual-inductive-design.md` §6 (Cost) describes a Θ(m²) term for a
group's step (each case node carries a convoy motive that spells the arity
tree) and the typing memo that keeps the gate from paying it per node. This
family is a single unindexed inductive, and the residue shows in a
*dependent* motive that mentions two eliminations of the scrutinee
(`t.Lc(d)` and `t.open_at(k, u)`); I did not attribute it further.

The same lemma over a generic syntax (`Tm<O>` with operators as a parameter
and arguments as a list, five arms whatever the signature) costs 9,240
steps at every `n` (the probe `heather-model/generic_syntax_probe.hthr` in the
project files, with the generator `gen_wide_syntax.py` beside it).
That is a way round for syntaxes, not a fix: an ISA-sized instruction type
with lemmas by cases has the same shape.

## Acceptance

`open_lc`'s gate steps and elaboration time grow about linearly from 30 to
90 formers, or the quadratic term is attributed and recorded as inherent.
A bench family beside `inductive/isa-roundtrip`
([[intricate-inductive-bench-families]]) holds the exponent.

Related, from the same probe: [[mutual-family-member-declarations]] and
[[mutual-group-type-valued-members]]. Earlier rounds on this cost family:
[[mutual-group-recursion-gate-cost]], [[wide-inductive-constructor-mention-cost]].
