---
title: A lemma by cases over an n-constructor recursive inductive costs about n² kernel steps
status: closed
labels: [kernel,elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-11-09
updated: 2026-11-10
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

## Log

- 2026-11-10: Fixed, two layers, both "keep the ih as what it came from" (docs/inductive-tier1-wf-lowering.md §6.4).

  Attribution. Each arm of `open_lc` got two copies of `open_at`'s whole step (the case tree over all n formers): (1) the unifier solved the congruence's implicits with the unfolded call's hypothesis read back as `λ i. elim_Wf(…; step; nth(cs; i))`, so the arm's elaborated term and every type read back from it carried the step; (2) the kernel applied the lemma's own ih at a neutral child through a λ built around a *shifted* copy of the step (`wf_ih_lam`), so the call through the ih and the call through `open_at`'s definition had different closures and conversion compared the two case trees structurally. The dependent motive mentioning a second recursion over the scrutinee is what makes both sides appear.

  Changes. Elaborator: `crates/elab/src/refold.rs` spells the ih of a fired step that is a defined global's body as calls of that global (`λ i. λ q̄. g(…, nth(cs; i), …, q̄)`), in `TermReducts` (the small-step walk) and in `Readback::wf_ih` (the value machine's readback, with a per-step verdict cache). Kernel: `Eval::wf_ih_child` evaluates only the `nth` and pushes the same `elim` frame; `wf_ih_lam` is gone.

  Counters, release, width one (`heather check --timings`), `open_lc` steps: n=10 6,862 / n=30 23,412 / n=90 79,306 / n=180 170,510 / n=360 362,465 (was 24,629 / 222,938 / 2,274,118 at 10/30/90). Gate and steps linear; elaboration about linear from 30 to 90, with one superlinear residue that dominates only past a few hundred formers: the unifier's head walk descends the case tree by substitution, filed as [[wide-inductive-unifier-case-descent]].

  Bench family `inductive/wide-lemma` (fixtures/intricate.rs): `lift` and `lift_id` over n formers with one congruence per arity, slope ~1.2 over 16..128 (band 0.88–1.58); the lemma alone was about quadratic. Regression test `a_wide_lemma_by_cases_is_linear_in_the_formers` (crates/elab/tests/annotation_cost.rs): gate steps 3,217 → 13,993 at 8 → 32 formers (was 9,385 → 122,953).
