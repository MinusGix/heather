---
title: "Nat: half, Even/Odd — the wave-3 names that need two-step recursion"
status: blocked
labels: [stdlib,proofs,arithmetic]
blocked-by: [recursion-at-deeper-subterms]
created: 2026-08-17
updated: 2026-08-17
---

The rest of [[std-api-waves]] wave 3, minus the two names that needed nothing
new (`pow` and `fact` are [[nat-pow-and-fact]]). Stalled
deliberately rather than encoded around: see [[recursion-at-deeper-subterms]]
for the wall, the costed fix, and the workaround that was probed and rejected.

## The spellings, which are this issue's acceptance test

They are written out here so the feature round has something to check against
on its first day, and so the shape is not renegotiated later:

```
fn half(n: Nat) -> Nat {
    match n {
        Zero => 0,
        Succ(k) => match k { Zero => 0, Succ(l) => Succ(half(l)) },
    }
}

fn Even(n: Nat) -> Type {
    match n {
        Zero => True,
        Succ(k) => match k { Zero => False, Succ(l) => Even(l) },
    }
}

fn Odd(n: Nat) -> Type {
    match n {
        Zero => False,
        Succ(k) => match k { Zero => True, Succ(l) => Odd(l) },
    }
}
```

`Even`/`Odd` are **propositional and reducing**, like `Le`
(`docs/nat-order-design.md` §1): `Even(4)` unfolds to `True` so the proof is
`trivial`, and `¬ Even(7)` is the hypothesis itself. No `Bool` appears in the
statement of anything — the parity *decision* can come later as an `even_dec`
returning `Or<Even(n), ¬ Even(n)>`, mirroring `le_dec`, with a value-generic
`Decide<Even(n)>` instance the way the order has one.

## The kit that goes with them

- `half_le(n): half(n) <= n`, and `half_double(n): half(add(n, n)) = n`.
- `even_or_odd(n): Or<Even(n), Odd(n)>`, and that it is exclusive:
  `not_even_and_odd(n): ¬ And<Even(n), Odd(n)>`.
- The two that tie parity to the arithmetic: `even_double(n): Even(add(n, n))`,
  and `half_add_half(n, h: Even(n)): add(half(n), half(n)) = n` — the reason
  `half` and `Even` belong in one issue rather than two.
- `even_dec`, then `instance(n: Nat) Decide<Even(n)>` (the order's spelling,
  [[value-generic-instances]]).

## The alternative that needs no feature, and why it is not taken

`Even(n) := ∃k, add(k, k) = n` is the mathematical definition and checks
today. It is not the definition here because it does not **reduce** — `Even(4)`
stops being `trivial`, which is the property every recursion in
`lib/std/nat.hthr` is written to keep. Once the reducing definition exists,
this statement is a *lemma* about it, which is the right relationship between
the two; taking it as the definition now would mean two `Even`s and a bridge
later.

## What it assumes from elsewhere

- **[[recursion-at-deeper-subterms]]** owns the language gap. Assumed here:
  only that the spellings above are what it will make checkable.
- **[[std-api-waves]]** owns sequencing. Assumed here: nothing.

## Acceptance

The three definitions above check as written, `half(7) = 3` is `refl`,
`Even(4)` is `trivial`, and the kit lemmas are proved with the four axes of
`docs/testing-generated-terms.md` covered as in
`crates/elab/tests/nat_arith.rs`.
