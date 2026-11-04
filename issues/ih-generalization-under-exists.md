---
title: Induction-hypothesis generalization misses a self-call under ∃
status: open
labels: [elaborator, recursion]
area: language
created: 2026-11-01
updated: 2026-11-01
---

A `Type`-valued `fn` whose self-call varies a parameter inside an `∃` is
refused with "recursive call to `RecSum` must pass `a` unchanged", although
`docs/ih-generalization-design.md` generalizes varied parameters:

```heather
fn List::RecSum({F: Format}, self xs: List<Finite(F)>, mode: Mode, a, s: Finite(F)) → Type {
    match xs {
        Nil => a = s,
        Cons(y, t) => ∃ r: Finite(F), a.add(y, mode := mode) = Float::Fin(r) ∧ t.RecSum(mode, r, s),
    }
}
```

`lib/std/num/float/summation.hthr` curries it by hand (`List::RecSum_of`
returns `Finite(F) → Finite(F) → Type`, with `RecSum` a wrapper).

## Notes

Not investigated: the refusal may come from the scan not seeing the call
inside the `∃`'s lambda (`Elaborator::varying_params` reads surface arms),
or from the goal `Type` not counting as a known result type. A fix
removes `RecSum_of`.
