---
title: A decreases measure over a record field at a constructed record is unspelled and omega cannot read it
status: closed
labels: [omega,proofs,elaboration]
area: tactics
created: 2026-10-31
updated: 2026-10-31
---

A `decreases` measure over a record field, at a recursive call whose
argument is a constructed record, raises an obligation that is displayed
unspelled and that `omega` cannot read. Found by the sequencing design's
probe P4 (`docs/sequencing-surface-design.md`, appendix). On `3099a7d`:

```heather
record CdState { m: Nat, out: List<Nat> }
fn cd_loop(s: CdState) → CdState decreases s.m {
    match h: Nat::leb(s.m, 0) {
        True => s,
        False => cd_loop(CdState(s.m - 1, Cons(s.m, s.out))),
    }
    on ?dec1 := { let nle: ¬(s.m <= 0) = s.m.not_le_of_leb(0, h); omega(nle) };
}
```

The unsolved-goal display shows `?dec1 : Le(Succ(fst@(snd@(pair@(El[0](…`,
and `omega(nle)` fails with "Omega could not spell a natural expression".
The same loop with the state as two parameters (`cd_loop(m: Nat, out:
List<Nat>) decreases m`) checks.

The design sidesteps it: a lowered `while` takes its state as separate
parameters (§5.3). Hand-written `decreases` functions over records still
hit it. The measure at the call should be spelled as the written field of
the written constructor (`CdState(…).m`), or reduced to the field's value
(`s.m - 1`) before it is stated, as `issues/omega-measure-at-constructor-pattern.md`
did for a measure applied to a constructor pattern.

## Done when

The repro checks with `omega` as the default closer and no `on`.

## Log

- 2026-10-31: CLOSED. Three gaps, not one (docs/omega-measure-reduction-design.md §18): the read `fst(snd(pair(…)))` off a constructed record had no spelling (the speller's weak head overshot into `sub`'s eliminator; now projected by syntax, `CdState(sub(s.m, 1), …).m` for display and the field's value for source), `omega` reflected it as an unspellable atom (same overshoot; `field_as_put` takes the syntactic component), and the arm's `h: leb(s.m, 0) = False` was never a fact `omega` read — the two-parameter control failed without `on` too. Bool equations are now guards (`omega::guard_eq_true`/`guard_eq_false`), and the lifted obligation quantifies an arm equation at `True`/`False`. The repro checks with no `on`; probes in `lib/_tests/std/tactic/omega_tests.hthr`.
