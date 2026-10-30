---
title: A match refines an earlier hypothesis in the elaborator but not in the kernel term
status: closed
labels: [frontend,elaboration,motives,bug]
area: language
created: 2026-10-10
updated: 2026-10-30
---

The elaborator treats a hypothesis bound *before* a `match` as refined by the
arm's constructor, but the term it emits does not generalize that hypothesis
in the motive, so the kernel rejects what the elaborator accepted (all three probes on master `25b3d8b`):

```heather
import logic;
import nat;

fn Is(n: Nat) → Type { n = 0 }

theorem probe(n: Nat, h: ¬Is(n)): Nat {
    match n {
        Zero => false_elim(h(refl)),
        Succ(k) => k,
    }
}
```

```text
error: the kernel rejected `probe`: NotConvertible. `refl` needs both sides to
be definitionally equal, but `n` and `0` are not
```

The defined head is not needed: `h: ¬(n = 0)` and `h: n = 0 → False` fail
the same way. What differs is where the check happens. Checking `refl`
against `h`'s domain `n = 0` succeeds in the elaborator, presumably because
its conversion uses the arm's `n ≡ Zero`. A hypothesis used *as* the arm's
result is refused correctly (`h: n = 0`, arm `Succ(k) => sym(h)` against the
goal `0 = Succ(k)`: "this has type `0 = n`, but `0 = Succ(k)` is expected").
That reading is inferred from these three probes, not from the code. Found in
`Rat::mul_inv_parts` (2026-10-10), where the hypothesis was
`¬(Rat(a, d) ≈ Rat::zero())`.

Either outcome is fine, but they must agree: generalize the hypotheses that
mention a variable scrutinee into the motive (what the elaborator already
believes), or refuse at the arm. Generalizing is the useful one; the
workaround is to move the hypothesis after the match (`→` in the statement,
`λ h =>` in each arm).

## What it assumes from elsewhere

- **[[goal-motive-by-scrutinee-abstraction]]** owns motive synthesis for the
  goal. Assumed here: only that hypotheses are not part of it today.

## Log

- 2026-10-30: Customer count (2026-10-30, interval elegance round): the workaround's other spelling, the convoy by application `match I as λ K => K.Has(x) → … { Bnd(…) => λ k => …, Whole => λ _ => trivial }(h)`, is 11 sites in lib/std/num/float/interval.hthr and 13 in creal_interval.hthr (every `*_has` lift from boxes to intervals, and `lt_of_below`). Generalizing the hypotheses that mention a variable scrutinee would turn each into a motive-less `match I { Bnd(…) => …, Whole => trivial }` over the refined hypothesis. The library rewrite kept them; this issue is where they go.
- 2026-10-30: Fixed by generalizing. The elaborator never believed the refinement: `refl` is not checked by the elaborator at all (it notes the endpoints for the gate and emits `Refl`), so the kernel was the first judge, and the motive left `h` about `n`. Now a motive-less `match` on a local in checking position generalizes every later binder whose type mentions the scrutinee, closed under dependency, through the ih-generalization path (`Elaborator::refined_hypotheses` in `generalize.rs`; Π goal, arms wrapped in `λ h =>` under the hypotheses' own names, recursor applied back). Not done for a recursion's own `match` with self-calls in its arms (a self-call cannot pass a non-parameter local) nor in inference position; `docs/ih-generalization-design.md` §5. A pattern variable named like a refined hypothesis still shadows it (the wrapped binder is renamed `#h` in that arm). The convoys went: 7 in `interval.hthr`, 9 in `creal_interval.hthr` (the issue's 11/13 counted the inner `match J` convoys separately); the two left are on computed scrutinees (`Interval::of_rat(…)`, `Dyadic::lt_bool(0, lo)`), which are not locals. Acceptance: `crates/elab/tests/match_refines_hypotheses.rs`.
