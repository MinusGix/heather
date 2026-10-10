---
title: A match refines an earlier hypothesis in the elaborator but not in the kernel term
status: open
labels: [frontend,elaboration,motives,bug]
created: 2026-10-10
updated: 2026-10-10
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
