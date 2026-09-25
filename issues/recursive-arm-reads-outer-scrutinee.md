---
title: A recursive arm that names its scrutinee computes with the outermost value
status: open
labels: [elaboration,correctness,recursion]
created: 2026-09-25
updated: 2026-09-25
---

A structurally recursive `fn` that names its scrutinized parameter inside the
`Succ` arm computes a **wrong answer**. The program is well typed, and the
kernel accepts the wrong equation by `refl`:

```text
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
fn sum(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => add(sum(k), n) } }
theorem wrong(): sum(2) = 4 { refl }   // accepted; the source means 3
```

Writing `Succ(k)` instead of `n` in the arm gives 3. The likely reading is
that the arm is the `elim_Nat` step, and `n` inside it is still the outer
λ's parameter. The step runs once per level, and at every level `n` is the
top-level argument, not that level's `Succ(k)`. Nothing refines the
scrutinee variable to the constructor inside its own arm for the *value*
(only the motive is refined). Found 2026-09-25 while testing `have`
([[proof-let-substitution-cost]]'s follow-up, docs/have-design.md); it is
independent of `let` and `have`.

## Acceptance

- `sum(2) = 3` by `refl`, and `sum(2) = 4` is refused. Test at a literal
  argument (it must compute) and at a neutral one.
- The fix either substitutes the arm's constructor for the scrutinee in the
  arm body, or refuses the mention by name. It does not silently keep the
  outer value.
- Sweep: whether `lib/` or the showcase has a recursive arm that mentions its
  own scrutinee (a wrong computation that no `refl` pinned).

## What it assumes from elsewhere

- **[[ih-generalization]]** owns motive generalization. Assumed here: only
  that it never rebinds the scrutinee in the arm *body*.
