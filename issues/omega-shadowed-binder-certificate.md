---
title: omega under a binder that shadows an outer variable writes a certificate the kernel refuses
status: open
labels: [omega,proofs,elaboration]
created: 2026-09-26
updated: 2026-09-26
---

`omega` inside a `λ` whose binder shadows an outer variable writes a
certificate the elaborator accepts and the kernel refuses:

```text
theorem shadow(n: Nat, small: n < 5): n < 10 {
    let g: ((n: Nat) → n < 5 → n < 10) = λ n s => omega;
    g(n, small)
}
error: the kernel rejected `shadow`: NotConvertible. this has type `Lt(n, 5)`
where a type that displays the same is expected
```

The same shape closed by a lemma instead of `omega` checks. The likely cause:
omega reflects the outer `small: n < 5` and spells it by name, and inside the
`λ` the name `n` means the inner binder. The certificate is then about the
wrong variable. The elaborator accepts it, so this is an elaborator/kernel
disagreement and not only a refusal.

Found 2026-09-26 while probing [[bitvec-nat-lifting-tactic]]. `bv_omega` avoids
it by binding only `__bv_`-prefixed names and fact names it rebinds on
purpose.

## Acceptance

- The repro checks, or omega leaves out a fact it cannot spell faithfully.
- A control where the shadowed fact is needed still proves the goal.
