---
title: omega under a binder that shadows an outer variable writes a certificate the kernel refuses
status: closed
labels: [omega,proofs,elaboration]
created: 2026-09-26
updated: 2026-09-28
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

## Log

- 2026-09-28: Omega now reconstructs and checks certificates in a context whose shadowed
  binders have fresh internal source names. The kernel context and de Bruijn
  indices stay unchanged, so outer facts remain usable and their variables
  cannot be confused with inner binders or later aliases.

  Regression coverage checks the original repro, goals that need an outer
  fact under Nat and Int shadowing, shadowed proof names, nested binders,
  collisions with generated names, and refusal when an outer bound is the
  only fact about an unrelated inner variable.
- 2026-09-28: Verified the new regression fails without the fix with the reported kernel
  `NotConvertible` rejection, and passes with it. Updated the subtype control
  that previously expected a shadowed proof binder to be discarded: Omega
  can now preserve that evidence under its internal name. Plain `scripts/test`
  passed: 3,033 passed, 0 failed, 5 ignored. `scripts/issue check` passed with
  one existing warning about an unrelated open issue's log.
