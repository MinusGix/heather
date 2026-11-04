---
title: omega in inference position says unbound name omega
status: closed
labels: [diagnostics,tactics,omega]
area: tactics
created: 2026-10-29
updated: 2026-10-30
---

`omega` (and `omega(h…)`) is a checking-position form. In inference
position it is not recognised at all, and the name falls through to an
ordinary lookup:

```
theorem letomega(a: Nat, h: a < 3): a < 4 { let k = omega(h); k }
```

says `unbound name omega`, which reads as a missing import. Probe on master
4f0ac27 ([[proof-patterns-audit-2026-10]]); first recorded in memory on
2026-10-19 (PR #67) as a rule to remember rather than a diagnostic to fix.

The collection literal already has the message wanted here: "a collection
literal needs an expected container type (it is checking-only, like
`refl`): annotate it (`let xs: List<T> = [a, b];`) or use it as an
argument".

## Acceptance

- `let k = omega(h);` and a bare `let k = omega;` say that `omega` needs an
  expected type and show the `let k: (T) = omega(…);` spelling. The same for
  `ring`, `linarith`, `nlinarith`, `bv_omega` if they share the gap.
- A pinned refusal in lib/_tests with `// expect-error:` naming that text.

## Resolution (2026-10-30)

The resolver's last stop (`resolve`'s unbound branch in
`crates/elab/src/lib.rs`, beside `rewrite` and `subst`) names `omega`,
`ring`, `linarith`, `nlinarith`, `bv_omega` and `positivity` as checking-only
forms with the `let k: (T) = omega(…);` spelling. It fires only where the
name is unbound, so a local or global of that name still wins. Pinned in
`lib/_tests/std/tactic/{omega,ring,linarith}_tests.hthr`.
