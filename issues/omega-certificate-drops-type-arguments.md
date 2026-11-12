---
title: omega's certificate re-spells a hypothesis without its type arguments and fails to elaborate
status: closed
labels: [tactics,omega,certificates,diagnostics]
area: tactics
milestone: [tac-arith]
created: 2026-11-12
updated: 2026-11-12
---

```heather
theorem nil_typed(n: Nat, h: n + List::Nil<Nat>.len() = 3): n <= 3 { omega }
```

```
error: cannot infer the type argument `A` of `List` here — no argument of `Nil` determines it. …
  generated Omega certificate: { let __omega_exact_0 = omega::normalized_eq_value(int::OfNat(nat::Nat::add(n, list::List::len(Nil))), …
```

The hypothesis is well typed as written. The certificate `omega` generates re-spells it as surface text, `list::List::len(Nil)`, and the spelling has lost the type argument, so the certificate does not elaborate. The user sees a "cannot infer" error at their own `omega`, about a term they did not write.

It comes up whenever a hypothesis in scope mentions a constructor with no arguments at a parameterised type: `Nil.len()`, `None`, an empty map. In `lib/lang/lexer/lexer_span.hthr` the base case of `scan_from_longest` has `i.toNat() + Nil.len() = length.toNat()` in scope after the `match rest`, and the bound is proved by `j` there because `omega` cannot be called.

## What would fix it

The certificate's atoms are terms the tactic was handed; they should go back as terms (quoted, not printed), or the printer should write the type arguments a constructor's own arguments do not determine. The first is the general fix and is what [[host-elaboration-interface]] is for; the second is small and would do for this.

## Done when

The theorem above checks, and the `j` in `scan_from_longest`'s `Nil` case is `omega`.

## Log

- 2026-11-12: Fixed on master by PR #580 (the certificate keeps a constructor's type arguments). The last item, on PR #551 after merging master: the `j` in `scan_from_longest`'s `Nil` case is `omega` (`let past: length.toNat() <= i.toNat() = omega;`), and the module checks.
