---
title: An implicit parameter a structural self-call would infer anew is refused only by the kernel
status: closed
labels: [elaboration,recursion,diagnostics]
area: language
created: 2026-11-02
updated: 2026-11-02
---

A structurally recursive `fn` whose self-call varies a parameter `x` and
omits an *earlier* implicit parameter whose value the call determines:

```
fn g(n: Nat, x: Nat, {e: Nat}, h: e = x) -> Nat {
    let y = e;
    match n { Zero => y, Succ(k) => g(k, x + 10, refl) }
}
```

At the call `e` is passed unchanged (it is implicit and not written), while
`h` needs `e = x + 10`. The elaborator accepts `refl` there and the error
the user sees is the kernel's: `the kernel rejected g: NotConvertible ...
e and add(x, 10) are not`, i.e. an unrecorded kernel refusal
([[unrecorded-kernel-refusals]]), at a program that is well-typed under the
ordinary reading (the call infers `e := x + 10`).

`generalize::varying_params` closes the varied set forward only (later
parameters whose types mention a varied one), so `e` is never generalized;
`recursion::elab_self_call` then checks `refl` against a domain mentioning
the outer `e`. Two ways out:

- refuse at the call, located, with the spelling that works:
  `@g(k, x + 10, x + 10, refl)` (which generalizes `e`, and a `let` bound
  from it then takes the measure route,
  [[recursion-let-reads-changing-parameter]]);
- or generalize an omitted implicit whose value the varied arguments
  determine (needs the call's unification, not the surface scan).

Also find out why `refl` at `e = x + 10` passed the elaborator against the
ih's domain (likely the same class as
`cat-handoff/elab-accepts-mismatch-under-redex-head.md` in the project files).

Acceptance: `g` is either refused at the call with the `@` spelling, or
computes `g(1, 0, refl) = 10`; a probe in `crates/elab/tests/recursion_meaning.rs`.

## Resolution (2026-11-02)

Generalized (Minus's call). `generalize::varying_params`' dependency closure
now runs to a fixpoint both ways: forward as before, and **backward for a
value implicit**: an earlier `{q}` (not an index the scrutinee's type
mentions) that a generalized parameter's type mentions is generalized too.
`recursion::elab_self_call` then applies the ih through the ordinary
implicit-inserting engine (`SelfCallElab::apply_self_call_implicit` →
`application::apply_implicit`), so an omitted generalized implicit is
inferred from the varied arguments after it. One with no varied argument
after it keeps the old refusal ("pass it explicitly (`@f(…)`)").

`recursion::plan` mirrors the closure by name over the written parameter
types, so a `let` bound above the `match` from such an implicit is stale like
any varied value: it takes the measure route, which passes every parameter
and so refuses the call without `@`; that refusal now says why the
declaration is under a `decreases` and names the structural spelling.

The mismatched `refl` was not a recursion gap: any `refl` checked at a
non-equation (`fn k(e, x, f: (h: e = x + 10) → Nat) { f(refl) }`) is refused
by the kernel with a located, spelled `refl needs both sides…` note, the
designed route.

`g` above computes `@g(1, 0, 0, refl) = 10` (and at a neutral `x`) when the
call's equation argument has an inferable type; a bare `refl` there is
deferred and refused with "write the call fully explicitly", since `refl`
checks only against a known equation. Pinned in
`crates/elab/tests/recursion_meaning.rs`.
