---
title: An implicit parameter a structural self-call would infer anew is refused only by the kernel
status: open
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
