---
title: Infer an implicit from a record type's parameter when its fields project it
status: open
labels: [elaborator,inference]
area: language
created: 2026-10-31
updated: 2026-10-31
---

An implicit argument that appears only as a parameter of a record type is
not inferred from an argument of that type when the record's fields reach
the parameter through a projection. The memory `X86Memory(x)` is the case
that keeps coming up: `fn X86Memory::LoadedFrom({x: X86Profile}, size: Nat,
self m: X86Memory(x), file)` refuses `m.LoadedFrom(size, file)` with "could
not infer the implicit argument `x`", even when `m` is a local of type
`X86Memory(x)` for a variable `x`. Rounds have worked around it by making
the parameter explicit (`m.LoadedFrom(x, size, file)`,
issues/io-image-process-stack.md) or by turning it into a field
(memory-model-machine-instances, wp-view-separating-product).

## Reproduction

```
record Q { k: Nat }
record U(x: Q) { v: Nat, ok: x.k = v }
fn U::f({x: Q}, self m: U(x), k: Nat) → Nat { m.v }
fn use2(x: Q, m: U(x)) → Nat { m.f(1) }      // refused: could not infer `x`
```

The same shape with a field that names `x` whole (`ok: x = x`), or with a
parameter of type `Nat` (`ok: v = x`), or a function (`ok: x(v)`), infers
`x`. So the failure is the projection in a field type: it looks as though
the unifier meets the record type through its fields, where `?x.k` against
`x.k` has no Miller solution, instead of matching the type former's
arguments first.

## Scope

- Match a record type former applied to arguments against the same former
  head-first (the arguments pairwise), before or instead of unfolding it;
  a solution found that way is sound even if the former is not injective,
  only incomplete.
- Then drop the explicit profile from `X86Memory::LoadedFrom` and
  `X86Memory::loaded_entry` (lib/std/os/linux/linux_x86_64_image.hthr).
