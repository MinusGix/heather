---
title: A type mismatch in a meta fn is refused only by the kernel, unlocated
status: open
labels: [elaboration,diagnostics,meta]
area: language
created: 2026-11-03
updated: 2026-11-03
---

Found probing [[recursion-on-elaborated-terms]] (master c345c863). Inside a
`meta fn`, a type mismatch passes the elaborator and only the kernel refuses
it, as a bare `NotConvertible` at the declaration with no note and no span
at the expression:

```
meta fn b1(g: Ctx, n: Nat) -> Code(g |- Nat) { n }
meta fn b2(g: Ctx, x: Code(g |- Nat)) -> Nat { x }
meta fn b6(g: Ctx, x: Code(g |- Nat)) -> Code(g |- Bool) { x }
meta fn a1(g: Ctx, x: Code(g |- Nat)) -> Code(g |- Nat) {
    match code x as Nat { tm_succ(y) => y, _ => x }
}
// error: the kernel rejected `b1`: NotConvertible   (each)
```

An ordinary `fn` gets "this has type `Nat`, but `Bool` is expected here"
through `kernel_refusal`'s recorded sites. The meta gate
(`elab_meta_decl_inner`, crates/elab/src/quote.rs) maps kernel errors to
`ElabError::Kernel { note: None, site: Other }` directly.

Tried: routing both meta kernel checks through `kernel_refusal` (Layer::Meta).
The note improves, but `recorded_site_of` matches the refusal to an
**earlier declaration's** recorded site (b2, b3 and b6 all pointed at b1's
`n`), and `CodeTm` displays as its inner type (`Nat`), so `b6` read "this has
type `Nat`". Reverted: a wrong location is worse than none.

## Fix shape

The elaborator should refuse the mismatch itself (P1: the kernel is the net,
not the check): `elab_check` at a `Code`/`CodeTy` expected type compares the
inferred type and says so at the expression, with a display that spells
`Code(g |- T)`. Then clear or scope recorded sites per meta declaration so
the `kernel_refusal` route is safe as a backstop.

## Acceptance

Each example above refused by the elaborator at the expression, naming both
types as written; an expect-error probe per shape in lib/_tests.
