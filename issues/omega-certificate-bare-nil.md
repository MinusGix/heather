---
title: omega's certificate spells a refined list as bare Nil and cannot re-elaborate it
status: open
labels: [omega,proofs,bug]
area: tactics
created: 2026-10-31
updated: 2026-10-31
---

`omega` fails in a `Nil` arm whose goal mentions the scrutinee's length,
because the certificate it generates spells the refined list as a bare
`Nil` and re-elaborates it where nothing fixes the element type. Found by
the sequencing design's probe P2 (`docs/sequencing-surface-design.md`,
appendix). Minimal repro on `3099a7d`:

```heather
import logic;
import nat;
import list;
import omega;
theorem t(xs: List<Nat>, w: Nat): w <= w + xs.len() {
    match xs { Nil => omega, Cons(_, _) => omega }
}
```

The `Nil` arm fails with "cannot infer the type argument `A` of `List` here
— no argument of `Nil` determines it", and the note shows the generated
certificate: `omega::nat_le_of_not_not_le(w, nat::Nat::add(w,
list::List::len(Nil)), …)`. The `Cons` arm is fine.

This is the generated-source gotcha the ring work hit ("generated source
must not use `list::Nil`"). The certificate should spell constructors with
their type arguments (`Nil<Nat>`), or not re-elaborate atoms it already
holds as terms.

## Done when

The repro checks, and a probe in `lib/_tests` pins it.
