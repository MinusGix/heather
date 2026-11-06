---
title: Corecursive match on an index term at an inline codata signature
status: open
labels: [codata,coinduction,elaborator]
area: interaction-trees
created: 2026-11-06
updated: 2026-11-06
---

A corecursive body matching a term its result index mentions works when the
codata's signature is *named* (every type argument at `Ty 0`): `corec_check`
reads the arm's refined index off the shape's last argument,
`El(D#mshape ā idx)` (`step_index`, crates/elab/src/codata.rs;
[[corec-match-on-index-term]]). An *inline* signature (a type argument above
`Ty 0`) has no named shape to read, so the arm still falls through to the
ordinary constructor path:

```
codata CountA<A> : (n: Nat) -> Type { TickA(x: A, at: Nat, ok: at = n, next: CountA<A>(Succ(n))) }
fn c(n: Nat) -> CountA<Type>(n) {
    match n { Zero => TickA(Nat, 0, refl, c(1)), Succ(m) => TickA(Nat, Succ(m), refl, c(Succ(Succ(m)))) }
}
// error: `TickA` is a constructor of `CountA`, which is not the expected type here
```

Reading the index needs first-order matching of the inline shape `S` (over
`Γ, i`) against the arm's `Σ`'s first component, or the corecursion site
tracking the refinement the match applies. The error should at least name
the cause until then.

## Done when

The example elaborates (or is refused with a message naming the inline
signature), with a probe at a literal and an open argument.
