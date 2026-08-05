---
title: Type-argument inference does not see through an indexed family's index
status: closed
labels: [frontend,elaboration,ergonomics]
created: 2026-08-05
updated: 2026-08-05
---

Found by the [[dependent-motive-crossing-sweep]] round (2026-08-05), out of its scope.

`theorem t<A>(n: Nat, t: W3<A>(n)): idw(n, t) = t` is rejected with "cannot infer the type argument \`A\` of \`idw\` … no argument's type mentions it", even though `t`'s type is literally `W3<A>(n)`; the call must be written `idw<A>(n, t)`. The equivalent over a plain inductive (`r: Res3<A>`) infers fine — so the harvest that reads type arguments out of argument types does not look through the applied-index form an indexed family's type takes.

Small ergonomics ticket; the fix is presumably in the same first-order harvest [[congruence-by-anti-unification]]'s round threaded through `apply_implicit`.

## Log

- 2026-08-05: Fixed. The filed hypothesis was wrong in an instructive way: the family's type is not opaque because of a *reference* — the probe showed both family classes lower structurally, with no Ψ reference in sight. A declared-index `W3<A>(n)` is `El` of an **index recursion choosing among quoted codes** (`elimN(M; z «Σ…+…»; s «…»; n)`) with `A` inside the code literals; a forded `Fq<A>(n)` is a Σ-ford the structural walk already reached (that class inferred fine all along — only the declared-index class failed). So the fix is walker congruences for `elimN` and the type-code constructors (`«Π»/«Σ»/«W»/«Wf»/«+»/«Vec»/«Fin»/«Id»/«sEq»`), mirroring `unify_ty`'s complete former walk, with each variant's own binding depth. Two shapes were prototyped and deliberately **reverted** as untestable on today's lowerings: a same-definition congruence for `GlobalTm`/`GlobalTy` references (family types are not references anywhere a test can reach; if El-of-reference domains ever meet inference, that is the lever, tails compare up to the scratch-world's `n`-shift) and a rigid-rigid head-clash guard on the `App` case (learning across clashing heads is real but the kernel judges it; refusing needs a shape that distinguishes heads, which structural family types do not have). Negative control pinned accordingly: a structural look-alike family may teach the walker `A`, and the call still fails at the kernel — if look-alikes ever become convertible the test flips to a positive, not the walker to a refusal. Tests in `crates/elab/tests/implicit_args.rs` (declared-index positive — the issue's reproducer — forded positive, look-alike negative).
