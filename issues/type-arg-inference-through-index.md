---
title: Type-argument inference does not see through an indexed family's index
status: open
labels: [frontend,elaboration,ergonomics]
created: 2026-08-05
updated: 2026-08-05
---

Found by the [[dependent-motive-crossing-sweep]] round (2026-08-05), out of its scope.

`theorem t<A>(n: Nat, t: W3<A>(n)): idw(n, t) = t` is rejected with "cannot infer the type argument \`A\` of \`idw\` … no argument's type mentions it", even though `t`'s type is literally `W3<A>(n)`; the call must be written `idw<A>(n, t)`. The equivalent over a plain inductive (`r: Res3<A>`) infers fine — so the harvest that reads type arguments out of argument types does not look through the applied-index form an indexed family's type takes.

Small ergonomics ticket; the fix is presumably in the same first-order harvest [[congruence-by-anti-unification]]'s round threaded through `apply_implicit`.
