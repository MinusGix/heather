---
title: inj through a corecursive function's observation: elaborator accepts, kernel says NotInferable
status: open
labels: [elaboration,codata,bug]
area: language
created: 2026-11-03
updated: 2026-11-03
---

`inj(e)` is accepted by the elaborator and refused by the kernel with a bare
`NotInferable` (no location, no spelling) when `e`'s left side is an
observation that only reaches a constructor by reducing a corecursive
function's output. Found in [[eutt-iteration-and-io-reading]]'s round,
in `Io::pass_ret` (`lib/std/os/linux/linux_world.hthr`):

```
// e : CoTree::after(Events::none(), 0, Io::pass_reading(t, io)) = ORet(r)
// Io::pass_reading_at(t, io, ORet(x), h0) :
//   CoTree::obs(Events::none(), Io::pass_reading(t, io))
//     = CoTree::obs(Events::none(), Io::pass_reading_obs(ORet(x), io))
// and the right side reduces to ORet(Io::shift(Mutated(io, x))), where
// pass_reading_obs is CoTree::map of the corecursive Io::against_co_obs.
prelude::sym(inj(prelude::trans(prelude::sym(Io::pass_reading_at(t, io, ORet(x), h0)), e)))
// the kernel rejected `Io::pass_ret`: NotInferable
```

The same `inj` on an `OTau` equation of the same shape (`Io::pass_tau`)
passes, and a small file with `ORet(f(x)) = ORet(r)` through a plain
non-corecursive reduct does not reproduce it, so the trigger is likely the
reduct of the `M` corecursor (an unannotated pair or projection in the
whnf the elaborator hands to the eliminator; compare
[[emission-walker-residual-sites]]'s 2026-09-23 note on unannotated
projections being NotInferable).

**Workaround used**: `Obs::ret_same(E, o, a, r, at, e, λ y => y = a, refl)`
(`coitree_rec.hthr`), which transports through `j` and never asks the
kernel to infer the reduct.

**Done when** `inj` either elaborates to a term the kernel can infer here,
or refuses at elaboration with a located message; a probe in
`lib/_tests` restores the `inj` form of `pass_ret`'s two return cases.
