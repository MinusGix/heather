---
title: inj through a corecursive function's observation: elaborator accepts, kernel says NotInferable
status: closed
labels: [elaboration,codata,bug]
area: language
created: 2026-11-03
updated: 2026-11-04
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

## Resolution

- 2026-11-04: Closed. The trigger was wider than corecursion: any equation
  whose side reaches its constructor through a codata `match` reproduced it,
  down to `CoTree::obs(E, CRet(n)) = ORet(r)`. A codata term is emitted in the
  kernel's checked spelling, so the label `out` hands the `match` is a bare
  `pair@`; the arm reads its field as `fst@(snd@(v))`, and the weak head
  substitutes the bare label for `v`. The kernel infers a projection's
  receiver and a bare pair does not infer, so the field, the endpoints `inj`
  hands `J`, and every term built from them were `NotInferable` (in
  `pass_ret` the field is a λ applied to such a projection, so the redex sat
  under an application, not only at the top). `pass_tau` passed because its
  field is the child tree, a `corec`, which infers.
- Fix: `spelling::contract_projections` reads every projection of a literal
  pair off the pair, through the formers a reduct's fields are built of, and
  `equation` (the reader under `inj` and `absurd`) applies it to both reduced
  endpoints. It is Σ's β rule and only removes nodes, so it is convertible
  and moves no scope.
- `Io::pass_ret`'s two return cases use `inj` again
  (`lib/std/os/linux/linux_world_co.hthr`); probes in
  `lib/_tests/std/itree/coitree_tests.hthr` (`inj_obs_ret`, `inj_obs_map`,
  `inj_corec_ret` in a checking position, `inj_corec_tau_ret` through
  `absurd`, and the refused `inj` between different constructors).
- The class, not only the instance: a kernel `NotInferable` is now a
  `KernelSite::Unrecorded` refusal like a bare `NotConvertible`
  ([[elab-accepts-conjunction-for-equation]]), so the locator re-runs the check and the
  report says it is an elaborator gap and at which expected type, where it
  was a bare `NotInferable` before. `check --expectations` and
  `assert_refused` refuse to pin one, as they do the conversion kind.
