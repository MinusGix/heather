---
title: Name the refusal when a partial fn's call is used as its result
status: done
labels: [diagnostics,sequencing]
area: language
milestone: [lang-sequencing]
created: 2026-11-03
updated: 2026-11-06
---

Calling a `partial fn` where its result type is expected is a plain type
mismatch today:

```
fn use_it(n: Nat) → Nat { down(n) }
// error: this has type `CoTree<Nat>(none)`, but `Nat` is expected here
```

docs/language/partial-functions-design.md §4.2 promised a named refusal: "`f` is
partial: bind it with `<-`, or use `CoTree::get` with a termination proof".
The mismatch is found late (a kernel-located refusal recorded at a checking
site, `RecordedSite::Check` in crates/elab/src/lib.rs), so the restatement
needs the elaborator to know which globals are partial, including imported
ones (a flag in the module image, or `f::body`'s designation read back).
The displayed type should also read `Partial(Nat)`
([[type-name-display-respelling]]).

## Done when

The probe above is refused with the named reason, under `expect-error` in
`lib/_tests/std/itree/partial_fn_tests.hthr`, for a partial function from
the same module and from an imported one.

## Log

- 2026-11-05: gardener: cites a file it shares with [[partial-fn-tail-iter]] (`lib/_tests/std/itree/partial_fn_tests.hthr`).
- 2026-11-06: Done. The fallback checking site records the call's head with
  its mismatch candidate (`note_check_expr`, `CheckNote::partial`); when the
  gate refuses, both the probed note and the recorded kernel site ask
  `Elaborator::is_partial_fn` (`f#body` designated `f::body`, no `f::rec`, so
  imported functions count and measures do not) and say "`f` is partial, so a
  call to it is a computation that may not return: this one has type
  `Partial(B)`, but `B` is expected here; bind it with `let r <- f(…);` inside
  a computation, or use `CoTree::get` with a termination proof". Probes: the
  same-module case, an argument position and the ordinary two-computation
  mismatch in `partial_fn_tests.hthr`; the imported case (`Tm::whnf_co`, as a
  call and as a method) in `lib/_tests/kernel_model/kernel_whnf_tests.hthr`,
  which already imports it, rather than growing `partial_fn_tests`' closure
  by the kernel model. docs/language/partial-functions-design.md §9 item 11.
- 2026-11-06: type-name-display-respelling closed without respelling `Partial` in general display (the named refusal above spells it itself): Partial takes a type and is codata, filed as [[type-name-respelling-type-arguments]].
