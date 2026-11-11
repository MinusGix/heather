---
title: Conversion walks a spelled-out reflection when one argument beside it is respelled
status: open
labels: [kernel,conversion,performance,native,runtime-fn]
area: kernel
milestone: [nh-front]
created: 2026-11-11
updated: 2026-11-11
---

Two types that differ only in how one small argument is spelled, with a large
literal beside it, cost the kernel a comparison of the literal's reductions,
and the cost grows as a high power of a numeral inside the literal. Found
while restating the `Compile` class at every file
([[native-one-compiler]], U3c step 3a,
`docs/native-one-compiler-design.md` §2.3).

## The shape

The class's agreement at a file `b` is stated at the world there,
`world.at(callees, b)` (`World::over(world, callees(b), b)`). A first
restatement kept the function's type at the bare world's table:

```
typed: Itself(F) = Itself(Ty::Lent(world.tys, reflected.lent, reflected.params, reflected.result)),
agrees: (b: Buffers()) → … → Ty::Answers(world.at(callees, b).tys, …,
    Ty::lent_at(world.tys, …, typed, f, b), λ xs => code.eval(call, xs, buffers := b)),
```

and the builder's pin compared the function with
`rt.meaning(w.over(callees(b), b))`, whose inferred type is
`Ty::Arrows(w.over(callees(b), b).tys, rt.params, rt.result)` against the
expected `Ty::Arrows(w.tys, rt.params, rt.result)`. The two table arguments
are one projection step apart (`World::over(w, cs, b).tys` is `w.tys`), and
every other argument is the same term.

Written by hand, over named definitions or over hand-written literals, this
costs nothing to notice. A generated instance is gated at a reflection the
generator spells out in full (constructor functions as β-redexes with their
type encodings inline, several hundred thousand characters printed), and
there the comparison did not shortcut on the equal arguments. Its kernel
steps over one shift by `k` in the body (`x.shift_left(k)` as a
`runtime fn`):

| `k` | 0 | 16 | 32 | 48 | 56 | 59 and up |
|---|---|---|---|---|---|---|
| steps | 333k | 394k | 900k | 2.86M | 4.88M | out of fuel |

against about 318k at every `k` before the restatement and 312k after the
fix. The conversion-miss trace (below) put the time in misses between
`…(W)` and `…(World::over(W, ·, ·))` inside the type of
`Fun::meaning(rt, …)`. `examples/x86-native/shifts_past.hthr` (a shift by
1000) and `sha512_small0` in `lib/native/crypto/sha512_round.hthr` (by 63)
were refused with `OutOfFuel`.

## What the library does about it

One spelling: `World::at(w, callees, b)` is the only way the class, the
builders and the generator name the world at a file, its type table
included (`w.at(callees, b).tys`, never `w.tys`), and `typed` is stated per
file. Costs are flat again. The rule is in `docs/proof-patterns.md` §2.
That is a workaround in the statement: nothing stops the next class from
meeting the same cost.

## Investigation

- Why the equal arguments are not accepted before the differing one is
  reduced. Candidates: the reflection literal appears as distinct `Rc`s on
  the two sides (so the pointer shortcut misses and the memo keys differ),
  or the differing argument makes the head application miss and the kernel
  falls back to normalizing both sides, numeral included.
- Why a numeral inside the literal sets the exponent: the growth is far
  steeper than one walk of a unary count.
- Whether comparing an application's arguments left to right with the
  cheap ones first (or the small one first) would have made this a one-step
  conversion.
- Related: [[conv-pointer-equality-reflexivity]],
  [[conversion-cost-at-large-values]], [[constructor-literal-respell-cost]],
  [[runtime-shift-conversion-unfolding]] (the same numerals, met from the
  elaborator's side).

## Reproducing

Restore the two lines above in `class Compile` (and `Setup::typed_refl`
without its file binder), and check a `runtime fn` whose body shifts by 48.
To see where the conversion goes: build with
`--features value-metrics` into a target directory of its own, then run the
check with `HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=<fn name>` (the
bare function name, not `f::compile`); each `conv miss trace … <ms>` line is
followed by excerpts of the expected and the inferred type. A cached verdict
hides a re-run, so rename the function between runs.

## Acceptance

- The statement with two spellings of the world costs within a small factor
  of the statement with one, at every shift count, on generated instances.
- A kernel benchmark or probe case holds the shape (a large generated
  literal beside an argument respelled by one projection).

## Log

- 2026-11-11: Filed from U3c step 3a. The statement was respelled; the
  kernel was not changed.
