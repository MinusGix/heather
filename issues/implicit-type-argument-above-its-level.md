---
title: An inferred type argument above its parameter's level reaches the kernel
status: closed
labels: [frontend,elaboration,diagnostics]
area: language
created: 2026-11-09
updated: 2026-11-09
---

A type parameter is `Type<0>` unless annotated, but an inferred type argument
is not checked against that level before the term is emitted:

```heather
import logic;
fn bot1<A: Type<1>>(e: False) → A { false_elim(e) }
```

is refused by the kernel (`the kernel rejected bot1: LevelMismatch`), with no
elaborator diagnostic: `false_elim<P>`'s `P` is solved to `A`, which lives at
`Type<1>`. Writing the argument (`false_elim<A>(e)`) is refused properly by
the elaborator ("universes in this system are non-cumulative"). The inferred
route should give the same refusal, at the argument.

Met in `lib/std/locale/frame.hthr`, whose carriers live at `Type<1>`; the
library writes `match e {}` instead.

Related: [[generic-congruence-inferred-type-arg-level-mismatch]] (a different
cause, closed), [[implicit-level-polymorphism]] (which would make the call
legal).

## Log

- 2026-11-09: Filed from frame-and-locale-foundations.
- 2026-11-09: Done. The unifier's El rule declines to solve a meta at `Type<n>` with a type whose apparent level is another (`apparent_level`), and records the decline; the unsolved-argument error then says which level the parameter wants and which the call offers, with the non-cumulativity reason. Probe in lib/_tests/lang/universe_parameter_tests.hthr. The call stays refused: making it legal is implicit-level-polymorphism.
