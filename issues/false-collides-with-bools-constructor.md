---
title: "A type name and a constructor name are one namespace, so `False` is unavailable"
status: closed
labels: [frontend,elaboration,modules,stdlib,naming]
created: 2026-08-16
updated: 2026-08-16
---

**Closed 2026-08-16.** Fixed by route (a) below, plus a third fix the plan did
not predict; see the Log. The body is kept as filed.

`lib/std/logic.hthr`'s empty type is named `Empty`. It should be named
`False` — it pairs with `True`, and it is what `¬P` unfolds to — and it
cannot be, because `bool::False` already exports that name.

The collision is not between two types. It is between a **type name** and a
**constructor name**, and it fires in **type position**, where a constructor
could never have been meant:

```
import bool;        // inductive Bool { False, True }
import falsy;       // inductive False {}

theorem t(P: Type, h: False): P { match h {} }
//                     ^ `False` is ambiguous: it is declared in `bool` and `falsy`
```

Reproduced at `crates/elab/tests/logic.rs`,
`false_is_not_available_as_the_empty_types_name`.

**`True` escapes this only by not being a declaration.** It is the kernel's
`Unit^0` claimed as a surface name in `lower_named`
([[true-prop-trivial-hypotheses]]), so it never enters a module's export list
and never competes. That is an accident of how `True` had to be built, not a
policy — and it is why the asymmetry is worth fixing rather than working
around twice.

## Two ways out, and they are not exclusive

**(a) Resolve by position.** A constructor is not a type name. The elaborator
already knows which position it is in — `lower_named` is *the* type-position
path — so a name that resolves to a constructor there could be skipped rather
than counted as a competing candidate. Cheapest, fixes the general case (any
library type sharing a name with any constructor anywhere), and makes the
diagnostic honest: today an annotation says "ambiguous" while a result type
says "`False` cannot be used here", for the same collision.

**(b) Claim `False` over the kernel's `Empty`,** mirroring `True` exactly.
Symmetric, and it buys the same never-in-a-namespace property. More
expensive than `True` was, and the extra cost is the reason this is not
already done: `True` needed only an inhabitant (`trivial`), while `False`
needs an **eliminator** reachable from the surface. `match h {}` on a
*declared* zero-constructor inductive works today; on a kernel `Empty` there
is no declaration for the match to look up, so that path needs building
(compare `absurd`, which takes an equation and does not apply here).

Recommendation: **(a)**, because it is the general defect and (b) is a
name-by-name fix that leaves the next collision unaddressed. (b) remains
attractive on its own terms — kernel `Empty` has η questions of its own
([[empty-eta-conversion]]) — but as an `Empty`/`False` story rather than as
this issue's fix.

## What it assumes from elsewhere

- **[[true-prop-trivial-hypotheses]]** owns `True`'s residency. Assumed here:
  only that it is claimed in `lower_named` rather than declared in a module,
  which is what makes it immune.
- **[[std-logic-module]]** owns the `logic` module. Assumed here: only that
  its falsity is currently spelled `Empty` and that a fix here is a rename.
- **[[type-owned-namespaces]]** owns namespacing declarations by type.
  Assumed here: nothing — a constructor's home namespace is a separate
  question from whether a *type* position should see constructors at all.

## Acceptance

`lib/std/logic.hthr` declares `False`, a file importing both `bool` and
`logic` uses `False` in type position and `False` in expression position in
the same declaration, and the existing coexistence test for `True`
(`crates/elab/tests/true_prop.rs`) still passes unchanged.

## Log

- 2026-08-16: Filed from the [[std-logic-module]] round, which hit this while
  writing the module and renamed rather than shipping a library that cannot
  be imported beside `bool`. The finding that makes it more than a naming
  gripe: the two type positions **disagree** about the diagnosis — an
  annotation reports ambiguity, a result type reports "cannot be used here" —
  so whatever consults the namespace is not the same code in both, and one of
  them is already close to the position-directed answer.
- 2026-08-16: FIXED (2026-08-16), same day, and by route (a) — resolve by position — as recommended. `lib/std/logic.hthr` declares `False` and the round's placeholder `Empty` is gone. TWO rules, and the round's finding is that ONE was not enough because the collision has two halves that fail in different places. (1) TYPE POSITION never considers a constructor a candidate: `names::resolve_kinds` takes the candidate kinds and `Elaborator::lookup_inductive` passes `[Inductive]`. This is the half the issue described, and it covers `h: False`, `P -> False`, `Or<P, False>` and — a case worth naming because it looks like expression position and is not — `Not(False)`, whose argument reaches `lookup_inductive` through `expr_as_ty`. (2) EXPRESSION POSITION at an inductive expected type never considers a TYPE NAME one: `only_ctors_visible` used to stand the expected-type route down whenever any visible candidate was not a constructor, and an `inductive` is now admitted beside them, because a type name denotes a value whose type is a UNIVERSE and could never inhabit the expected inductive. Without (2), `and(False, True)` still failed with `False` unusable as a Bool. A `Global` still stands the route down and must: a `fn` may perfectly well return the expected type, so between it and a constructor there is a real decision and this route does not make those — pinned by `a_global_of_the_same_name_still_stands_the_route_down`. BOTH RULES ARE SHRINKS, NEVER CHOICES, which is the whole licence: in each case the dropped reading could not have checked where it was dropped, so this is docs/modules-design.md §8's invariant applied to a syntactic position and to a second kind, not a new precedence. THE THIRD FIX, and the one the plan did not predict: `ctor_here_expected` must WHNF the expected type before reading its tag. A declared result type arrives structural, but a parameter's domain — which is what an argument is checked against — can still be a reference that only δ-unfolds to the lowering `tag_of` reads, so before this `theorem t(): Bool { False }` resolved and `idb(False)` did not. That is the same question in two spellings, and the asymmetry was invisible until (2) made the first half work. Cost is confined to the fallback: the line is reached only after the ordinary reading has already failed. NOT DONE, and not needed: route (b), claiming `False` over the kernel's `Empty`. It stays available as an `Empty`/`False` story of its own (a surface eliminator for kernel `Empty` is the piece it would need, since `match h {}` looks up a declaration), but nothing wants it now — and (a) was preferred precisely because it fixes the general defect rather than one name. The issue's own reading of the diagnostics was right and is now moot: the two type positions disagreed because the annotation path and the result path consult the namespace differently, and both now resolve rather than report. Tests: crates/elab/tests/logic.rs `the_two_falses_coexist` (both `False`es in one declaration, five type-position spellings and five expression-position ones, none qualified) and `a_global_of_the_same_name_still_stands_the_route_down` (the control). Docs: docs/logic-connectives-design.md §6.1. CLOSING.
