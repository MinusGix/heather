---
title: Fixtures and docs use the idiomatic surface, not the generator's explicit style
status: open
labels: [docs,testing,ergonomics]
created: 2026-08-15
updated: 2026-08-15
---



Spun off [[datarepr-surface-ergonomics]] finding 0, user-ratified
(2026-08-15): the idiomatic spelling —

```heather
Repr_ListTok::fold(Nat, Zero, λ t r b => Succ(b), l)
```

— already checks (n-ary application of a namespace member, unannotated
multi-binder λ in checking position), reads far better than the curried
fully-annotated form the fixtures copy from the generator, and the sugar
"isn't that intricate to unfold into the underlying case" (user). Pass
over the datarepr/reprgen fixtures, hand-runs, and the design doc's
examples.

Open sub-question for the pass: whether **generator emissions** switch
too. The user's rationale (desugaring is simple and reliable) leans yes;
the cost is a deliberate byte-stability flip across every pinned emission,
so it should be its own commit with every changed emission named. The
hand-runs are emission specs, so they follow whichever way the emissions
go — fixtures that are *not* emission specs switch regardless.
