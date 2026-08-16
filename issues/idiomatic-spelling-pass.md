---
title: Fixtures and docs use the idiomatic surface, not the generator's explicit style
status: open
labels: [docs,testing,ergonomics]
created: 2026-08-15
updated: 2026-08-16
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

## Log

- 2026-08-16: Unblocked-ish (2026-08-16, the repr-access-spellings round): generator EMISSION bytes are unchanged — every generator still writes Repr_N::abs(), N_spec_rec, Impl_R_f::body() — but the surface now has one designed spelling (N::abs, N::spec_rec, Impl(f, N)::body) that resolves to those declarations through an alias, and the minted forms are refused in user source. Two consequences for this issue's pass. First, the fixture half is already done for datarepr/reprgen/obligation-records/record-projection tests: every hand-written certificate and fixture in them now spells the designed form; what still spells minted names is exactly the assertions ABOUT emission text and the hand-forced emissions, which are generated source and should stay. Second, flipping the emissions themselves to the designed spelling is now a pure style choice rather than a compatibility event — the alias means both spellings resolve inside generated mode — so this issue can do it whenever it runs, at the cost of re-baselining the emission-text assertions.
