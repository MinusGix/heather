---
title: Rewrite along a relation inside a codata constructor
status: open
labels: [setoids,relations,tactics,coinduction]
area: tactics
milestone: [tac-general,nh-effects]
created: 2026-11-03
updated: 2026-11-03
---

A relation `rewrite` (`docs/equation-rewrite-design.md` §9, §11) matches a
codata constructor as an occurrence (`CTau(t)` against `Eutt::tau_l`, §11.2)
but does not walk *into* one: `CTau(bind(bind(t, f), g))` with `bind_assoc`
is refused ("a form that is no application or λ"), because a constructor is a
`corec` whose children sit inside its step (`λp. inr(t)`, under the step's
two binders and the position's), not an application spine.

Wanted: a constructor `corec` read as a node whose arguments are its fields
(the label's payload and the children, a function child as a λ), rebuilt with
a changed child, and its context written `λ z. CTau(z)` / `λ k. CVis(c, k)`
as `Eutt::tau_respects` and `Eutt::vis_respects` state it, so resolution
answers it. `read_ctor` reads the label but gives children back as
stand-ins; the walk needs the children themselves.
