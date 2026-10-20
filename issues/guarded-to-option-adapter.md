---
title: Guarded total fns get their Option/Result face by adapter, not by twin definition
status: open
labels: [frontend,design,ergonomics,stdlib]
area: language
created: 2026-08-14
updated: 2026-08-17
---

Filed from the datarepr design review (2026-08-14, user note on
docs/datarepr-design.md sec. 2.2): a guarded total function
`nth_g(l, i, h: i < len(l)) -> A` should not need a hand-written twin
`nth -> Option<A>` — the Option/Result face is derivable by an ADAPTER
(helper fn or syntax): decide the precondition; None on failure, otherwise
Some(nth_g(l, i, proof)). Composes with the intended default that proof
parameters are inferred from context (`h := infer_via_tactic` — the
"too lazy to pass it" commonplace), so the guarded form is the one
canonical definition and every weaker face is mechanical. The datarepr
dispatch ladder's rung 2 (decide-and-bubble, datarepr-design sec. 2.2) is
this same adapter living inside generated Impls; this issue is the
SPEC-SIDE/surface face of it. Decider provenance is shared with
[[class-ops-prop-vs-bool]] — and per the user (2026-08-14): a rung-2/adapter
decider must be RUNTIME-COMPUTABLE (Compile-instance-bearing when used for
compilation), Decidable alone does not mean sane-to-run. Related:
[[datarepr-separation]].

## Log

- 2026-08-17: First customers, and they arrived written the other way (issues/std-list-api.md, 2026-08-17): `std/list` now has `List::head` and `List::last`, both returning `Option<A>` outright, because that is the only spelling available today. So this issue's premise is now concrete rather than hypothetical — there are two functions in the library whose `Option` face is the DEFINITION rather than an adapter over a guarded total function, and closing this issue means rewriting them and keeping the current signatures as the adapted view.
