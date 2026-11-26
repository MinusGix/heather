---
title: The checker with several objects per function, references held in data, and places with steps
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

What the fourth experiment ([[ownership-checker-loans-and-joins]], `lib/lang/ownership/call_check.hthr`) left untested, from its log of 2026-11-25. Every function there has one object (its parameter, or for a `Lends(n)` function one erased owner), and every place is a window of one list.

## Scope

- **Several objects per function.** Several parameters, or local objects, each with its own places; a write view of one beside views of another. The checker's state becomes a map keyed by object ([[place-check-name-lookup-cost]]: the holder table as a `NatMap`), and its cost should be measured again at doubling sizes. `FnSafe` then states one `OnRef` per parameter; the frame of a call is per object.
- **References into several owners.** A lending function lent references into two owners takes two erased owners (one per region parameter, §15.8); its promise is stated at one reference per owner. The fourth experiment's promise names the owner's place once; whether it still names nothing per object reachable, with several, is the open question.
- **A collection held in data across statements.** There the stored references were the call's argument, formed at the call (`CallAll`). A cell holding write views as a value that lives across statements, is passed on, or is returned, is the case §15.2 describes (`&mut{o} T` stored in data: the value and an erased slot). Whether the place states still suffice once the cell is a value with its own lifetime beside its owner's is the open question.
- **Places with steps.** A window is the only place kind; a field of a record inside a window, and `Steps::apart` deciding overlap (`steps.hthr`), are untested in the checker.
- **One checker.** `place_check.hthr`, the first experiment's checker, still stands beside `call_check.hthr` with its own statement of the licence over named versions, several objects and clone. Once `call_check.hthr` has several objects, fold the first experiment's programs into it and delete `place_check.hthr` (the charge of §14.18).

## Done when

`check_sound` over a fragment with several objects, references into two owners, and a cell of references held across statements, each with an accepted program and a `¬` control, and the log answers whether place states still suffice.

## Log

- 2026-11-25: Not a further round on `call_check.hthr` (docs/language/ownership-design.md §20): the experiment module is not extended again. This is a requirement on the checker built once over the fixed interfaces (§20.6) and is closed by that build.
- 2026-11-25: The interface this is built against is fixed in docs/language/ownership-design.md §21 (the build's probes: §21.5).
