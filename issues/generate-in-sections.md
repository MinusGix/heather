---
title: Run generate inside a section and under assuming
status: open
labels: [metaprogramming,elaboration]
area: tactics
created: 2026-10-28
updated: 2026-10-31
---

`generate g(args);` is refused inside a `section` and under `assuming`
(crates/syntax/src/parser.rs; docs/host-elaboration-interface-design.md
§19): a generator runs at the module's empty context, and nothing yet says
how its declarations would inherit the head's binders (a section's carrier
and class dictionaries, an `assuming` telescope). Generic lemma groups are
exactly what a section is for (`congruences` over a carrier with a class in
scope), so the refusal is the gap, not a design choice.

## Acceptance

- Decide whether the generator runs under the head (its `Goal`-less run gets
  the head's binders as root locals) or outside it with the head spliced onto
  each published member, and record which in the design doc.
- `generate` inside a `section<A: …>(…)` publishes members that take the
  section's head like a written member does, checked by a probe that uses one
  at a concrete carrier.
- The `assuming` case follows the same rule or keeps a named refusal.

## Log

- 2026-10-31: `tac-host-interface` is marked done in docs/roadmap.md (its "done when" is met), so this issue no longer serves it; it stays open in area `tactics` with no milestone.
