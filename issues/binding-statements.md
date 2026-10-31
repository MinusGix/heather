---
title: Bind results in blocks over any carrier with a bind (let x <- e;)
status: open
labels: [frontend,syntax,elaboration,ergonomics]
area: language
milestone: [lang-sequencing]
created: 2026-10-31
updated: 2026-10-31
---

Round R2 of `docs/compiler-milestones-proposal.md` (§3.1, §7): binding statements over any carrier, as
[[sequencing-surface-design]] decides them.

## Scope

- `let x <- e;` and `e;` in a block whose carrier has a `bind`, lowering to the `bind` chain written by hand today, with no trusted rule.
- `?` for `Option` beside `Result` (`docs/result-propagation-design.md`).
- Port `lib/std/tactic/mono.hthr` and one parser-combinator chain as the customers.
- Refusals that name their reason (`docs/test-value-audit.md` §5): `<-` in a block with no carrier, and a carrier with no `bind`.

## Done when

`mono.hthr` has no `bind` towers, and the `.bind(` count in `lib/std/tactic` falls by most of `mono`'s share.

## What it assumes from elsewhere

- **[[sequencing-surface-design]]** owns the spelling and the protocol.
