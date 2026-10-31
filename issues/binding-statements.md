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

Against `docs/sequencing-surface-design.md` (§2, §3, §10, §12):

- `let x <- e;` (also `←`, an annotated binder, record destructuring, `let _ <- e;`), the expression statement `e;`, nested `(<- e)` and `match <- e { … }`, lowered in `elab_stmts` to `M::bind(e, λ x => rest)`. No trusted rule.
- The carrier protocol is owner members (§2.1): `M::bind(self m, k)`, and `M::pure(a)` where a form injects a value. The carrier is the owner of the scope's expected type, else of its first bound expression by owner-by-head resolution (§2.2). One carrier per scope, no lifting.
- Nested binds run in written order and stay inside their match arm, `if` branch or λ (§3.2).
- The library members of §2.3: `Tac::pure`, `Tac::or_fail`, `Option::bind`/`pure`, `Result::bind`/`pure`, `Parser::pure`, and a `self` form of `ITree::bind`.
- `?` for `Option` beside `Result` (`docs/result-propagation-design.md`, design §3.5).
- Port `lib/std/tactic/mono.hthr` and one parser-combinator chain as the customers. `scripts/timings --diff` on mono's probes shows identical count columns, since no kernel term changes.
- The tree-sitter grammar and `heather fmt` learn the forms.
- Refusals that name their reason (design §10, layer-1 rows): no `bind` on the carrier, a computation on another carrier, `e;` in a pure scope, and a discarded non-`True` result (a lint).

## Done when

`mono.hthr` has no `bind` towers, and the `.bind(` count in `lib/std/tactic` falls by most of `mono`'s share.

## What it assumes from elsewhere

- **[[sequencing-surface-design]]** owns the spelling and the protocol.
