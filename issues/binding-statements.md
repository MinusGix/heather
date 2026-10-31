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
- The carrier protocol is the classes `Bind<M: Type → Type>` and `Pure<M>` (§2.1), from [[higher-kinded-classes]]; owner members `M::bind`/`M::pure` are the fallback. The carrier is the constructor of the scope's expected type, else of its first bound expression (§2.2). One carrier per scope, no lifting.
- Nested binds run in written order and stay inside their match arm, `if` branch or λ (§3.2).
- The instances and helpers of §2.3: `Bind`/`Pure` at `Tac`, `Option`, `Result`, `Parser`, `ITree`; `List::for_m`, `traverse`, `when`; `Tac::or_fail`.
- `?` for `Option` beside `Result` (`docs/result-propagation-design.md`, design §3.5).
- Port `lib/std/tactic/mono.hthr` and one parser-combinator chain as the customers. `scripts/perf ab` shows mono's probes do not move beyond noise (the lowered term now goes through one instance).
- The tree-sitter grammar and `heather fmt` learn the forms.
- Refusals that name their reason (design §10, layer-1 rows): no `bind` on the carrier, a computation on another carrier, `e;` in a pure scope, and a discarded non-`True` result (a lint).

## Done when

`mono.hthr` has no `bind` towers, and the `.bind(` count in `lib/std/tactic` falls by most of `mono`'s share.

## What it assumes from elsewhere

- **[[sequencing-surface-design]]** owns the spelling and the protocol.
- **[[higher-kinded-classes]]** (R2a) provides classes over a type constructor.
