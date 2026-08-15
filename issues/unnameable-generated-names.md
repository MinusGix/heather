---
title: Generated names are not ordinary identifiers: the # hygiene boundary
status: open
labels: [frontend,elaboration,design,ergonomics]
created: 2026-08-14
updated: 2026-08-14
---

Filed from the datarepr design review (2026-08-14, user live commentary on
docs/datarepr-design.md sec. 1.4): generated artifacts (typeclass instance
records like Repr_ListTok, monomorph names, derived Impls) should NOT be
ordinary user-spellable identifiers. Lean is the counterexample: generated
instance names are referenceable as normal identifiers, which makes them
easy to reach but hard to trust — user code silently depends on a name the
elaborator invented and may respell. Wanted instead: generated names are
unnameable-by-default at the surface (sketch spelling: a # sigil, e.g.
#Repr_ListTok — lower layers treat it as any identifier), reached through
deliberate syntax or indirection (e.g. Repr<List<Tok>>::record_ty). This is
an overarching design boundary touching multiple features (datarepr,
Compile instances, certgen emissions, derived tables), not a datarepr
blocker — the datarepr landing round should merely avoid committing to
surface-spellable generated names. Related: [[datarepr-separation]],
[[compile-typeclass-design]].

2026-08-15, datarepr v1 landing: the round DID land nameable names
(`Repr_N`, `N_spec_rec`, `Repr_N::⟨clause⟩` — docs/datarepr-design.md §1.4
as-landed note 1), and the constraint is structural, not an oversight: the
artifacts are emitted as surface source and re-parsed (the certgen move,
for the same dependent-record reason), and `#` never *begins* a surface
identifier, so an unnameable name cannot be written in the text that
declares it. Whatever design lands here must either give the generated-
source path a way to declare-and-reference sigiled names (parser accepts
`#` in generated-source mode only), or move generation off surface text.
The datarepr names are the first standing customers to migrate.

2026-08-15, user verdicts on the above: `#` is WITHDRAWN as the sigil —
use a reserved Unicode character the way Lean marks inaccessible names
(its `✝` style). And the bar is softened: generated names need to be
*mostly* inaccessible — a clear visual "you should avoid depending on
this" marker plus convention — not 100% unwritable; harder inaccessibility
is a nicety. Sharpened same day: the marker should NOT be literally
typeable in ordinary source — "mostly inaccessible" means reaching such a
name takes deliberate code-kludging (programmatic identifier construction,
metaprogramming), not just typing the character. So the lexer rejects the
marker in user-written files while the generated-source path may produce
it — a mode split at the *lexer* for one character class, far smaller than
the parser-mode split feared above. Not immediate; implement when a round
wants it.
