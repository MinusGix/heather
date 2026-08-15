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
